import OcapnLean.Captp.Client
import OcapnLean.Locators
import OcapnLean.Netlayer.Tcp

/-!
# Sturdyref `fetch` semantics layer (M9)

The plumbing between `OcapnLean.Locators.SturdyRef` and
`OcapnLean.Captp.Client`. Given a sturdyref the caller obtained
out-of-band (e.g. by parsing a URI, by reading from disk), this module
opens a CapTP session against the named peer, runs the handshake,
sends `<op:deliver <desc:export 0> [fetch swiss] False
<desc:import-object N>>`, awaits the fulfill, and returns the
imported object's position alongside the live session — ready for
further `op:deliver`s.

Three orthogonal per-peer quirks (framing, captp-version, empty-hints
shape) are bundled into a `TransportProfile`. The defaults match the
de-facto Python-ref / Endo / Goblins / ocapn-lean convention; a
`TransportProfile.ridley` preset captures the Ridley dobjects
deviations documented in `docs/INTEROP.md` Disagreements 3 & 4.
-/

namespace OcapnLean.Captp.SturdyRefClient

open OcapnLean OcapnLean.Captp OcapnLean.Captp.Client OcapnLean.Locators
     OcapnLean.Netlayer OcapnLean.Syrup
open Std.Net

/-! ## Per-transport profile -/

/-- The three settings a `fetch` needs to pick on a per-peer basis.
Default values match the de-facto OCapN convention. -/
structure TransportProfile where
  /-- Wire framing. `.raw` for the de-facto convention; `.netstring`
  for Ridley dobjects on `tcp-testing-only`. -/
  framing            : Netlayer.Tcp.Framing
  /-- CapTP version string we advertise in `op:start-session`. -/
  captpVersion       : String
  /-- If `true`, emit empty hints as `.bool false` instead of `.dict []`.
  Needed for Ridley because `PeerLocator.toRecord` re-encodes empty
  hints as `false`, which breaks signature verification of an
  empty-dict payload. See `docs/INTEROP.md` Disagreement 3. -/
  emptyHintsAsFalse  : Bool
deriving Repr

namespace TransportProfile

/-- Default profile: spec/de-facto convention shared by Python ref,
@endo/ocapn, Goblins ≥ v0.16.1, and ocapn-lean self. -/
def default : TransportProfile :=
  { framing := .raw, captpVersion := "1.0", emptyHintsAsFalse := false }

/-- Ridley dobjects on `tcp-testing-only`: netstring framing, captp
version `0.1`, hints emitted as `false`. -/
def ridley : TransportProfile :=
  { framing := .netstring, captpVersion := "0.1", emptyHintsAsFalse := true }

end TransportProfile

/-! ## Hint + address helpers -/

/-- Look up a hint by key. -/
def lookupHint (key : List UInt8) :
    Option (List (List UInt8 × List UInt8)) → Option (List UInt8)
  | none      => none
  | some kvs  => kvs.find? (fun (k, _) => k = key) |>.map (·.2)

/-- ASCII byte list → `String`. The hints we consume here (`host`,
`port`) are URI-derived and always ASCII; if a future caller passes
non-UTF-8 we'd surface a parse error one level up. -/
private def bytesToString (bs : List UInt8) : String :=
  String.fromUTF8! ⟨bs.toArray⟩

/-- Resolve `host=…&port=…` hints to a Std.Net `SocketAddress`.
IPv4-only (matches `OcapnLean.Netlayer.Tcp.connect`). Throws on
missing or malformed hints. -/
def addressFromPeer (peer : PeerLocator) : IO SocketAddress := do
  let hostBytes ←
    match lookupHint "host".toUTF8.toList peer.hints with
    | some b => pure b
    | none   => throw (IO.userError "[sturdyref] peer hints missing 'host'")
  let portBytes ←
    match lookupHint "port".toUTF8.toList peer.hints with
    | some b => pure b
    | none   => throw (IO.userError "[sturdyref] peer hints missing 'port'")
  let hostStr := bytesToString hostBytes
  let addr ←
    match IPv4Addr.ofString hostStr with
    | some a => pure a
    | none   => throw (IO.userError s!"[sturdyref] cannot parse IPv4 host \"{hostStr}\"")
  let portStr := bytesToString portBytes
  let port ←
    match portStr.toNat? with
    | some n => pure n.toUInt16
    | none   => throw (IO.userError s!"[sturdyref] cannot parse port \"{portStr}\"")
  pure (Tcp.v4 addr port)

/-- Build the `<ocapn-peer …>` value-ext we'll advertise as **our**
location. Reuses the peer's transport so the wire `transport`
field matches, picks an empty hints shape per the profile, and
takes an explicit `designator` so callers can give each session a
distinct id. -/
def ourLocationFor (peer : PeerLocator) (profile : TransportProfile)
    (designator : List UInt8) : ValueExt :=
  let hintsVal : ValueExt :=
    if profile.emptyHintsAsFalse then .bool false else .dict []
  .record (.sym "ocapn-peer".toUTF8.toList)
    [ .sym peer.transport
    , .str designator
    , hintsVal
    ]

/-! ## Connect + fetch -/

/-- A safe default `designator` for clients that don't supply one.
32 ASCII characters matching the test-suite's swissnum-byte width. -/
def defaultClientDesignator : List UInt8 :=
  "ocapnleansturdyclientbeefdeadbeef".toUTF8.toList

/-- Connect to a sturdyref's peer and complete the handshake. The
caller is responsible for closing the returned session (on both
success and failure paths). -/
def connectAndHandshake (s : SturdyRef)
    (profile : TransportProfile := .default)
    (ourDesignator : List UInt8 := defaultClientDesignator) :
    IO Client.Session := do
  let addr ← addressFromPeer s.peer
  let ourLoc := ourLocationFor s.peer profile ourDesignator
  let sess ← Client.Session.connect addr ourLoc
              (captpVersion := profile.captpVersion)
              (framing       := profile.framing)
  Client.handshake sess
  pure sess

/-- Full sturdyref `fetch`: connect, handshake, send `[fetch swiss]`,
await the fulfill, extract the resolved `<desc:import-object N>` and
return `(sess, N)`. Closes the session and rethrows on any failure
after the handshake. -/
def fetch (s : SturdyRef)
    (profile : TransportProfile := .default)
    (ourDesignator : List UInt8 := defaultClientDesignator)
    (budgetMs : Nat := 10000) :
    IO (Client.Session × Nat) := do
  let sess ← connectAndHandshake s profile ourDesignator
  try
    let rmd ← Client.fetch sess s.swiss
    let resolved ← Client.expectFulfill sess rmd budgetMs
    match Captp.Session.extractImportObjPos resolved with
    | some pos => pure (sess, pos)
    | none =>
      throw (IO.userError
        "[sturdyref] fetch fulfill did not resolve to a <desc:import-object N>")
  catch e =>
    sess.close
    throw e

end OcapnLean.Captp.SturdyRefClient
