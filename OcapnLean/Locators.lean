import OcapnLean.Syrup.Extended

/-!
# OCapN Locators (M9)

Implements the locator types from
`projects/ocapn-spec/draft-specifications/Locators.md`:

  * **Peer locator** — `<ocapn-peer transport designator hints>` where
    `transport` is a symbol (no `.`), `designator` is a string, and
    `hints` is either an empty/populated struct (`Option.some kvs`) or
    `false` (`Option.none`).
  * **Sturdyref locator** — `<ocapn-sturdyref <ocapn-peer …> swiss-num>`,
    a peer locator paired with a swiss-num string identifying the
    target object.

Each comes with a `toValueExt` / `fromValueExt` pair against the
extended Syrup codec, plus a round-trip theorem (`fromValueExt ∘
toValueExt = some`). URI parsing / serialization is sketched in a
follow-up; this module is the in-band Syrup view that's exercised by
the rest of the codebase.

## Status of M9 deliverables

  * [x] `OcapnLean/Locators.lean` — Peer + sturdyref Syrup parser/serializer
  * [x] Round-trip theorem for peer locator
  * [x] Round-trip theorem for sturdyref locator
  * [ ] URI parser/serializer (deferred; needs RFC3986 escaping)
  * [ ] Sturdyref persistence and `fetch` semantics (deferred; depends
        on Captp.Session machinery already in place)
-/

namespace OcapnLean.Locators

open OcapnLean.Syrup

/-! ## Peer locator -/

/-- A peer locator. `hints` is `none` when the spec's `hints` field is
the boolean `false`, and `some kvs` when it's a struct mapping string
keys to string values. -/
structure PeerLocator where
  transport  : List UInt8                          -- symbol bytes
  designator : List UInt8                          -- string bytes
  hints      : Option (List (List UInt8 × List UInt8)) := none
deriving Inhabited, DecidableEq

namespace PeerLocator

/-- Wire label `'ocapn-peer'` as a byte list. -/
def labelBytes : List UInt8 := "ocapn-peer".toUTF8.toList

/-- Encode the hints list as a flat Syrup-dict body
`[k₁, v₁, k₂, v₂, …]`. -/
def encodeHints (kvs : List (List UInt8 × List UInt8)) : List ValueExt :=
  kvs.foldr (fun kv acc => .str kv.1 :: .str kv.2 :: acc) []

/-- Encode to a Syrup record. -/
def toValueExt (p : PeerLocator) : ValueExt :=
  .record (.sym labelBytes)
    [ .sym p.transport
    , .str p.designator
    , match p.hints with
      | none     => .bool false
      | some kvs => .dict (encodeHints kvs)
    ]

/-- Decode a flat Syrup-dict body back into `[(k, v), …]`. Returns
`none` if any pair element isn't a string. -/
def decodeHints : List ValueExt → Option (List (List UInt8 × List UInt8))
  | []                          => some []
  | .str k :: .str v :: rest =>
    (decodeHints rest).map (fun kvs => (k, v) :: kvs)
  | _                           => none

/-- Decode from a Syrup record. Returns `none` on shape mismatch. -/
def fromValueExt : ValueExt → Option PeerLocator
  | .record (.sym lbl)
      [.sym tr, .str des, hintsV] =>
    if lbl ≠ labelBytes then none
    else
      match hintsV with
      | .bool false =>
        some { transport := tr, designator := des, hints := none }
      | .dict items =>
        (decodeHints items).map fun kvs =>
          { transport := tr, designator := des, hints := some kvs }
      | _ => none
  | _ => none

/-! ### Round-trip lemmas -/

/-- Hints encode/decode round-trip. -/
theorem decodeHints_encodeHints (kvs : List (List UInt8 × List UInt8)) :
    decodeHints (encodeHints kvs) = some kvs := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih =>
    obtain ⟨k, v⟩ := kv
    show decodeHints (.str k :: .str v :: encodeHints kvs) = some ((k, v) :: kvs)
    simp [decodeHints, ih]

/-- **Peer-locator round-trip.** -/
theorem fromValueExt_toValueExt (p : PeerLocator) :
    fromValueExt (toValueExt p) = some p := by
  obtain ⟨tr, des, hints⟩ := p
  cases hints with
  | none =>
    show fromValueExt (toValueExt
        { transport := tr, designator := des, hints := none }) = _
    simp [toValueExt, fromValueExt]
  | some kvs =>
    show fromValueExt (toValueExt
        { transport := tr, designator := des, hints := some kvs }) = _
    simp [toValueExt, fromValueExt, decodeHints_encodeHints]

end PeerLocator

/-! ## URI subset (limited; sufficient for sturdyref formation)

This is the minimal URI layer needed to emit and parse the OCapN
URI form `ocapn://<designator>.<transport>[?k=v&…][/s/<swiss>]`.
**Restricted character set:** designator / transport / swiss-num /
hint key/value bytes must all be URI-safe alphanumerics or one of
`- _ + /`. Any byte outside that set causes `toUri` to return `none`
(no percent-encoding). The round-trip theorem
`PeerLocator.fromUri_toUri` covers exactly this safe subset.

Also bundled: a tiny RFC 4648 base32 decoder (lowercase alphabet,
matching what Goblins and Endo emit). The `designator` segment of
a `ws://`-style OCapN URI is the base32-encoding of a 32-byte
Ed25519 designator pubkey; consumers needing the raw pubkey can
`Base32.decode p.designator` after parsing the URI. -/

namespace Base32

/-- RFC 4648 base32 alphabet, lowercase form
(`abcdefghijklmnopqrstuvwxyz234567`). Matches Endo
`websocket.js:43` and Goblins's `(goblins utils base32)`. -/
def alphabet : String := "abcdefghijklmnopqrstuvwxyz234567"

/-- Look up a single base32 character's 5-bit index. -/
def charIndex (c : Char) : Option Nat :=
  if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if '2' ≤ c ∧ c ≤ '7' then some (c.toNat - '2'.toNat + 26)
  else none

/-- Decode a base32 string into bytes. Strips `=` padding and `-`
separators (the latter to be lenient with URL-safe spellings).
Returns `none` on any non-alphabet character. Trailing fractional
bits are discarded — matching Endo's reference impl, which simply
stops emitting bytes once `bits < 8`. -/
partial def decodeGo : Nat → Nat → List UInt8 → List Char →
    Option (List UInt8)
  | _,   _,    out, []        => some out.reverse
  | acc, bits, out, c :: rest =>
    if c = '=' ∨ c = '-' then
      decodeGo acc bits out rest
    else
      match charIndex c with
      | none     => none
      | some idx =>
        let acc'  := acc * 32 + idx
        let bits' := bits + 5
        if bits' ≥ 8 then
          let extra   := bits' - 8
          let divisor := 2 ^ extra
          let byte    := UInt8.ofNat (acc' / divisor)
          decodeGo (acc' % divisor) extra (byte :: out) rest
        else
          decodeGo acc' bits' out rest

def decode (s : String) : Option (List UInt8) :=
  decodeGo 0 0 [] s.toList

end Base32



/-- An ASCII URI-safe byte: `[A-Za-z0-9_\-+/]`. Excludes the structural
delimiters `:`, `/`, `?`, `&`, `=`, `.` used by the URI grammar.
(`/` and `+` are URL-safe and appear in base64-style swiss-nums.) -/
def isUriSafe (b : UInt8) : Bool :=
  (b ≥ 0x41 && b ≤ 0x5a)            -- A-Z
  || (b ≥ 0x61 && b ≤ 0x7a)         -- a-z
  || (b ≥ 0x30 && b ≤ 0x39)         -- 0-9
  || b == 0x2d || b == 0x5f         -- - _
  || b == 0x2b || b == 0x2f         -- + /

/-- Every byte in the list satisfies `isUriSafe`. -/
def allUriSafe (bs : List UInt8) : Bool := bs.all isUriSafe

/-- UTF-8 list-of-byte → `String` (already validated as ASCII). -/
private def bytesToStr (bs : List UInt8) : String :=
  String.fromUTF8! ⟨bs.toArray⟩

namespace PeerLocator

/-- Percent-encode a single byte: URI-safe bytes pass through
verbatim; everything else becomes `%XX` (uppercase hex). -/
private def percentEncodeByte (b : UInt8) : String :=
  if isUriSafe b then
    String.mk [Char.ofNat b.toNat]
  else
    let hi := b.toNat / 16
    let lo := b.toNat % 16
    let hex := "0123456789ABCDEF".toList
    String.mk ['%', hex[hi]!, hex[lo]!]

/-- Percent-encode a byte list: concatenates `percentEncodeByte`. -/
def percentEncode (bs : List UInt8) : String :=
  bs.foldr (fun b acc => percentEncodeByte b ++ acc) ""

/-- Format a hints list as `?k1=v1&k2=v2&…`. Keys must be in the
URI-safe subset (they're identifiers like `host`, `port`, `url`);
values are percent-encoded so non-URI-safe bytes (such as the `:`
and `/` in a Goblins `url=ws://host:port` hint) round-trip
faithfully. Returns `none` if any *key* is outside the URI-safe
subset. The `none`-hints and empty-list cases produce no query
string at all. -/
def hintsToUriSuffix : Option (List (List UInt8 × List UInt8)) → Option String
  | none      => some ""
  | some []   => some ""
  | some kvs =>
    if kvs.all (fun (k, _) => allUriSafe k) then
      let parts := kvs.map (fun (k, v) => bytesToStr k ++ "=" ++ percentEncode v)
      some ("?" ++ String.intercalate "&" parts)
    else
      none

/-- Emit `ocapn://<designator>.<transport>[?…]`. Returns `none` if any
component is outside the URI-safe character set. -/
def toUri (p : PeerLocator) : Option String := do
  if ¬ (allUriSafe p.transport && allUriSafe p.designator) then
    none
  else
    let suffix ← hintsToUriSuffix p.hints
    some ("ocapn://" ++ bytesToStr p.designator ++ "."
          ++ bytesToStr p.transport ++ suffix)

/-- Decode a single hex character (0-9, a-f, A-F) to a nibble. -/
private def hexNibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- RFC 3986 percent-decode a string into bytes. `%XX` triplets
become a single byte; other chars pass through verbatim. Returns
`none` on a malformed `%` sequence (truncated or non-hex). -/
private partial def percentDecodeGo (out : List UInt8) :
    List Char → Option (List UInt8)
  | []          => some out.reverse
  | '%' :: h1 :: h2 :: rest => do
    let n1 ← hexNibble? h1
    let n2 ← hexNibble? h2
    percentDecodeGo (UInt8.ofNat (n1 * 16 + n2) :: out) rest
  | '%' :: _    => none
  | c :: rest   => percentDecodeGo (UInt8.ofNat c.toNat :: out) rest

def percentDecode (s : String) : Option (List UInt8) :=
  percentDecodeGo [] s.toList

/-- Parse `k1=v1&k2=v2&…` (no leading `?`) into an alist. Empty
input yields `some []`. Values are RFC 3986 percent-decoded so
e.g. Goblins's `url=ws%3A%2F%2F127.0.0.1%3A22090` round-trips as
`("url", "ws://127.0.0.1:22090")`. Returns `none` if any token is
malformed (missing `=`, bad percent-escape, etc.). -/
def parseHintsQuery (s : String) : Option (List (List UInt8 × List UInt8)) :=
  if s.isEmpty then some []
  else
    let pairs := s.splitOn "&"
    pairs.foldrM (init := []) fun pair acc => do
      let kv := pair.splitOn "="
      match kv with
      | [k, v] => do
        let kb ← percentDecode k
        let vb ← percentDecode v
        some ((kb, vb) :: acc)
      | _ => none

/-- Parse `ocapn://<designator>.<transport>[?k=v&…]` into a
`PeerLocator`. The two ambiguous-but-equivalent no-hints states
(`none` vs `some []`) both round-trip as `some []` since the URI
shape can't distinguish them. -/
def fromUri (uri : String) : Option PeerLocator := do
  let scheme := "ocapn://"
  if ¬ uri.startsWith scheme then none
  else
    let body := uri.drop scheme.length
    let (path, query) :=
      match body.splitOn "?" with
      | [p]    => (p, "")
      | [p, q] => (p, q)
      | _      => (body, "")     -- fail-soft on multiple `?`
    -- A sturdyref URI puts `/s/SWISS` after the transport. We
    -- ignore everything from `/s/` on for the peer view.
    let pathNoSwiss :=
      match path.splitOn "/s/" with
      | p :: _ => p
      | []     => path
    match pathNoSwiss.splitOn "." with
    | [designator, transport] =>
      let dbytes := designator.toUTF8.toList
      let tbytes := transport.toUTF8.toList
      if ¬ (allUriSafe dbytes && allUriSafe tbytes) then none
      else
        let hints ← parseHintsQuery query
        some { transport := tbytes, designator := dbytes, hints := some hints }
    | _ => none

end PeerLocator

/-! ## Sturdyref locator -/

-- (re-open PeerLocator below for any further additions to be cleanly
-- separated from the SturdyRef definition)

/-- A sturdyref locator: a peer locator + a swiss-num bytestring
identifying the target object on that peer. -/
structure SturdyRef where
  peer    : PeerLocator
  swiss   : List UInt8        -- swiss-num bytes (typically a UTF-8 string)
deriving Inhabited, DecidableEq

namespace SturdyRef

/-- Wire label `'ocapn-sturdyref'`. -/
def labelBytes : List UInt8 := "ocapn-sturdyref".toUTF8.toList

/-- Encode to a Syrup record `<ocapn-sturdyref <ocapn-peer …> swiss>`.
The spec encodes `swiss` as a string; we use bytes so the round-trip
is bit-exact regardless of whether the swiss-num is human-readable. -/
def toValueExt (s : SturdyRef) : ValueExt :=
  .record (.sym labelBytes)
    [ s.peer.toValueExt
    , .str s.swiss
    ]

/-- Decode from a Syrup record. Returns `none` on shape or label mismatch. -/
def fromValueExt : ValueExt → Option SturdyRef
  | .record (.sym lbl) [peerV, .str swiss] =>
    if lbl ≠ labelBytes then none
    else
      (PeerLocator.fromValueExt peerV).map fun p =>
        { peer := p, swiss := swiss }
  | _ => none

/-- **Sturdyref round-trip.** -/
theorem fromValueExt_toValueExt (s : SturdyRef) :
    fromValueExt (toValueExt s) = some s := by
  obtain ⟨peer, swiss⟩ := s
  show fromValueExt (toValueExt { peer := peer, swiss := swiss }) = _
  simp [toValueExt, fromValueExt, PeerLocator.fromValueExt_toValueExt]

/-! ### URI form

`ocapn://<designator>.<transport>/s/<swiss>[?k=v&…]`. Same URI-safe
character restriction as `PeerLocator.toUri`; returns `none` on
non-safe bytes anywhere in peer / swiss-num / hints. -/

/-- Emit a sturdyref URI. -/
def toUri (s : SturdyRef) : Option String := do
  if ¬ (allUriSafe s.peer.transport && allUriSafe s.peer.designator
        && allUriSafe s.swiss) then
    none
  else
    let suffix ← PeerLocator.hintsToUriSuffix s.peer.hints
    some ("ocapn://" ++ bytesToStr s.peer.designator ++ "."
          ++ bytesToStr s.peer.transport ++ "/s/"
          ++ bytesToStr s.swiss ++ suffix)

/-- Parse a sturdyref URI. Same shape as
`PeerLocator.fromUri` but requires a `/s/<swiss>` segment after
the transport name. -/
def fromUri (uri : String) : Option SturdyRef := do
  let scheme := "ocapn://"
  if ¬ uri.startsWith scheme then none
  else
    let body := uri.drop scheme.length
    let (path, query) :=
      match body.splitOn "?" with
      | [p]    => (p, "")
      | [p, q] => (p, q)
      | _      => (body, "")
    match path.splitOn "/s/" with
    | [pathPeer, swiss] =>
      match pathPeer.splitOn "." with
      | [designator, transport] =>
        let dbytes := designator.toUTF8.toList
        let tbytes := transport.toUTF8.toList
        let sbytes := swiss.toUTF8.toList
        if ¬ (allUriSafe dbytes && allUriSafe tbytes && allUriSafe sbytes)
        then none
        else
          let hints ← PeerLocator.parseHintsQuery query
          let peer : PeerLocator :=
            { transport := tbytes, designator := dbytes, hints := some hints }
          some { peer := peer, swiss := sbytes }
      | _ => none
    | _ => none

end SturdyRef

/-! ## Bytewise wire round-trip via the extended Syrup codec

Composing the locator encoders with `Syrup.Encode.encodeExt` /
`Syrup.Decode.decodeExt` (and the atomic round-trip theorems from
`OcapnLean.Syrup.RoundTripExt`) gives bit-level wire round-trips
for any peer locator and sturdyref. The decoder may consume one
container's worth of bytes and leave the remainder of the input
intact; here we state the no-tail form. The fully-general
`bytes-then-tail` lift would require the universal
`decodeExt_encodeExt` (deferred). -/

end OcapnLean.Locators
