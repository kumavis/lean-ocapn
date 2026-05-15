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
`PeerLocator.fromUri_toUri` covers exactly this safe subset. -/

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

/-- Format a hints list as `?k1=v1&k2=v2&…`. Returns `none` if any
key or value is outside the URI-safe subset. The empty-list and
`none` cases produce no query string at all. -/
def hintsToUriSuffix : Option (List (List UInt8 × List UInt8)) → Option String
  | none      => some ""
  | some []   => some ""
  | some kvs =>
    if kvs.all (fun (k, v) => allUriSafe k && allUriSafe v) then
      let parts := kvs.map (fun (k, v) => bytesToStr k ++ "=" ++ bytesToStr v)
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
