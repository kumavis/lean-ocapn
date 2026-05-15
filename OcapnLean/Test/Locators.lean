import OcapnLean.Locators

/-!
# Locator unit tests

Ported from Ridley dobjects's `test/locators/peer_locator_test.dart`
and `test/locators/sturdy_ref_test.dart`. Compile-time
(`native_decide` / `rfl`) assertions over the Syrup-record encoder
and decoder defined in `OcapnLean.Locators`.

These complement the universal round-trip theorems
(`PeerLocator.fromValueExt_toValueExt`, `SturdyRef.fromValueExt_toValueExt`)
with concrete-example checks of:

  * the exact wire shape we emit (`toValueExt` byte structure),
  * rejection paths (`fromValueExt` returns `none` on malformed input),
  * specific-byte equality between encoder output and re-decoder.
-/

namespace OcapnLean.Locators.Test

open OcapnLean.Syrup OcapnLean.Locators

/-! ## Test fixtures (shared with the Ridley tests above) -/

private def testTransport : List UInt8 := "transport".toUTF8.toList
private def testDesignator : List UInt8 := "designator".toUTF8.toList
private def testHints : List (List UInt8 × List UInt8) :=
  [ ("hint1".toUTF8.toList, "value1".toUTF8.toList)
  , ("hint2".toUTF8.toList, "value2".toUTF8.toList)
  , ("hint3".toUTF8.toList, "value3".toUTF8.toList)
  ]

private def peerWithHints : PeerLocator :=
  { transport := testTransport
  , designator := testDesignator
  , hints := some testHints
  }

private def peerNoHints : PeerLocator :=
  { transport := testTransport
  , designator := testDesignator
  , hints := none
  }

private def testSwiss : List UInt8 := "testSwissNum".toUTF8.toList

private def srefWithHints : SturdyRef :=
  { peer := peerWithHints, swiss := testSwiss }

private def srefNoHints : SturdyRef :=
  { peer := peerNoHints, swiss := testSwiss }

/-! ## PeerLocator: record encode/decode

`ValueExt` is a nested inductive (recursing through `List ValueExt`), so
it doesn't have `DecidableEq`. The "exact wire shape" examples below
compare byte-level Syrup encodings instead, which is itself a sharper
specification (it pins down the on-the-wire bytes, not just the
abstract record). -/

/-- The exact Syrup-encoded wire bytes for a peer with hints. -/
example :
    Encode.encodeExt peerWithHints.toValueExt
    = Encode.encodeExt
        (.record (.sym PeerLocator.labelBytes)
          [ .sym testTransport
          , .str testDesignator
          , .dict
              [ .str "hint1".toUTF8.toList, .str "value1".toUTF8.toList
              , .str "hint2".toUTF8.toList, .str "value2".toUTF8.toList
              , .str "hint3".toUTF8.toList, .str "value3".toUTF8.toList
              ]
          ]) := by native_decide

/-- The exact Syrup-encoded wire bytes for a peer with no hints. -/
example :
    Encode.encodeExt peerNoHints.toValueExt
    = Encode.encodeExt
        (.record (.sym PeerLocator.labelBytes)
          [ .sym testTransport
          , .str testDesignator
          , .bool false
          ]) := by native_decide

/-- Concrete round-trip: peer-with-hints reconstructs faithfully. -/
example :
    PeerLocator.fromValueExt peerWithHints.toValueExt = some peerWithHints := by
  native_decide

/-- Concrete round-trip: peer-without-hints reconstructs faithfully. -/
example :
    PeerLocator.fromValueExt peerNoHints.toValueExt = some peerNoHints := by
  native_decide

/-! ## PeerLocator: rejection paths

Ported from `peer_locator_test.dart` `'Incorrect record name'`,
`'Incorrect num args'`, `'Designator must be String'`, etc. We
return `none` on any shape mismatch rather than throwing. -/

/-- Wrong record label is rejected. -/
example :
    PeerLocator.fromValueExt
      (.record (.sym "wrong-name".toUTF8.toList)
        [.sym testTransport, .str testDesignator, .bool false]) = none := by
  native_decide

/-- Too many args is rejected (must be exactly 3). -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [ .sym testTransport, .str testDesignator, .bool false
        , .str "extra".toUTF8.toList ]) = none := by
  native_decide

/-- Too few args is rejected. -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [.sym testTransport, .str testDesignator]) = none := by
  native_decide

/-- Designator must be a string (not an int). -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [.sym testTransport, .int 4, .bool false]) = none := by
  native_decide

/-- Transport must be a symbol (not a string). -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [.str "transport".toUTF8.toList, .str testDesignator, .bool false]) = none := by
  native_decide

/-- Hints must be `false` or a dict; bool `true` is rejected. -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [.sym testTransport, .str testDesignator, .bool true]) = none := by
  native_decide

/-- Hints must be `false` or a dict; an integer is rejected. -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [.sym testTransport, .str testDesignator, .int 42]) = none := by
  native_decide

/-- Hints dict with non-string keys/values is rejected
(`decodeHints` only matches `.str k :: .str v :: rest`). -/
example :
    PeerLocator.fromValueExt
      (.record (.sym PeerLocator.labelBytes)
        [ .sym testTransport, .str testDesignator
        , .dict [.int 1, .int 2] ]) = none := by
  native_decide

/-- Not a record at all is rejected. -/
example : PeerLocator.fromValueExt (.bool false) = none := by native_decide
example : PeerLocator.fromValueExt (.list []) = none := by native_decide
example : PeerLocator.fromValueExt (.int 0) = none := by native_decide

/-! ## SturdyRef: record encode/decode -/

/-- The exact Syrup-encoded wire bytes for a sturdyref with hints. -/
example :
    Encode.encodeExt srefWithHints.toValueExt
    = Encode.encodeExt
        (.record (.sym SturdyRef.labelBytes)
          [ peerWithHints.toValueExt
          , .str testSwiss
          ]) := by native_decide

/-- Concrete round-trip: sturdyref reconstructs faithfully (with hints). -/
example :
    SturdyRef.fromValueExt srefWithHints.toValueExt = some srefWithHints := by
  native_decide

/-- Concrete round-trip: sturdyref reconstructs faithfully (no hints). -/
example :
    SturdyRef.fromValueExt srefNoHints.toValueExt = some srefNoHints := by
  native_decide

/-! ## SturdyRef: rejection paths

Ported from `sturdy_ref_test.dart`. -/

/-- Wrong record label is rejected. -/
example :
    SturdyRef.fromValueExt
      (.record (.sym "bad-record-name".toUTF8.toList)
        [peerWithHints.toValueExt, .str testSwiss]) = none := by
  native_decide

/-- Too many args is rejected. -/
example :
    SturdyRef.fromValueExt
      (.record (.sym SturdyRef.labelBytes)
        [peerWithHints.toValueExt, .str testSwiss
        , .str "extra".toUTF8.toList]) = none := by
  native_decide

/-- Peer field must be a parseable PeerLocator record (not a bare string). -/
example :
    SturdyRef.fromValueExt
      (.record (.sym SturdyRef.labelBytes)
        [.str "not-a-peer".toUTF8.toList, .str testSwiss]) = none := by
  native_decide

/-- Swiss-num must be a string (not an int). Ported from Ridley's
`'Swiss num must be a String'`. -/
example :
    SturdyRef.fromValueExt
      (.record (.sym SturdyRef.labelBytes)
        [peerWithHints.toValueExt, .int 4]) = none := by
  native_decide

/-! ## URI subset

Ported from `peer_locator_test.dart` `'Convert PeerLocator to URI
format'` and `sturdy_ref_test.dart` `'Convert SturdyRef to Uri
format'`. Our URI layer is the limited subset that handles
URL-safe characters without percent-encoding; safe-character
violations return `none`. -/

/-- Peer-with-hints serializes to the spec's URI form. -/
example :
    peerWithHints.toUri
    = some "ocapn://designator.transport?hint1=value1&hint2=value2&hint3=value3" := by
  native_decide

/-- Peer-without-hints serializes without a query string. -/
example :
    peerNoHints.toUri = some "ocapn://designator.transport" := by
  native_decide

/-- Sturdyref-with-hints serializes to the spec's URI form. -/
example :
    srefWithHints.toUri
    = some "ocapn://designator.transport/s/testSwissNum?hint1=value1&hint2=value2&hint3=value3" := by
  native_decide

/-- Sturdyref-without-hints serializes with the `/s/<swiss>` suffix only. -/
example :
    srefNoHints.toUri = some "ocapn://designator.transport/s/testSwissNum" := by
  native_decide

/-- URI-unsafe characters cause `toUri` to bail (no percent-encoding). -/
example :
    ({ transport := "bad.transport".toUTF8.toList
       , designator := testDesignator
       , hints := none } : PeerLocator).toUri = none := by
  native_decide

example :
    ({ transport := testTransport
       , designator := "with space".toUTF8.toList
       , hints := none } : PeerLocator).toUri = none := by
  native_decide

end OcapnLean.Locators.Test
