import OcapnLean.Model

/-!
# CapTP message and descriptor types

Mirrors `projects/ocapn-spec/draft-specifications/CapTP Specification.md`.

Descriptors describe *references* on the wire; operations are the verbs of
the protocol. The two are intentionally separate inductive types — a
descriptor is a passable value, while an operation is only ever a top-level
frame on the wire.
-/

namespace OcapnLean.Captp

/-- An export / import / answer position. Positive integer in the spec; we
use `Nat` here because position `0` is reserved for the bootstrap object,
which we treat uniformly. -/
abbrev Pos := Nat

/-- EdDSA public key value. Concrete representation is gcrypt-style
s-expression; we only need its identity here. -/
structure PublicKey where
  bytes : ByteArray

/-- EdDSA signature value. -/
structure Signature where
  r : ByteArray
  s : ByteArray

/-- A 32-byte Public Identifier: `SHA256(SHA256(serialise(pubkey)))`. -/
abbrev PublicId := ByteArray

/-- A 32-byte Session ID derived from the two peers' Public Identifiers. -/
abbrev SessionId := ByteArray

/-- A 32-byte gift id used in three-party handoffs. -/
abbrev GiftId := ByteArray

/-- An OCapN locator (transport + designator + hints). We keep the
representation abstract here — see `OcapnLean.Locators` for the codec. -/
structure Locator where
  transport  : String       -- e.g. "onion", "tcp-tls"
  designator : String       -- self-authenticating identifier (often a pubkey)
  hints      : List (String × String) := []
deriving Repr

mutual
  /-- Descriptors describe a reference on the wire. They are *values* that
  can appear inside `op:deliver`'s `args`, etc. -/
  inductive Desc
    | importObject  (position : Pos)
    | importPromise (position : Pos)
    | export        (position : Pos)
    | answer        (answerPos : Pos)
    | sigEnvelope   (signed : Wire) (signature : Signature)
    | handoffGive
        (receiverKey      : PublicKey)
        (exporterLocation : Locator)
        (session          : SessionId)
        (gifterSide       : PublicId)
        (giftId           : GiftId)
    | handoffReceive
        (receivingSession : SessionId)
        (receivingSide    : PublicId)
        (handoffCount     : Nat)
        (signedGive       : Desc)

  /-- A passable wire value (Atom, Container, or Descriptor). This is the
  in-message value algebra. -/
  inductive Wire
    | atom   (a : Atom)
    | list   (xs : List Wire)
    | struct (fields : List (String × Wire))
    | tagged (tag : String) (v : Wire)
    | desc   (d : Desc)
end

/-- CapTP top-level operations. -/
inductive Op
  | startSession
      (captpVersion           : String)        -- MUST be "1.0"
      (sessionPubkey          : PublicKey)
      (acceptableLocation     : Locator)
      (acceptableLocationSig  : Signature)
  | deliver
      (toDesc        : Desc)
      (args          : List Wire)
      (answerPos     : Option Pos)             -- none ↔ no result expected
      (resolveMeDesc : Option Desc)            -- some ↔ async-resolver
  | listen
      (toDesc     : Desc)
      (listenDesc : Desc)
  | abort
      (reason : String)
  | get
      (receiverDesc : Desc)
      (fieldName    : String)
      (newAnswerPos : Pos)
  | index
      (receiverDesc : Desc)
      (idx          : Int)
      (newAnswerPos : Pos)
  | untag
      (receiverDesc : Desc)
      (tag          : String)
      (newAnswerPos : Pos)
  | gcExports
      (exportPosList : List Pos)
      (wireDeltaList : List Nat)
  | gcAnswers
      (answerPosList : List Pos)

end OcapnLean.Captp
