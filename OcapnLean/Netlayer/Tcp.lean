import Std.Internal.Async.TCP
import OcapnLean.Netlayer
import OcapnLean.Syrup.Extended

/-!
# TCP reference netlayer

Concrete `Netlayer` backed by Lean 4.24's libuv TCP API
(`Std.Internal.IO.Async.TCP.Socket.{Client,Server}`).

A raw TCP byte stream has no inherent message boundaries, so the
transport itself owns the framing choice:

* `Framing.raw` — back-to-back Syrup values. Each `recvMessage?` peels
  one Syrup value off the byte buffer. This is the de-facto
  `tcp-testing-only` convention shared by the Python reference suite,
  `@endo/ocapn`, Goblins, and ocapn-lean self.
* `Framing.netstring` — ASCII-decimal length prefix `<n>:<bytes>`,
  where the body itself must be exactly one Syrup value. Used by
  Ridley dobjects on `tcp-testing-only`; see `docs/INTEROP.md`
  Disagreement 4.

Both modes share the same chunked-read implementation; the only
difference is the per-frame boundary parser.
-/

namespace OcapnLean.Netlayer.Tcp

open Std.Net
open Std.Internal.IO.Async
open OcapnLean.Syrup OcapnLean.Syrup.Decode

/-- The well-known IPv4 loopback address `127.0.0.1`. -/
def loopback : IPv4Addr := { octets := #v[127, 0, 0, 1] }

/-- Build an OCapN-style socket address `addr:port` (IPv4). -/
@[inline] def v4 (addr : IPv4Addr) (port : UInt16) : SocketAddress :=
  .v4 { addr := addr, port := port }

/-- Wire-framing strategy for the byte stream. -/
inductive Framing where
  /-- Concatenated Syrup values; each `recvMessage?` consumes one
  via `Syrup.Decode.decodeExt`. The de-facto convention. -/
  | raw
  /-- `<ascii-decimal-length>:<body>` where `body` is exactly one
  Syrup value. No trailing `,` (this is Ridley's variant, not
  Bernstein netstrings). -/
  | netstring
  deriving DecidableEq, Repr

/-- The chunk size we request from the kernel when refilling the
buffer. 4 KiB strikes a balance: large enough to amortise the recv
syscall, small enough to keep memory bounded for tiny messages. -/
def recvChunkSize : USize := 4096

/-- Outcome of trying to parse a `<digits>:` netstring prefix off the
buffer. -/
inductive NetstringParse where
  | ok (len : Nat) (rest : List UInt8)
  | malformed
  | needMore
  deriving Repr

/-- Parse a Ridley-style length prefix off the head of `buf`. Reuses
the digit helpers from `Syrup.Decode` so digit-reading is identical
to a Syrup `bytes` length. -/
def parseNetstringPrefix (buf : List UInt8) : NetstringParse :=
  let (digits, rest) := takeDigits buf
  match rest with
  | []        => .needMore
  | 0x3a :: r =>
    if digits.isEmpty then .malformed
    else .ok (digitsToNat digits) r
  | _         => .malformed

/-- Pull one complete message off a buffered byte stream. The
`bufRef` accumulates received-but-not-yet-consumed bytes across
calls. Returns `none` on clean EOF (empty buffer + no more bytes
incoming). Shared between the TCP and UDS netlayers, both of which
present a raw byte stream that needs Syrup-shaped framing. -/
partial def readMessage
    (framing : Framing) (recv? : USize → IO (Option ByteArray))
    (bufRef : IO.Ref (List UInt8)) : IO (Option ByteArray) := do
  match framing with
  | .raw       => readRaw
  | .netstring => readNetstring
where
  readRaw : IO (Option ByteArray) := do
    let buf ← bufRef.get
    match decodeExt buf with
    | some (_, rest) =>
      -- The decoder tells us where the frame ends (`rest` = bytes
      -- after the consumed frame). Slice the consumed prefix and
      -- return it as the message bytes; the caller (`FramedConn`)
      -- redecodes once more, accepting a small perf cost for the
      -- cleaner byte-oriented netlayer interface.
      let consumed := buf.length - rest.length
      let body := buf.take consumed
      bufRef.set rest
      return some ⟨body.toArray⟩
    | none =>
      match ← recv? recvChunkSize with
      | none =>
        if buf.isEmpty then return none
        else throw (IO.userError "EOF with partial Syrup frame in buffer")
      | some bs =>
        bufRef.set (buf ++ bs.toList)
        readRaw
  readNetstring : IO (Option ByteArray) := do
    let buf ← bufRef.get
    match parseNetstringPrefix buf with
    | .malformed =>
      throw (IO.userError "malformed netstring length prefix")
    | .needMore =>
      match ← recv? recvChunkSize with
      | none =>
        if buf.isEmpty then return none
        else throw (IO.userError "EOF with partial netstring length prefix")
      | some bs =>
        bufRef.set (buf ++ bs.toList)
        readNetstring
    | .ok len rest =>
      if rest.length ≥ len then
        let body  := rest.take len
        let after := rest.drop len
        bufRef.set after
        return some ⟨body.toArray⟩
      else
        match ← recv? recvChunkSize with
        | none => throw (IO.userError "EOF awaiting netstring body bytes")
        | some bs =>
          bufRef.set (buf ++ bs.toList)
          readNetstring

/-- Encode a complete message for the wire according to `framing`. -/
def encodeForWire (framing : Framing) (body : ByteArray) : ByteArray :=
  match framing with
  | .raw       => body
  | .netstring =>
    let lenPrefix := ((toString body.size).toUTF8.toList ++ [0x3a]).toArray
    ⟨lenPrefix⟩ ++ body

/-- Wrap an established client socket as a `Netlayer`. The `framing`
parameter selects between raw-Syrup back-to-back (default) and
Ridley-style `<n>:<body>` netstring framing. -/
def fromClient (c : TCP.Socket.Client) (framing : Framing := .raw) : IO Netlayer := do
  let bufRef ← IO.mkRef ([] : List UInt8)
  let recv? : USize → IO (Option ByteArray) := fun size => do
    let t ← c.recv? size.toUInt64
    t.block
  pure {
    sendMessage := fun bytes => do
      let framed := encodeForWire framing bytes
      let t ← c.send framed
      t.block
    recvMessage? := readMessage framing recv? bufRef
    close := do
      let t ← c.shutdown
      t.block
  }

/-- Connect to a remote OCapN peer over TCP. -/
def connect (addr : SocketAddress) (framing : Framing := .raw) : IO Netlayer := do
  let c ← TCP.Socket.Client.mk
  let t ← c.connect addr
  t.block
  fromClient c framing

/-- Bind+listen on `addr`. Returns an `acceptOne : IO Netlayer` that
the caller invokes to accept the next connection. The server socket
remains open across accepts until the program exits. -/
def listen (addr : SocketAddress) (backlog : UInt32 := 8)
    (framing : Framing := .raw) : IO (IO Netlayer) := do
  let server ← TCP.Socket.Server.mk
  server.bind addr
  server.listen backlog
  pure do
    let t ← server.accept
    let client ← t.block
    fromClient client framing

end OcapnLean.Netlayer.Tcp
