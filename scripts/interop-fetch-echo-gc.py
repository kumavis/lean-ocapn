#!/usr/bin/env python3
"""Wire-level interop test for the bootstrap-fetch path.

After op:start-session, sends an op:deliver fetching the Echo-GC
swissnum from the bootstrap object and verifies the server returns a
non-empty Syrup frame (the dispatcher's reply). Uses the upstream
Python `syrup_encode` to produce the wire bytes, demonstrating
encoder interop between Python and Lean.

Usage:

    # Terminal 1
    lake exe ocapn-server -- --port 22045
    # Terminal 2
    python3 scripts/interop-fetch-echo-gc.py
"""
from __future__ import annotations

import os
import socket
import sys
import time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "projects/syrup-ocapn/impls/python"))

import syrup  # noqa: E402
from syrup import Record, Symbol  # noqa: E402

HOST = "127.0.0.1"
PORT = int(os.environ.get("OCAPN_PORT", "22045"))

ECHO_GC_SWISSNUM = b"IO58l1laTyhcrgDKbEzFOO32MDd6zE5w"


def main() -> int:
    op_start = Record(Symbol("op:start-session"),
                      ["1.0", b"\x00" * 32,
                       Record(Symbol("my-location"),
                              [Record(Symbol("ocapn-machine"),
                                      [f"{HOST}:{PORT}",
                                       Symbol("tcp-testing-only"),
                                       False])]),
                       b"\x00" * 64])
    op_fetch = Record(Symbol("op:deliver"),
                      [Record(Symbol("desc:export"), [0]),
                       [Symbol("fetch"), ECHO_GC_SWISSNUM],
                       1, False])

    payload = syrup.syrup_encode(op_start) + syrup.syrup_encode(op_fetch)
    print(f"sending {len(payload)} bytes (start-session + fetch)")

    with socket.create_connection((HOST, PORT), timeout=5) as s:
        s.sendall(payload)
        time.sleep(0.2)
        s.settimeout(2.0)
        buf = b""
        try:
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                buf += chunk
        except socket.timeout:
            pass

    print(f"received {len(buf)} bytes")
    if not buf:
        print("FAIL: empty response")
        return 1

    # The first frame must be the op:start-session reply.
    expected_handshake = b"<16'op:start-session3\"1.0"
    if not buf.startswith(expected_handshake):
        print(f"FAIL: bad handshake reply: {buf[:50]!r}")
        return 1
    print("OK: handshake reply present")

    # The full response must end with the Echo-GC empty-list result `[]`
    # (since we fetched with no args). The dispatcher concatenates the
    # handshake reply and the fetch reply on the wire.
    if not buf.endswith(b"[]"):
        print(f"FAIL: response did not end with []: ...{buf[-20:]!r}")
        return 1
    print("OK: fetch reply is `[]` — Echo-GC returned empty list as expected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
