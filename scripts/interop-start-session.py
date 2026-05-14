#!/usr/bin/env python3
"""Wire-level interop test for `OcapnLean.Captp.Session.run`.

Stands in for `projects/ocapn-test-suite/tests/op_start_session.py`
without the cryptography dependency — this script crafts a syrup-
encoded `op:start-session` with placeholder bytes for the pubkey and
location-signature, sends it, and asserts the server replies with its
own `op:start-session` carrying the matching `captp-version` "1.0".

Usage from the repo root:

    # 1. Start the ocapn-server in another terminal:
    #      lake exe ocapn-server -- --port 22045
    # 2. Then:
    python3 scripts/interop-start-session.py
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


def main() -> int:
    # Hand-rolled op:start-session with placeholder fields. The
    # OcapnLean server doesn't yet validate signatures, so this passes
    # its handshake check (version "1.0").
    pubkey = b"\x00" * 32
    location = Record(Symbol("my-location"),
                      [Record(Symbol("ocapn-machine"),
                              [f"{HOST}:{PORT}", Symbol("tcp-testing-only"), False])])
    location_sig = b"\x00" * 64
    op_start = Record(Symbol("op:start-session"),
                      ["1.0", pubkey, location, location_sig])

    payload = syrup.syrup_encode(op_start)
    print(f"sending {len(payload)}-byte op:start-session ...")

    with socket.create_connection((HOST, PORT), timeout=5) as s:
        s.sendall(payload)
        # Wait a beat, then read everything available.
        time.sleep(0.1)
        s.settimeout(2.0)
        buf = b""
        try:
            while True:
                chunk = s.recv(4096)
                if not chunk:
                    break
                buf += chunk
                # Stop greedily reading after the first whole frame.
                try:
                    syrup.syrup_decode(buf)
                    break
                except Exception:
                    continue
        except socket.timeout:
            pass

    print(f"received {len(buf)} bytes")
    if not buf:
        print("FAIL: empty response")
        return 1

    # NOTE: We deliberately avoid `syrup.syrup_decode(buf)` here —
    # the upstream Python reference impl has a typo bug at line 166
    # of syrup.py (`bytes_len` instead of `int_or_bytes_len`) that
    # crashes on any bytestring. We instead check the byte pattern
    # directly, which is sufficient to verify that the server
    # produced a record labelled `op:start-session` whose first
    # argument is the string `"1.0"`.

    expected_prefix = b"<16'op:start-session3\"1.0"
    if not buf.startswith(expected_prefix):
        print(f"FAIL: expected prefix {expected_prefix!r}")
        print(f"      got prefix      {buf[:len(expected_prefix)]!r}")
        return 1

    print("OK: server replied with op:start-session + version 1.0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
