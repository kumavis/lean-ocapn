#!/usr/bin/env python3
"""Standalone interop tests for the handshake error paths.

Equivalent to:
  - tests.op_start_session.test_start_session_with_invalid_version
  - tests.op_start_session.test_start_session_with_invalid_signature  (TODO)

The full upstream test_runner discovers tests alphabetically and gets
stuck on `test_crossed_hellos_mitigation_*` because we don't yet
implement the sturdyref-enlivener bootstrap object. This script runs
the simpler error-path tests directly.

Usage:
  # Terminal 1
  lake exe ocapn-server -- --port 22082
  # Terminal 2
  python3 scripts/interop-invalid-handshake.py
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
PORT = int(os.environ.get("OCAPN_PORT", "22082"))


def send_recv(payload: bytes, expect_prefix: bytes, label: str) -> bool:
    """Connect, send `payload`, read response, check it starts with
    `expect_prefix`. Returns True on success."""
    print(f"\n=== {label} ===")
    try:
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
                    if expect_prefix and buf.startswith(expect_prefix):
                        break
            except socket.timeout:
                pass
    except Exception as e:
        print(f"  FAIL: connection error: {e}")
        return False

    print(f"  recv {len(buf)} bytes")
    print(f"  starts with: {buf[:40]!r}")
    if buf.startswith(expect_prefix):
        print(f"  OK: matched expected prefix {expect_prefix!r}")
        return True
    else:
        print(f"  FAIL: expected prefix {expect_prefix!r}")
        return False


def main() -> int:
    pubkey = b"\x00" * 32
    location = Record(Symbol("my-location"),
                      [Record(Symbol("ocapn-peer"),
                              [Symbol("tcp-testing-only"),
                               "client",
                               []])])
    sig = b"\x00" * 64

    # --- test 1: valid version, expect op:start-session reply ---
    good = Record(Symbol("op:start-session"),
                  ["1.0", pubkey, location, sig])
    ok1 = send_recv(syrup.syrup_encode(good),
                    b"<16'op:start-session3\"1.0",
                    "test_captp_remote_version (valid 1.0)")

    # --- test 2: invalid version → op:abort ---
    bad_ver = Record(Symbol("op:start-session"),
                     ["wrong-version", pubkey, location, sig])
    ok2 = send_recv(syrup.syrup_encode(bad_ver),
                    b"<8'op:abort",
                    "test_start_session_with_invalid_version")

    # --- test 3: non-handshake first frame → op:abort ---
    not_handshake = Record(Symbol("op:deliver"),
                           [Record(Symbol("desc:export"), [0]),
                            [], 0, False])
    ok3 = send_recv(syrup.syrup_encode(not_handshake),
                    b"<8'op:abort",
                    "first frame is not op:start-session")

    print()
    print(f"Results: {sum([ok1, ok2, ok3])}/3 passed")
    return 0 if (ok1 and ok2 and ok3) else 1


if __name__ == "__main__":
    raise SystemExit(main())
