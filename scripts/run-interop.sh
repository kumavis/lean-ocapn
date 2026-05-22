#!/usr/bin/env bash
# Run the OCapN interop test suite against a running ocapn-lean peer.
#
# This script is the network-level CapTP harness. It depends on
# `OcapnLean.Captp.Impl` growing real IO/netlayer code that listens
# on a TCP port and speaks Syrup-over-TCP per the OCapN spec. Until
# that lands, the script can verify the test-suite invocation
# environment (Python, deps) and serve as documentation.
#
# Usage:
#   scripts/run-interop.sh                # checks env, prints status
#   scripts/run-interop.sh --port 22045   # once impl exists: full run

set -euo pipefail

REPO_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
TEST_SUITE="$REPO_ROOT/projects/ocapn-test-suite"

PORT=22045
while [[ $# -gt 0 ]]; do
  case "$1" in
    --port) PORT="$2"; shift 2;;
    -h|--help)
      sed -n '2,15p' "$0"; exit 0;;
    *) echo "unknown flag: $1" >&2; exit 2;;
  esac
done

echo "--- environment check ---"
command -v python3 >/dev/null || { echo "python3 not on PATH"; exit 1; }
python3 --version

if ! python3 -c "import cryptography" 2>/dev/null; then
  echo "WARN: python-cryptography missing (required by test_runner.py)."
  echo "     pip install cryptography"
fi

if [[ ! -d "$TEST_SUITE" ]]; then
  echo "FAIL: ocapn-test-suite submodule missing at $TEST_SUITE."
  echo "     run: git submodule update --init projects/ocapn-test-suite"
  exit 1
fi

echo "--- impl readiness check ---"
echo "Current OcapnLean.Captp.Impl is a pure-State machine without"
echo "network IO. CapTP-level interop testing requires:"
echo "  1. impl exposes a TCP listener on \$port"
echo "  2. impl performs op:start-session handshake using Syrup"
echo "  3. impl implements the test-suite's required bootstrap objects"
echo "     (Car Factory, etc. — see projects/ocapn-test-suite/README.md)"
echo ""
echo "When those land, this script will run:"
echo "  python3 $TEST_SUITE/test_runner.py \\"
echo "    'ocapn://a2ef69ddd5f84840970612ff660f5058.tcp-testing-only?host=127.0.0.1&port=$PORT'"
echo ""
echo "For now, exiting without running CapTP-level tests."

# Syrup-level interop (codec byte-equivalence with the Python ref) is
# verified at compile time by OcapnLean/Test/Interop.lean and runs via
# `lake build` — no scripting needed.
echo "--- syrup-level interop verified by compile-time fixtures ---"
echo "    OcapnLean/Test/Interop.lean -> 9 native_decide checks"
