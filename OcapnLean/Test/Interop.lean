import OcapnLean.Syrup

/-!
# Cross-implementation interop fixtures

This module verifies, at compile time, that our `OcapnLean.Syrup`
encoder produces byte-identical output to the Python reference
implementation in `projects/syrup-ocapn/impls/python/syrup.py` for
the subset of values our codec supports (booleans, integers, byte
arrays).

The reference encodings below were captured by running
`scripts/regenerate-interop-fixtures.py` against
`impls/python/syrup.py`. Re-run that script if you extend the codec
to additional Syrup types or want to compare against a different
reference implementation.

This is the strongest interop signal currently achievable: the
network-level CapTP interop (test_runner.py against a running OCapN
peer) requires our `Captp.Impl` to grow `IO`-based netlayer code,
which is queued for a follow-up commit. See `scripts/run-interop.sh`
for the CapTP-level harness skeleton.
-/

namespace OcapnLean.Test.Interop

open OcapnLean.Syrup OcapnLean.Syrup.Encode

-- Each row: (Lean Value, expected reference encoding).
-- The reference column is the byte sequence produced by
-- syrup.syrup_encode(...) in the upstream python impl, transcribed
-- verbatim. UTF-8 makes the bytes printable in many cases.

example : encode (.bool true)  = [0x74] := by native_decide                 -- "t"
example : encode (.bool false) = [0x66] := by native_decide                 -- "f"
example : encode (.int 0)      = [0x30, 0x2b] := by native_decide           -- "0+"
example : encode (.int 1)      = [0x31, 0x2b] := by native_decide           -- "1+"
example : encode (.int 42)     = [0x34, 0x32, 0x2b] := by native_decide     -- "42+"
example : encode (.int (-7))   = [0x37, 0x2d] := by native_decide           -- "7-"
example : encode (.int 100)    = [0x31, 0x30, 0x30, 0x2b] := by native_decide -- "100+"
example : encode (.bytes [])   = [0x30, 0x3a] := by native_decide           -- "0:"
example : encode (.bytes [0x63, 0x61, 0x74])
        = [0x33, 0x3a, 0x63, 0x61, 0x74] := by native_decide                -- "3:cat"

end OcapnLean.Test.Interop
