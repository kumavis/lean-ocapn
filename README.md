# ocapn-lean

A Lean 4 implementation of the [OCapN](https://ocapn.org) (Object Capability
Network) protocol with safety properties of the CapTP layer mechanically
proved using [Veil](https://github.com/verse-lab/veil).

## Status

**Seven of the eight proposed proofs of behavior are mechanically discharged**
(147 SMT theorems passing under Z3/cvc5 via Veil's `#check_invariants`):

| ID | Property | Module |
| --- | --- | --- |
| **P1** | end-to-end reference FIFO (headline) | `OcapnLean/Captp/Twoparty.lean` |
| **P2** | promise resolution monotonicity (×3) | `OcapnLean/Captp/Spec.lean` |
| **P3** | no-forgery (direct-send case) | `OcapnLean/Captp/NoForgery.lean` |
| **P4** | GC soundness (wire-delta refcount) | `OcapnLean/Captp/Gc.lean` |
| **P5** | crossed-hellos determinism | `OcapnLean/Captp/CrossedHellos.lean` |
| **P6** | three-party handoff non-replay | `OcapnLean/Captp/Threeparty.lean` |
| **P8** | bootstrap-at-zero | `OcapnLean/Captp/Spec.lean` |

Remaining: **P7** abort terminal (deferred — needs temporal/history
tracking, not a clean inductive state invariant in Veil v1).

See [`docs/PLAN.md`](docs/PLAN.md) for the proof plan and
[`docs/ROADMAP.md`](docs/ROADMAP.md) for milestones.

## Layout

```
ocapn-lean/
├── OcapnLean.lean              top-level module (imports everything)
├── OcapnLean/
│   ├── Model.lean              abstract data model
│   ├── Syrup.lean              wire codec (bool/int/bytes; round-trip proved)
│   ├── Captp/
│   │   ├── Messages.lean       op:* / desc:* algebraic types
│   │   ├── Spec.lean           Veil: single-peer  — proves P8, P2
│   │   ├── Twoparty.lean       Veil: two-peer    — proves P1 (FIFO)
│   │   ├── CrossedHellos.lean  Veil: handshake   — proves P5
│   │   ├── Gc.lean             Veil: refcounts   — proves P4
│   │   ├── NoForgery.lean      Veil: authority   — proves P3
│   │   ├── Threeparty.lean     Veil: handoffs    — proves P6
│   │   └── Impl.lean           executable impl   — bootstrap inv. proved in Lean
│   └── Test/
│       └── Interop.lean        byte-parity check vs python ref syrup
├── scripts/
│   ├── run-interop.sh                     captp-level harness skeleton
│   └── regenerate-interop-fixtures.py     refresh syrup fixtures
├── docs/
│   ├── PLAN.md                 proof plan + per-property scoreboard
│   └── ROADMAP.md              milestones M0–M10
├── projects/                   submodules: ocapn-spec, ocapn-test-suite,
│                               syrup-ocapn, goblins, endo, ridley-dobjects, veil
├── lakefile.toml
└── lean-toolchain              pinned: leanprover/lean4:v4.24.0
```

## Build

Requires elan (see [Lean install](https://lean-lang.org/install/)). On
NixOS/this machine `tar`, `unzip`, etc. live in
`/run/current-system/sw/bin`, so build with:

```sh
export PATH="/run/current-system/sw/bin:$HOME/.elan/bin:$PATH"
lake update    # first time only
lake build
```

The first build downloads Z3 4.15.4 and cvc5 1.3.1 (Veil's SMT backends).

## Quick reference

| File | Purpose |
| ---- | ------- |
| `projects/ocapn-spec/draft-specifications/CapTP Specification.md` | the protocol |
| `projects/ocapn-spec/draft-specifications/Model.md`               | the value algebra |
| `projects/veil/Examples/Tutorial/Ring.lean`                       | canonical Veil example |
| `projects/veil/Examples/IvyBench/`                                | benchmark protocols |

## License

TBD.
