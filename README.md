# ocapn-lean

A Lean 4 implementation of the [OCapN](https://ocapn.org) (Object Capability
Network) protocol with safety properties of the CapTP layer mechanically
proved using [Veil](https://github.com/verse-lab/veil).

## Status

**Six of the eight proposed proofs of behavior are mechanically discharged**
(141 SMT theorems passing under Z3/cvc5 via Veil's `#check_invariants`):

| ID | Property | Module |
| --- | --- | --- |
| **P1** | end-to-end reference FIFO (headline) | `OcapnLean/Captp/Twoparty.lean` |
| **P2** | promise resolution monotonicity (×3) | `OcapnLean/Captp/Spec.lean` |
| **P3** | no-forgery (direct-send case) | `OcapnLean/Captp/NoForgery.lean` |
| **P4** | GC soundness (wire-delta refcount) | `OcapnLean/Captp/Gc.lean` |
| **P5** | crossed-hellos determinism | `OcapnLean/Captp/CrossedHellos.lean` |
| **P8** | bootstrap-at-zero | `OcapnLean/Captp/Spec.lean` |

Remaining: **P6** three-party handoff non-replay (M6 — three-vat composition);
**P7** abort terminal (deferred — needs temporal/history tracking).

See [`docs/PLAN.md`](docs/PLAN.md) for the proof plan and
[`docs/ROADMAP.md`](docs/ROADMAP.md) for milestones.

## Layout

```
ocapn-lean/
├── OcapnLean.lean             top-level module
├── OcapnLean/
│   ├── Model.lean             abstract data model (Atom/Container/Reference)
│   └── Captp/
│       ├── Messages.lean      op:* / desc:* algebraic types
│       └── Spec.lean          Veil module: single-peer state machine
├── docs/
│   ├── PLAN.md                proof plan (P1 = E2E reference FIFO)
│   └── ROADMAP.md             milestones
├── projects/                  read-only reference checkouts (do not modify)
│   ├── ocapn-spec/            canonical draft specifications
│   ├── ocapn-test-suite/      Python interop tests
│   ├── syrup-ocapn/           serialization format
│   ├── goblins/               Spritely Goblins (Guile)
│   ├── endo/                  Endo / @endo/ocapn (JavaScript)
│   ├── ridley-dobjects/       Ridley DObjects (Dart)
│   └── veil/                  Veil framework checkout (for reference)
├── lakefile.toml
└── lean-toolchain             pinned: leanprover/lean4:v4.24.0
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
