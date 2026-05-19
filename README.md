# ocapn-lean

A Lean 4 implementation of the [OCapN](https://ocapn.org) (Object Capability
Network) protocol with safety properties of the CapTP layer mechanically
proved using [Veil](https://github.com/verse-lab/veil).

## Status

**Seven of the eight proposed proofs of behavior are mechanically discharged**
(235 SMT theorems passing under Z3/cvc5 via Veil's `#check_invariants` —
Spec 143, Twoparty 48, Gc 18, CrossedHellos 12, NoForgery 8, Threeparty 6):

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
│   ├── Crypto.lean             Ed25519 + SHA256 via libsodium FFI
│   ├── Locators.lean           PeerLocator + SturdyRef (Syrup round-trip proved)
│   ├── Syrup.lean              wire codec (bool/int/bytes; universal round-trip proved)
│   ├── Syrup/
│   │   ├── Extended.lean       codec (str/sym/list/record/dict; fueled total decoder)
│   │   └── RoundTripExt.lean   universal round-trip `decodeExt ∘ encodeExt = some` for all `ValueExt` (+ encoder injectivity)
│   ├── Netlayer.lean           abstract `Netlayer { send, recv?, close }`
│   ├── Netlayer/
│   │   ├── Tcp.lean            libuv-backed TCP reference netlayer
│   │   └── Uds.lean            unix-domain-socket netlayer (matches Goblins testuds)
│   ├── Uds.lean                UDS bindings re-export
│   ├── Server.lean             `lake exe ocapn-server` — accept loop
│   ├── Captp/
│   │   ├── Messages.lean       op:* / desc:* algebraic types
│   │   ├── Spec.lean           Veil: single-peer  — proves P8, P2, listen-notify (143 thms)
│   │   ├── Twoparty.lean       Veil: two-peer     — proves P1 (FIFO) (48 thms)
│   │   ├── CrossedHellos.lean  Veil: handshake    — proves P5 (12 thms)
│   │   ├── Gc.lean             Veil: refcounts    — proves P4 (18 thms)
│   │   ├── NoForgery.lean      Veil: authority    — proves P3 (8 thms)
│   │   ├── Threeparty.lean     Veil: handoffs     — proves P6 (6 thms)
│   │   ├── Impl.lean           executable impl    — bootstrapAtZero in pure Lean
│   │   ├── Refinement.lean     simulates + initial/abort/export/import refines + 3 lifts
│   │   ├── RefinementExtended.lean   extended-action refinement
│   │   ├── Run.lean            FramedConn + runHandler event loop
│   │   ├── Bootstrap.lean      swissnum registry + dispatchFetch
│   │   ├── Session.lean        per-connection handshake + dispatch
│   │   └── Client.lean         outbound CapTP driver (Lean-as-client)
│   └── Test/
│       ├── Interop.lean        byte-parity checks vs python ref syrup
│       └── Locators.lean       Ridley-ported PeerLocator + SturdyRef unit tests
├── scripts/
│   ├── netlayer-echo.lean              TCP echo loopback smoke test
│   ├── captp-framed-echo.lean          syrup-framed CapTP exchange over TCP
│   ├── bootstrap-echo-gc.lean          end-to-end op:deliver/fetch routing
│   ├── ClientSmoke.lean                client-side handshake smoke
│   ├── ClientVsExternal.lean           Lean-as-client driver vs any OCapN peer
│   ├── ClientVsUds.lean                Lean-as-client driver over UDS (Goblins testuds)
│   ├── CryptoSmoke.lean                Ed25519 sign/verify FFI smoke
│   ├── EnlivenerSmoke.lean             sturdyref-enlivener bootstrap-object smoke
│   ├── SessionHandshakeSmoke.lean      full op:start-session exchange smoke
│   ├── UdsProbe.lean / UdsSmoke.lean   UDS netlayer probes
│   ├── interop-invalid-handshake.py    real-crypto handshake error-path tests
│   ├── goblins-testuds-server.scm      Goblins-side UDS server for interop probes
│   ├── run-interop.sh                  captp-level harness skeleton
│   ├── regenerate-interop-fixtures.py  refresh syrup fixtures
│   └── diagnostics/                    upstream-issue drafts + minimal reproducers
├── docs/
│   ├── PLAN.md                 proof plan + per-property scoreboard
│   ├── ROADMAP.md              milestones M0–M10
│   └── INTEROP.md              cross-impl test results + disagreements log
├── projects/                   submodules: ocapn-spec, ocapn-test-suite,
│                               syrup-ocapn, goblins (codeberg), endo,
│                               ridley-dobjects, veil
├── lakefile.toml
└── lean-toolchain              pinned: leanprover/lean4:v4.24.0
```

## Running the reference server

```sh
# Terminal 1
lake exe ocapn-server -- --port 22045

# Terminal 2 — drive the server end-to-end from the Lean client
lake exe client-vs-external -- --port 22045
# or exercise the error-path handshakes with real Ed25519 crypto:
nix-shell -p "python3.withPackages (p: with p; [ cryptography stem ])" \
  --command "python3 scripts/interop-invalid-handshake.py"
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
