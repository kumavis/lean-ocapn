# Draft upstream issue: testuds peer doesn't reply to inbound op:start-session

Target: <https://codeberg.org/spritely/goblins>

Status: draft. Ready to file once we've cross-validated against the
upstream `examples/try-base-netlayer.scm` REPL flow and confirmed the
hang is reproducible there. Saved here so the analysis isn't lost.

---

## Title

`testuds` netlayer peer never accepts inbound connections from a
standalone (non-REPL) script

## Summary

A goblins peer started from a **standalone** script (as opposed to
the REPL) that pairs `spawn-vat`, `(with-vat … (spawn ^testuds-netlayer
…))`, and `(with-vat … (spawn-mycapn …))` never delivers its
`op:start-session` to inbound connections. The accept loop appears
to never run. The same construction works fine when typed into the
REPL.

Observed on:
- guile-goblins 0.17.0 (and earlier — 0.16.1 has the same shape)
- guile 3.0.11
- guile-fibers 1.3.1
- Linux x86_64 (Nixos host)

## Reproducer

A minimal probe is at
[`scripts/diagnostics/goblins-minimal-vat-probe.scm`](goblins-minimal-vat-probe.scm)
in the `kumavis/lean-ocapn` repo. It does only the netlayer + mycapn
spawn — no socket activity, no remote peer. Run with:

```sh
nix-shell -p guile guile-goblins guile-fibers \
  --command "GUILE_AUTO_COMPILE=0 guile \
    scripts/diagnostics/goblins-minimal-vat-probe.scm"
```

The probe wraps the body in `run-fibers` to rule out the obvious
"top-of-script isn't in the fibers scheduler" theory. Expected
output ends with `[min] script done`; observed output hangs after
`[min] a-nl ok` (i.e., the netlayer spawns fine, but
`(with-vat a-vat (spawn-mycapn a-nl))` never returns).

A more elaborate variant in this repo's
[`scripts/goblins-testuds-server.scm`](../goblins-testuds-server.scm)
runs the full server-side setup with the standard ocapn-test-suite
swissnums registered. It does print "ready" — which is misleading;
inbound connections still aren't served. Drove it with a Python
probe sending a real-signed `op:start-session`; received zero bytes
within a 3s timeout.

## Hypothesis

`spawn-mycapn` (in `goblins/ocapn/captp.scm`) constructs the
`netlayer-map` and spawns `^mycapn`. Inside `^mycapn`'s body, this
runs at spawn time:

```scheme
(on (<- netlayer-map 'data)
    (lambda (netlayer-map-data)
      (hashmap-for-each
       (lambda (netlayer-name netlayer)
         (<-np netlayer 'setup (spawn ^connection-establisher self netlayer netlayer-name)))
       netlayer-map-data)))
```

The callback fires the `'setup` message that turns on the listen
loop. If the vat dispatcher doesn't drain this callback before
`vat-send`'s reply path completes — or if the reply path's
fiber-channel send is blocked waiting on a continuation that's now
queued behind the `on`-callback — then `with-vat`'s caller never
sees a return, AND the listen loop never starts.

`run-fibers` wrapping doesn't fix it, suggesting the issue is
internal to the vat dispatcher's reply mechanism rather than the
absence of a scheduler.

## Why it works in the REPL

The REPL evaluates top-level forms one at a time and yields between
them, giving the vat scheduler chances to drain its pending fibers.
A standalone script runs in one phase and (apparently) doesn't
provide those yield points.

## Suggested fix directions

1. (Goblins-side, smallest) Document that top-level `with-vat ; …
   spawn-mycapn` requires the caller to drain the vat afterwards, and
   provide a `setup-mycapn!` helper that explicitly waits for the
   `on netlayer-map 'data` callback to fire.

2. (Goblins-side, larger) Restructure `^mycapn`'s body to do the
   netlayer-map iteration synchronously rather than via `on`, since
   the netlayer-map is provided at construction time and doesn't
   need to be awaited.

3. (Caller-side workaround we're not adopting) Wrap our script in
   an explicit fibers loop and yield after each `with-vat`. We'd
   need to know how long to yield, which is fragile.

## Cross-validation TODO before filing

- [ ] Adapt upstream `examples/try-base-netlayer.scm` to a
  standalone script (the upstream is REPL-driven). If the standalone
  version hangs, file. If it works, the bug is specific to how
  `lean-ocapn` is calling.
- [ ] Test on guile-goblins 0.18.0 / main HEAD to see if it's
  already fixed.
- [ ] Try running with a small delay after `spawn-mycapn` to give the
  vat dispatcher time to drain its callback queue.

## Related

- INTEROP.md §"Goblins testuds, current state" in this repo, which
  documents the symptom from the lean-ocapn-as-client side.
- Disagreement 1 (`<ocapn-peer>` vs `<ocapn-node>`) is already
  resolved upstream in 0.16.1; this issue is separate.
