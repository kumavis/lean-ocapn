;;; Minimal reproducer for the Goblins testuds "silent handshake" bug.
;;;
;;; Run from anywhere with guile-goblins ≥ 0.16.1 available:
;;;
;;;   nix-shell -p guile guile-goblins guile-fibers \
;;;     --command "GUILE_AUTO_COMPILE=0 guile \
;;;       scripts/diagnostics/goblins-minimal-vat-probe.scm"
;;;
;;; Expected output (working case):
;;;   [min] start
;;;   [min] modules loaded
;;;   [min] vat spawned
;;;   [min] a-nl ok
;;;   [min] a-mycapn ok
;;;   [min] all setup ok, fibers-scheduler exit
;;;   [min] script done
;;;
;;; Observed (Goblins v0.17.0 on Linux x86_64, guile 3.0.11,
;;; guile-fibers 1.3.1): hangs after "[min] a-nl ok". The body of
;;; `(with-vat a-vat (spawn-mycapn a-nl))` executes (per
;;; instrumented probes we ran in earlier sessions), but `vat-send`
;;; never delivers the result back to the calling thread. Wrapping
;;; in `run-fibers` (as below) does NOT change the behaviour.
;;;
;;; Hypothesis: spawn-mycapn's `(on (<- netlayer-map 'data) ...)`
;;; callback in `^mycapn`'s body schedules async work that's
;;; competing with `vat-send`'s reply-delivery on the same fiber
;;; scheduler. Specifically, `(<- netlayer-map 'data)` returns a vow
;;; whose resolution feeds the listen-loop setup; if the vat dispatcher
;;; doesn't drain that callback before vat-send's reply mechanism
;;; completes, the reply never fires.
;;;
;;; Companion symptom on the testuds-server.scm side: an inbound
;;; connection from a non-Goblins peer (e.g. a Python probe sending
;;; a real-signed op:start-session over the UDS socket) gets ZERO
;;; reply bytes within a 3s timeout, even though the server
;;; printed "ready" at startup. Suggests the listen loop also never
;;; gets driven.
;;;
;;; This minimal probe isolates the issue from any wire-format
;;; question — no socket is opened (only the netlayer is constructed),
;;; no remote peer is involved.

(format (current-error-port) "[min] start~%")
(force-output (current-error-port))

(use-modules (goblins)
             (goblins vat)
             (goblins ocapn captp)
             (goblins ocapn netlayer testuds)
             (fibers)
             (fibers conditions))

(format (current-error-port) "[min] modules loaded~%")
(force-output (current-error-port))

(define netlayers-dir "/tmp/goblins-minimal-vat-probe")
(when (file-exists? netlayers-dir)
  (system* "rm" "-rf" netlayers-dir))
(mkdir netlayers-dir)

(run-fibers
 (lambda ()
   (define a-vat (spawn-vat))
   (format (current-error-port) "[min] vat spawned~%")
   (force-output (current-error-port))

   (define a-nl
     (with-vat a-vat
       (spawn ^testuds-netlayer netlayers-dir #:peer-id "alice")))
   (format (current-error-port) "[min] a-nl ok~%")
   (force-output (current-error-port))

   (define a-mycapn
     (with-vat a-vat (spawn-mycapn a-nl)))
   (format (current-error-port) "[min] a-mycapn ok~%")
   (force-output (current-error-port))

   (format (current-error-port) "[min] all setup ok, fibers-scheduler exit~%")
   (force-output (current-error-port)))
 #:drain? #t)

(format (current-error-port) "[min] script done~%")
(force-output (current-error-port))
(exit 0)
