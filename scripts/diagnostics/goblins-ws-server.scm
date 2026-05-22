;;; Minimal Goblins websocket-netlayer peer for ocapn-lean interop testing.
;;;
;;; Usage from inside the repo root:
;;;
;;;   nix-shell -p guile guile-goblins guile-fibers --command \
;;;     "GUILE_AUTO_COMPILE=0 guile \
;;;       scripts/diagnostics/goblins-ws-server.scm [port]"
;;;
;;; Default port is 22090. Output (single line, machine-parseable):
;;;
;;;   goblins-ws-ready designator-hex=ABCD…  port=22090
;;;
;;; Then sleeps indefinitely waiting for an inbound websocket
;;; connection. A driver from ocapn-lean (see
;;; `scripts/ClientVsGuileWs.lean`) parses those two values, opens
;;; a `Ws.Authenticated` connection against the named pubkey, and
;;; runs the OCapN handshake.
;;;
;;; This is the websocket counterpart to the testuds probe in this
;;; same directory. Unlike testuds, the websocket netlayer survives
;;; the standalone-script vat-dispatcher hang (see
;;; `UPSTREAM-GOBLINS-ISSUE.md`) so we can drive it from a one-shot
;;; script with no REPL gymnastics.

(use-modules (goblins)
             (goblins vat)
             (goblins ocapn captp)
             (goblins ocapn ids)
             (goblins ocapn netlayer websocket)
             (goblins utils crypto)
             (fibers conditions)
             (rnrs bytevectors))

(define args (cdr (command-line)))
(define listen-port
  (if (null? args) 22090 (string->number (car args))))

;; Generate the long-lived designator keypair ourselves so we can
;; print the public half — ocapn-lean's `Ws.Authenticated.connect`
;; will verify the auth response against this pubkey.
(define designator-keypair (generate-key-pair))
(define designator-pubkey-bv
  (captp-public-key->bytevector (key-pair->public-key designator-keypair)))

(define (bv->hex bv)
  (string-concatenate
   (map (lambda (i)
          (let* ((b (bytevector-u8-ref bv i))
                 (s (number->string b 16)))
            (if (= 1 (string-length s)) (string-append "0" s) s)))
        (iota (bytevector-length bv)))))

(define machine-vat (spawn-vat))

(define netlayer
  (with-vat machine-vat
    (spawn ^websocket-netlayer
           #:encrypted? #f
           #:port listen-port
           #:designator-key designator-keypair)))

;; A mycapn isn't strictly required for the auth probe (the
;; designator-auth dance happens inside the netlayer, before any
;; CapTP), but standing one up makes the peer accept further
;; `op:start-session` traffic on the same connection.
(define mycapn
  (with-vat machine-vat (spawn-mycapn netlayer)))

;; Two machine-parseable banner lines:
;;   1. designator-hex + port — what the CI Lean driver consumes.
;;   2. uri — the canonical OCapN URI form
;;      (`ocapn://<base32-designator>.websocket?url=ws://host:port`),
;;      which `client-vs-guile-ws --uri ...` accepts directly.
(define our-loc (with-vat machine-vat ($ netlayer 'our-location)))
(format #t "goblins-ws-ready designator-hex=~a port=~a~%"
        (bv->hex designator-pubkey-bv) listen-port)
(format #t "goblins-ws-uri uri=~a~%" (ocapn-id->string our-loc))
(force-output)

;; Block forever — the netlayer's listen loop is alive in the vat.
(wait (make-condition))
