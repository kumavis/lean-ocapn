;;; Goblins peer using the testuds netlayer, set up to be driven by
;;; an external client (e.g. ocapn-lean's client driver).
;;;
;;; Run from a directory the client can also read/write:
;;;
;;;   guix shell guile-goblins -- \
;;;     guile -L /<goblins-checkout>/goblins \
;;;           -L /<goblins-checkout>/goblins/contrib \
;;;           scripts/goblins-testuds-server.scm
;;;
;;; (or via nix-shell -p guile guile-goblins on a NixOS host)
;;;
;;; This re-exposes the same swissnum/object set as the upstream
;;; goblins ocapn test-suite example, but listens on
;;;   /tmp/ocapn-lean-uds/goblins.sock
;;; so it can interop with an OcapN-lean peer using the same
;;; directory.
(use-modules (goblins)
             (goblins vat)
             (goblins ocapn captp)
             (goblins ocapn ids)
             (goblins ocapn netlayer testuds)
             (fibers conditions)
             (ice-9 iconv))

(define netlayers-dir "/tmp/ocapn-lean-uds")
(define our-node-id "goblins")

(define (trigger-gc)
  (define (^gc-collect _bcom)
    (lambda ()
      (sleep 1)
      (gc)))
  (define self (spawn ^gc-collect))
  (<-np self))

(define (^echo _bcom)
  (lambda args
    (trigger-gc)
    args))

(define (^greeter _bcom)
  (lambda (target)
    (on (<- target "Hello")
        (lambda result
          (trigger-gc)))))

(define (^promise-resolver _bcom)
  (lambda ()
    (define-values (vow resolver)
      (spawn-promise-and-resolver))
    (list vow resolver)))

(define (^car _bcom color model)
  (lambda ()
    (format #f "Vroom! I am a ~a ~a car!" color model)))

(define (^car-factory _bcom)
  (lambda car-specs
    (define cars
      (map (lambda (spec) (apply spawn ^car spec)) car-specs))
    (apply values cars)))

(define (^car-factory-builder _bcom)
  (lambda () (spawn ^car-factory)))

(define a-vat (spawn-vat))
(with-vat a-vat
  (define netlayer
    (spawn ^testuds-netlayer netlayers-dir #:peer-id our-node-id))
  (define mycapn (spawn-mycapn netlayer))
  (define nonce-registry ($ mycapn 'get-registry))

  ($ nonce-registry 'register
     (spawn ^car-factory-builder)
     (string->bytevector "JadQ0++RzsD4M+40uLxTWVaVqM10DcBJ" "ascii"))
  ($ nonce-registry 'register
     (spawn ^echo)
     (string->bytevector "IO58l1laTyhcrgDKbEzFOO32MDd6zE5w" "ascii"))
  ($ nonce-registry 'register
     (spawn ^greeter)
     (string->bytevector "VMDDd1voKWarCe2GvgLbxbVFysNzRPzx" "ascii"))
  ($ nonce-registry 'register
     (spawn ^promise-resolver)
     (string->bytevector "IokCxYmMj04nos2JN1TDoY1bT8dXh6Lr" "ascii"))

  (format (current-error-port)
          "goblins testuds peer ready, node-id: ~a~%" our-node-id)
  (force-output (current-error-port))
  (format (current-error-port)
          "socket: ~a/~a.sock~%" netlayers-dir our-node-id)
  (force-output (current-error-port)))

(define forever (make-condition))
(wait forever)
