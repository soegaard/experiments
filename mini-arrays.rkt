#lang racket
(provide (all-defined-out))

(require
  ; Homogeneous vectors
  (except-in ffi/vector u8vector-copy!)
  "vector-functions.rkt" ; s8vector-copy! and friends
  
  racket/list
  racket/vector
  racket/syntax

  (only-in srfi/1 iota take drop fold list-copy every)
  (only-in srfi/43 vector-every vector-concatenate)

  srfi/27 ; random number generation

  ; use Scheme names for most flonum and fixnum operations
  rnrs/arithmetic/flonums-6
  (only-in racket/flonum ->fl fl= flrandom)

  (except-in rnrs/arithmetic/fixnums-6 fx+)
  (only-in racket/fixnum               fx+ fx= fx< fx> fx<= fxquotient)
  
  (for-syntax racket/syntax
              racket/string
              (only-in racket/fixnum               fx+ fx= fx< fx> fx<= fxquotient)
              (except-in rnrs/arithmetic/fixnums-6 fx+)
              rnrs/arithmetic/flonums-6)
  )

;; Compatibility helpers for Gambit Scheme code

(define (flscalbn x n)
  (let ((factor (expt 2 n)))
    (fl* x (exact->inexact factor))))

(define (flcopysign magnitude sign)
  (if (flnegative? sign)
      (fl- 0.0 (flabs magnitude))
      (flabs magnitude)))

(define (flonum->fixnum x)
  (inexact->exact x))

(define (random-f64vector n)
  (define g (current-pseudo-random-generator))
  (list->f64vector (build-list n (λ (_) (flrandom g)))))

(define (concatenate xss)
  (append* xss))

(define (make-list n [fill 0])
  (for/list ([_ n]) fill)) 

(define pp pretty-print)

;;; Error exceptions in Gambit carry both a message and
;;; and some objects.

(struct exn:fail:error exn:fail (objects)
  #:extra-constructor-name make-exn:fail:error
  #:transparent)
  
; The error functions of Racket and Gambit differ slightly.
(define (error message . objects)
  (raise (exn:fail:error message  
                         (current-continuation-marks)
                         objects)))

(define (with-exception-catcher handler thunk)
  (with-handlers ([exn:fail:error? (λ (e) (handler e))])
    (thunk)))

(define (error-exception? e)
  exn:fail:error)

(define (error-exception-message e)
  (exn-message e))

(define (unbound-global-exception? e)
  exn?)

(define unbound-global-exception-variable #f)

(define (wrong-number-of-arguments-exception? e)
  (exn:fail:contract:arity? e))

;;; flilog

;; Constants mirroring common C/POSIX choices.
;; (The standard allows implementation-defined values for FP_ILOGB0
;; and FP_ILOGBNAN; many libcs use these.)
(define INT-MAX        2147483647)
(define FP-ILOGB0     -2147483647) ; allowed: either INT_MIN or -INT_MAX
(define FP-ILOGBNAN    2147483647) ; often equals INT_MAX

;; Return the unbiased base-2 exponent of a flonum, à la C ilogb().
;; For subnormals, returns the exponent of the normalized equivalent.
;;   Zero -> FP-ILOGB0,  ±Inf -> INT_MAX,  NaN -> FP-ILOGBNAN.
(define (flilogb x)
  (define xfl (if (exact-integer? x) (->fl x) x))
  (cond
    [(flnan? xfl)         FP-ILOGBNAN]
    [(or (fl= xfl +inf.0) (fl= xfl -inf.0)) INT-MAX]
    [(fl= xfl 0.0)        FP-ILOGB0]
    [else
     ;; Extract IEEE-754 fields from the 64-bit representation.
     (define bs       (real->floating-point-bytes xfl 8 (system-big-endian?)))
     (define bits     (integer-bytes->integer bs (system-big-endian?) #f))
     (define exp-bits (bitwise-and (arithmetic-shift bits -52) #x7FF))
     (define frac     (bitwise-and bits #x000FFFFFFFFFFFFF))
     (define BIAS     1023)
     (cond
       ; normal numbers
       [(and (positive? exp-bits) (< exp-bits 2047))
        (- exp-bits BIAS)] 
       [(zero? exp-bits)
        ; subnormal: ilogb = -1023 - leading_zeros(frac)
        (define (leading-zeros-52 f)
          (let loop ([i 51])
            (cond [(< i 0) 52]
                  [(bitwise-bit-set? f i) (- 51 i)]
                  [else (loop (sub1 i))])))
        (- 0 BIAS (leading-zeros-52 frac))]  ; -1023 - lz
       [else
        ; exp-bits = 2047 would be inf/nan, but we handled those above
        FP-ILOGBNAN])]))


;;; Syntax

(begin-for-syntax
  (define (colon-suffix? id)
    (define s (symbol->string (syntax-e id)))
    (string-suffix? s ":")))


(define-syntax (define-type stx)
  (syntax-case stx ()
    [(_ name stuff ...)
     (let* ([lst      (syntax->list #'(stuff ...))]
            [field-id (lambda (item)
                        (syntax-case item ()
                          [(id . _)  (and (identifier? #'id)
                                          (not (colon-suffix? #'id))
                                          #'id)]
                          [id        (and (identifier? #'id)
                                          (not (colon-suffix? #'id))
                                          #'id)]
                          [_         #f]))]
            [fields  (for/list ([item lst]
                                #:do [(define field (field-id item))]
                                #:when field)
                       field)])
       (with-syntax
         ([(field ...)          fields]
          [ctor                 (format-id #'name "make-~a" #'name)]
          [((setter alias) ...) (for/list ([field fields])
                                  (list (format-id #'name "set-~a-~a!"
                                                   #'name field)
                                        (format-id #'name "~a-~a-set!"
                                                   #'name field)))])
         #'(begin
             (struct name (field ...)
               #:transparent
               #:mutable
               #:constructor-name ctor)
             (begin
               (define alias setter)
               ...))))]))

(define-syntax (define-macro stx)
  (syntax-case stx ()
    [(_ (name . params) body ...)
     #'(define-syntax name
         (lambda (stx)
           (define (macro-fn . params)
             body ...)
           (let* ((parts (syntax->list stx))
                  (datums (map syntax->datum parts)))
             (datum->syntax stx
                            (apply macro-fn (cdr datums))))))]))

; ignore Gambit specific declarations
(define-syntax (declare stx) #'(void))

; Gambit has one-armed `if`.
(let-syntax ([if (λ (stx)
                   (syntax-case stx ()
                     [(_if e0 e1)    #'(if e0 e1 (void))]
                     [(_if e0 e1 e2) #'(if e0 e1 e2)]))])

  (include "mini-arrays.scm")
  (include "test-mini-arrays.scm")
  ; (test (+ 1 2) 4) ; '((+ 1 2) " => " 3 ", not " 4)
  (void)
  )


; Test cases for `flilogb`:

; (flilogb 1.0)         ; => 0
; (flilogb 0.75)        ; => -1
; (flilogb 1024.0)      ; => 10
; (flilogb 5e-324)      ; => -1074   ; smallest subnormal
; (flilogb 0.0)         ; => FP-ILOGB0
; (flilogb +inf.0)      ; => INT-MAX
; (flilogb +nan.0)      ; => FP-ILOGBNAN
