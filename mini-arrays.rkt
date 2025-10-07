#lang racket

(require
 racket/list
 racket/vector
 racket/syntax

 (only-in racket/flonum ->fl fl=)

 srfi/160/s8
 srfi/160/u8
 srfi/160/s16
 srfi/160/u16
 srfi/160/s32
 srfi/160/u32
 srfi/160/s64
 srfi/160/u64

 srfi/160/f32
 srfi/160/f64

 ; ffi/vector ; for s8vector and friends

 (only-in srfi/1 iota take drop fold list-copy every)
 (only-in srfi/43 vector-every vector-concatenate)

 rnrs/arithmetic/flonums-6

 (only-in racket/fixnum               fx+ fx= fx< fx> fx<= fxquotient)
 (except-in rnrs/arithmetic/fixnums-6 fx+)

 (for-syntax racket/syntax
             racket/string
             (only-in racket/fixnum               fx+ fx= fx< fx> fx<= fxquotient)
             (except-in rnrs/arithmetic/fixnums-6 fx+)
             rnrs/arithmetic/flonums-6)
 ; srfi/4
 )

;; Compatibility helpers for Gambit Scheme code

(define (fxeven? x)
  (fx= (fxand x 1) 0))

(define (flscalbn x n)
  (let ((factor (expt 2 n)))
    (fl* x (exact->inexact factor))))

(define (flcopysign magnitude sign)
  (if (flnegative? sign)
      (fl- 0.0 (flabs magnitude))
      (flabs magnitude)))

(define (flonum->fixnum x)
  (inexact->exact x))

(define (concatenate xss)
  (append* xss))

;;; flilog

;; Constants mirroring common C/POSIX choices.
;; (The standard allows implementation-defined values for FP_ILOGB0
;; and FP_ILOGBNAN; many libcs use these.)
(define INT-MAX        2147483647)
(define FP-ILOGB0     -2147483647) ; allowed: either INT_MIN or -INT_MAX
(define FP-ILOGBNAN    2147483647) ; often equals INT_MAX

;; Return the unbiased base-2 exponent of a flonum, à la C ilogb().
;; For subnormals, returns the exponent of the normalized equivalent.
;; Zero -> FP-ILOGB0, ±Inf -> INT_MAX, NaN -> FP-ILOGBNAN.
(define (flilogb x)
  (define xfl (if (exact-integer? x) (->fl x) x))
  (cond
    [(flnan? xfl)      FP-ILOGBNAN]
    [(or (fl= xfl +inf.0) (fl= xfl -inf.0)) INT-MAX]
    [(fl= xfl 0.0)     FP-ILOGB0]
    [else
     ;; Extract IEEE-754 fields from the 64-bit representation.
     (define bs (real->floating-point-bytes xfl 8 (system-big-endian?)))
     (define bits (integer-bytes->integer bs (system-big-endian?) #f))
     (define exp-bits (bitwise-and (arithmetic-shift bits -52) #x7FF))
     (define frac      (bitwise-and bits #x000FFFFFFFFFFFFF))
     (define BIAS 1023)
     (cond
       [(and (positive? exp-bits) (< exp-bits 2047))
        (- exp-bits BIAS)]                    ; normal numbers
       [(zero? exp-bits)
        ;; subnormal: ilogb = -1023 - leading_zeros(frac)
        (define (leading-zeros-52 f)
          (let loop ([i 51])
            (cond [(< i 0) 52]
                  [(bitwise-bit-set? f i) (- 51 i)]
                  [else (loop (sub1 i))])))
        (- 0 BIAS (leading-zeros-52 frac))]  ; -1023 - lz
       [else
        ;; exp-bits = 2047 would be inf/nan, but we handled those above
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

(define-syntax (declare stx) #'(void))
  

(include "mini-arrays.scm")
; (include "test-mini-arrays.scm")

(provide (all-defined-out))



; Test cases for `flilogb`:

; (flilogb 1.0)         ; => 0
; (flilogb 0.75)        ; => -1
; (flilogb 1024.0)      ; => 10
; (flilogb 5e-324)      ; => -1074   ; smallest subnormal
; (flilogb 0.0)         ; => FP-ILOGB0
; (flilogb +inf.0)      ; => INT-MAX
; (flilogb +nan.0)      ; => FP-ILOGBNAN
