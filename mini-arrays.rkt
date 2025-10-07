#lang racket

(require
 (only-in racket/fixnum               fx+ fx= fx<)
 (except-in rnrs/arithmetic/fixnums-6 fx+)
 ; racket/flonum
         racket/list
         racket/vector
         racket/syntax
         
         rnrs/arithmetic/flonums-6
         (only-in srfi/1 iota take drop fold list-copy every)
         (only-in srfi/43 vector-every vector-concatenate)
         (for-syntax racket/syntax
                     (only-in racket/fixnum               fx+ fx= fx<)
                     (except-in rnrs/arithmetic/fixnums-6 fx+)
                     rnrs/arithmetic/flonums-6)
         srfi/4)

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

(define-syntax (define-type stx)
  (syntax-case stx ()
    [(_ name stuff ...)
     (let* ((lst (syntax->list #'(stuff ...)))
            (fields
             (for/list ([item lst]
                        #:when (identifier? item)
                        #:unless (regexp-match #px":$"
                                               (symbol->string (syntax-e item))))
               item)))
       (with-syntax ([(field ...) fields]
                     [ctor (format-id #'name "make-~a" #'name)]
                     [((setter alias) ...)
                      (for/list ([field fields])
                        (list (format-id #'name "set-~a-~a!" #'name field)
                              (format-id #'name "~a-~a-set!" #'name field)))])
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

(include "mini-arrays.scm")

(provide (all-defined-out))
