#lang racket
(require ffi/vector
         ffi/unsafe
         (for-syntax racket/base racket/syntax syntax/parse))

;; define-copy! for homogeneous vectors using memmove
(define-syntax (define-hvec-copy! stx)
  (syntax-case stx ()
    [(_ (vec-id ctype) ...)
     (with-syntax* ([(pred? ...)  (for/list ([v (syntax->list #'(vec-id ...))])
                                    (format-id v "~a?" v))]
                    [(len-id ...) (for/list ([v (syntax->list #'(vec-id ...))])
                                    (format-id v "~a-length" v))]
                    [(ptr-id ...) (for/list ([v (syntax->list #'(vec-id ...))])
                                    (format-id v "~a->cpointer" v))]
                    [(name ...)    (for/list ([v (syntax->list #'(vec-id ...))])
                                     (format-id v "~a-copy!" v))])
       #'(begin
           (provide name) ...
           (define (name dest dest-start src [start 0] [end (len-id src)])
             ;; argument checks
             (unless (pred? dest)
               (raise-argument-error 'name "predicate for dest" dest))
             (unless (pred? src)
               (raise-argument-error 'name "predicate for src" src))
             (unless (exact-nonnegative-integer? dest-start)
               (raise-argument-error 'name
                                     "exact-nonnegative-integer?" dest-start))
             (unless (exact-nonnegative-integer? start)
               (raise-argument-error 'name
                                     "exact-nonnegative-integer?" start))
             (unless (exact-integer? end)
               (raise-argument-error 'name "exact-integer?" end))

             (define src-len (len-id src))
             (define dst-len (len-id dest))
             (unless (and (<= 0 start end) (<= end src-len))
               (raise-range-error 'name "vector" "start..end"
                                  start src 0 src-len))
             (define count (- end start))
             (unless (<= (+ dest-start count) dst-len)
               (raise-range-error 'name "vector" "dest-start..dest-start+len"
                                  dest-start dest 0 dst-len))

             (when (> count 0)
               (define dst-ptr (ptr-id dest))
               (define src-ptr (ptr-id src))
               (memmove dst-ptr dest-start src-ptr start count ctype))
             (void))
           ...))]))

;; Instantiate for all homogeneous vector kinds
(define-hvec-copy!
  (u8vector  _uint8)
  (s8vector  _int8)
  (s16vector _int16)
  (u16vector _uint16)
  (s32vector _int32)
  (u32vector _uint32)
  (s64vector _int64)
  (u64vector _uint64)
  (f32vector _float)
  (f64vector _double))

;; ------------ quick sanity checks ------------
(module+ test
  (require rackunit)
  ;; integer vectors
  (define d8 (s8vector 0 0 0 0 0))
  (define s8 (s8vector 1 2 3 4 5))
  (s8vector-copy! d8 1 s8 0 3)
  (check-equal? (for/list ([i (in-range (s8vector-length d8))])
                  (s8vector-ref d8 i))
                '(0 1 2 3 0))

  (define v8 (s8vector 0 1 2 3 4 5))
  (s8vector-copy! v8 1 v8 0 2) ; overlap-safe
  (check-equal? (for/list ([i (in-range (s8vector-length v8))])
                  (s8vector-ref v8 i))
                '(0 0 1 3 4 5))

  ;; float vectors
  (define fd (f32vector 0.0 0.0 0.0 0.0))
  (define fs (f32vector 1.0 2.0 3.0 4.0))
  (f32vector-copy! fd 1 fs 0 2)
  (check-equal? (for/list ([i (in-range (f32vector-length fd))])
                  (f32vector-ref fd i))
                '(0.0 1.0 2.0 0.0)))
