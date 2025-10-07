(define-type %%interval
  copier: #f
  no-functional-setter:
  read-only:
  lower-bounds
  upper-bounds)

(define-type %%array
  copier: #f
  no-functional-setter:
  (domain read-only:)
  (getter read-only:)
  (setter read-write:)
  (storage-class read-only:)
  (body read-only:)
  (indexer read-only:))

(define-type storage-class
  copier: #f
  read-only:
  no-functional-setter:
  getter
  setter
  checker
  maker
  copier
  length
  default
  data?
  data->body
  )

(define interval? %%interval?)

(define make-interval
  (case-lambda
   ((upper-bounds)
    (make-%%interval (make-vector (vector-length upper-bounds) 0)
                     (vector-copy upper-bounds)))
   ((lower-bounds upper-bounds)
    (make-%%interval (vector-copy lower-bounds)
                     (vector-copy upper-bounds)))))

(define (interval-lower-bound interval i)
  (vector-ref (%%interval-lower-bounds interval) i))

(define (interval-upper-bound interval i)
  (vector-ref (%%interval-upper-bounds interval) i))

(define (interval-width interval i)
  (- (interval-upper-bound interval i)
     (interval-lower-bound interval i)))

(define (interval-widths interval)
  (vector-map - (%%interval-upper-bounds interval) (%%interval-lower-bounds interval)))

(define (interval-lower-bounds->vector interval)
  (vector-copy (%%interval-lower-bounds interval)))

(define (interval-upper-bounds->vector interval)
  (vector-copy (%%interval-upper-bounds interval)))

(define (interval-lower-bounds->list interval)
  (vector->list (%%interval-lower-bounds interval)))

(define (interval-upper-bounds->list interval)
  (vector->list (%%interval-upper-bounds interval)))

(define (index-first n k)
  (let ((identity-permutation (iota n)))
    (list->vector
     (cons k (append (take identity-permutation k)
                     (drop identity-permutation (+ k 1)))))))

(define (index-last n k)
  (let ((identity-permutation (iota n)))
    (list->vector
     (append (take identity-permutation k)
             (drop identity-permutation (+ k 1))
             (list k)))))

(define (index-swap n i j)
  (let ((result (list->vector (iota n))))
    (vector-set! result i j)
    (vector-set! result j i)
    result))

(define (index-rotate n k)
  (let ((identity-permutation (iota n)))
    (list->vector
     (append (drop identity-permutation k)
             (take identity-permutation k)))))

(define (interval-volume interval)
  (apply * (vector->list (interval-widths interval))))

(define (interval-empty? interval)
  (zero? (interval-volume interval)))

(define (interval-dimension interval)
  (vector-length (%%interval-lower-bounds interval)))

(define (interval-projections interval right-dimension)
  (let ((left-dimension
         (- (interval-dimension interval) right-dimension))
        (lowers
         (interval-lower-bounds->list interval))
        (uppers
         (interval-upper-bounds->list interval)))
    (values (make-interval (list->vector (take lowers left-dimension))
                           (list->vector (take uppers left-dimension)))
            (make-interval (list->vector (drop lowers left-dimension))
                           (list->vector (drop uppers left-dimension))))))

(define (interval-cartesian-product . intervals)
  (make-interval (vector-concatenate (map %%interval-lower-bounds intervals))
                 (vector-concatenate (map %%interval-upper-bounds intervals))))

(define (permutation? permutation)
  (and (vector? permutation)
       (let* ((n (vector-length permutation))
              (permutation-range (make-vector n #f)))
         (let loop ((i 0))
           (or (= i n)
               (let ((p_i (vector-ref permutation i)))
                 (and (< -1 p_i n)
                      (not (vector-ref permutation-range p_i))
                      (let ()
                        (vector-set! permutation-range p_i #t)
                        (loop (+ i 1))))))))))

(define (%%vector-permute vector permutation)
  (let* ((n (vector-length vector))
         (result (make-vector n)))
    (do ((i 0 (+ i 1)))
        ((= i n) result)
      (vector-set! result i (vector-ref vector (vector-ref permutation i))))))

(define (%%vector-permute->list vector permutation)
  (do ((i (fx- (vector-length vector) 1) (fx- i 1))
       (result '() (cons (vector-ref vector (vector-ref permutation i))
                         result)))
      ((fx< i 0) result)))

(define (%%permutation-invert permutation)
  (let* ((n (vector-length permutation))
         (result (make-vector n)))
    (do ((i 0 (fx+ i 1)))
        ((fx= i n) result)
      (vector-set! result (vector-ref permutation i) i))))

(define (interval-permute interval permutation)
  (make-interval (%%vector-permute (%%interval-lower-bounds interval) permutation)
                 (%%vector-permute (%%interval-upper-bounds interval) permutation)))

(define (translation? translation)
  (and (vector? translation)
       (vector-every exact-integer? translation)))

(define (interval-translate interval translation)
  (make-interval (vector-map + (%%interval-lower-bounds interval) translation)
                 (vector-map + (%%interval-upper-bounds interval) translation)))

(define interval-rebase
  (case-lambda
   ((interval)
    (make-interval (vector-map - (%%interval-upper-bounds interval) (%%interval-lower-bounds interval))))
   ((interval new-lower-bounds)
    (make-interval new-lower-bounds
                   (vector-map (lambda (u l new-l)
                                 (+ (- u l) new-l))
                               (%%interval-upper-bounds interval)
                               (%%interval-lower-bounds interval)
                               new-lower-bounds)))))

(define (interval-scale interval scales)
  (let* ((uppers (%%interval-upper-bounds interval))
         (lowers (%%interval-lower-bounds interval))
         (new-uppers (vector-map (lambda (u s)
                                   (quotient (+ u s -1) s))
                                 uppers scales)))
    (make-interval lowers new-uppers)))

(define (interval-dilate interval lower-diffs upper-diffs)
  (let ((new-lowers (vector-map + (%%interval-lower-bounds interval) lower-diffs))
        (new-uppers (vector-map + (%%interval-upper-bounds interval) upper-diffs)))
    (make-interval new-lowers new-uppers)))

(define interval= equal?)

(define (interval-subset? interval1 interval2)
  (and (vector-every >= (%%interval-lower-bounds interval1) (%%interval-lower-bounds interval2))
       (vector-every <= (%%interval-upper-bounds interval1) (%%interval-upper-bounds interval2))))

(define (interval-intersect interval . intervals)
  (let* ((intervals (cons interval intervals))
         (lowers (apply vector-map max (map %%interval-lower-bounds intervals)))
         (uppers (apply vector-map min (map %%interval-upper-bounds intervals))))
    (and (vector-every <= lowers uppers)
         (make-interval lowers uppers))))

(define interval-insert-axis
  (case-lambda
   ((interval k)
    (interval-insert-axis interval k 1))
   ((interval k u_k)
    (let ((lowers (interval-lower-bounds->list interval))
          (uppers (interval-upper-bounds->list interval)))
      (make-interval (list->vector (append (take lowers k) (list 0) (drop lowers k)))
                     (list->vector (append (take uppers k) (list u_k) (drop uppers k))))))))

(define (compute-broadcast-intervals intervals)
  (let* ((max-dim
          (apply max (map interval-dimension intervals)))
         (indices
          (iota max-dim))
         (intervals   ;; add axes to the left with lower bound 0 and upper bound 1
          (map (lambda (interval)
                 (interval-cartesian-product
                  (make-interval (make-vector (- max-dim (interval-dimension interval)) 1))
                  interval))
               intervals))
         (lower-bounds
          (%%interval-lower-bounds (car intervals)))
         (max-upper-bounds
          (list->vector
           (map (lambda (k)
                  (apply max (map (lambda (interval)
                                    (interval-upper-bound interval k))
                                  intervals)))
                indices))))
    (and (every (lambda (interval)
                  (equal? (%%interval-lower-bounds interval) lower-bounds))
                (cdr intervals))
         (every (lambda (k)
                  (let ((max-upper-bound (vector-ref max-upper-bounds k))
                        (lower-bound (vector-ref lower-bounds k)))
                    (if (eqv? lower-bound 0)
                        (every (lambda (interval)
                                 (let ((upper-bound (interval-upper-bound interval k)))
                                   (or (eqv? upper-bound 1)
                                       (eqv? upper-bound max-upper-bound))))
                               intervals)
                        (every (lambda (interval)
                                 (eqv? (interval-upper-bound interval k)
                                       (vector-ref max-upper-bounds k)))
                               intervals))))
                indices)
         (make-interval lower-bounds max-upper-bounds))))
  
(define (interval-contains-multi-index? interval . multi-index)
  (let ((vec-multi-index (list->vector multi-index)))
    (and (vector-every <= (%%interval-lower-bounds interval) vec-multi-index)
         (vector-every >  (%%interval-upper-bounds interval) vec-multi-index))))

(define (%%get-next-args reversed-args
                         reversed-lowers
                         reversed-uppers)
  ;; returns the next reversed multi-index in the interval
  ;; with the given reversed lowers and reversed uppers
  ;; or #f if there is no following multi-index.
  (and (not (null? reversed-args))
       (let ((next-index (+ (car reversed-args) 1)))
         (if (< next-index (car reversed-uppers))
             (cons next-index (cdr reversed-args))
             (let ((tail-result (%%get-next-args (cdr reversed-args)
                                                 (cdr reversed-lowers)
                                                 (cdr reversed-uppers))))
               (and tail-result
                    (cons (car reversed-lowers) tail-result)))))))

(define (interval-for-each f interval)
  (if (interval-empty? interval)
      (void)
      (let ((reversed-lowers (reverse (interval-lower-bounds->list interval)))
            (reversed-uppers (reverse (interval-upper-bounds->list interval))))
        (let loop ((reversed-args reversed-lowers))
          (let ((ignore (apply f (reverse reversed-args)))
                (next-reversed-args (%%get-next-args reversed-args
                                                     reversed-lowers
                                                     reversed-uppers)))
            (if next-reversed-args
                (loop next-reversed-args)
                (void)))))))

(define (interval-fold-left f operator left-identity interval)
  (if (interval-empty? interval)
      left-identity
      (let ((reversed-lowers (reverse (interval-lower-bounds->list interval)))
            (reversed-uppers (reverse (interval-upper-bounds->list interval))))
        (let loop ((reversed-args reversed-lowers)
                   (result left-identity))
          (let ((result (operator result (apply f (reverse reversed-args))))
                (next-reversed-args (%%get-next-args reversed-args
                                                     reversed-lowers
                                                     reversed-uppers)))
            (if next-reversed-args
                (loop next-reversed-args result)
                result))))))

(define (interval-fold-right f operator right-identity interval)
  (if (interval-empty? interval)
      right-identity
      (let ((reversed-lowers (reverse (interval-lower-bounds->list interval)))
            (reversed-uppers (reverse (interval-upper-bounds->list interval))))
        (let loop ((reversed-args reversed-lowers))
          (if reversed-args
              (let* ((item (apply f (reverse reversed-args)))
                     (result (loop (%%get-next-args reversed-args
                                                    reversed-lowers
                                                    reversed-uppers))))
                (operator item result))
              right-identity)))))

(define specialized-array-default-mutable?
  (make-parameter
   #t
   (lambda (bool)
     (if (boolean? bool)
         bool
         (error "specialized-array-default-mutable?: The argument is not a boolean: " bool)))))

(define make-array
  (case-lambda
   ((domain getter)
    (make-%%array domain
                  getter
                  #f      ;; setter
                  #f      ;; storage-class
                  #f      ;; body
                  #f))    ;; indexer
   ((domain getter setter)
    (make-%%array domain
                  getter
                  setter
                  #f      ;; storage-class
                  #f      ;; body
                  #f))))  ;; indexer

(define array? %%array?)

(define array-domain %%array-domain)

(define array-getter %%array-getter)

(define (array-dimension array)
  (interval-dimension (array-domain array)))

(define array-setter %%array-setter)

(define (mutable-array? array)
  (and (array? array)
       (not (not (%%array-setter array)))))

(define (%%array-freeze! array)
  (%%array-setter-set! array #f)
  array)

(define-macro (make-standard-storage-classes)

  (define (symbol-concatenate . symbols)
    (string->symbol (apply string-append (map (lambda (s)
                                                (if (string? s)
                                                    s
                                                    (symbol->string s)))
                                              symbols))))

  `(begin
     ,@(map (lambda (name prefix default checker)
              (let ((name   (symbol-concatenate name '-storage-class))
                    (ref    (symbol-concatenate prefix '-ref))
                    (set!   (symbol-concatenate prefix '-set!))
                    (make   (symbol-concatenate 'make- prefix))
                    (copy!  (symbol-concatenate prefix '-copy!))
                    (length (symbol-concatenate prefix '-length))
                    (?      (symbol-concatenate prefix '?)))
                `(define ,name
                   (make-storage-class
                    ;; getter
                    (lambda (v i)
                      (,ref v i))
                    ;; setter
                    (lambda (v i val)
                      (,set! v i val))
                    ;; checker
                    ,checker           ;; already expanded
                    ;; maker
                    (lambda (n val)
                      (,make n val))
                    ;; copier
                    ,copy!             ;; complex call to memcopy, so don't expand
                    ;; length
                    (lambda (v)
                      (,length v))
                    ;; default
                    ,default
                    ;; data?
                    (lambda (data)
                      (,? data))
                    ;; data->body
                    (lambda (data)
                      (if (,? data)
                          data
                          (error ,(symbol->string
                                   (symbol-concatenate
                                    "Expecting a "
                                    prefix
                                    " passed to "
                                    "(storage-class-data->body "
                                    name
                                    "): "))
                                 data)))))))
            '(generic s8       u8       s16       u16       s32       u32       s64       u64       f32       f64       char)
            '(vector  s8vector u8vector s16vector u16vector s32vector u32vector s64vector u64vector f32vector f64vector string)
            '(0       0        0        0         0         0         0         0         0         0.0        0.0     #\null)
            `((lambda (x) #t)                        ; generic
              (lambda (x)                            ; s8
                (and (exact-integer? x)
                     (<= ,(- (expt 2 7))
                         x
                         ,(- (expt 2 7) 1))))
              (lambda (x)                            ; u8
                (and (exact-integer? x)
                     (<= 0
                         x
                         ,(- (expt 2 8) 1))))
              (lambda (x)                            ; s16
                (and (exact-integer? x)
                     (<= ,(- (expt 2 15))
                         x
                         ,(- (expt 2 15) 1))))
              (lambda (x)                            ; u16
                (and (exact-integer? x)
                     (<= 0
                         x
                         ,(- (expt 2 16) 1))))
              (lambda (x)                            ; s32
                (and (exact-integer? x)
                     (<= ,(- (expt 2 31))
                         x
                         ,(- (expt 2 31) 1))))
              (lambda (x)                            ; u32
                (and (exact-integer? x)
                     (<= 0
                         x
                         ,(- (expt 2 32) 1))))
              (lambda (x)                            ; s64
                (and (exact-integer? x)
                     (<= ,(- (expt 2 63))
                         x
                         ,(- (expt 2 63) 1))))
              (lambda (x)                            ; u64
                (and (exact-integer? x)
                     (<= 0
                         x
                         ,(- (expt 2 64) 1))))
              (lambda (x) (flonum? x))               ; f32
              (lambda (x) (flonum? x))               ; f64
              (lambda (x) (char? x))                 ; char
              ))))

(make-standard-storage-classes)

(define u1-storage-class
  (make-storage-class
   ;; getter
   (lambda (v i)
     (let ((index (fxarithmetic-shift-right i 4))
           (shift (fxand i 15))
           (bodyv (vector-ref v  1)))
       (fxand
        (fxarithmetic-shift-right
         (u16vector-ref bodyv index)
         shift)
        1)))
   ;; setter
   (lambda (v i val)
     (let ((index (fxarithmetic-shift-right i 4))
           (shift (fxand i 15))
           (bodyv (vector-ref v  1)))
       (u16vector-set! bodyv index (fxior (fxarithmetic-shift-left val shift)
                                          (fxand (u16vector-ref bodyv index)
                                                 (fxnot (fxarithmetic-shift-left 1 shift)))))))
   ;; checker
   (lambda (val)
     (and (fixnum? val)
          (eqv? 0 (fxand -2 val))))
   ;; maker
   (lambda (size initializer)
     (let ((u16-size (fxarithmetic-shift-right (+ size 15) 4)))
       (vector size (make-u16vector u16-size (if (eqv? 0 initializer) 0 65535)))))
   ;; no copier (for now)
   #f
   ;; length
   (lambda (v)
     (vector-ref v 0))
   ;; default
   0
   ;; data?
   (lambda (data)
     (u16vector? data))
   ;; data->body
   (lambda (data)
     (if (not (u16vector? data))
         (error "Expecting a u16vector passed to (storage-class-data->body u1-storage-class): " data)
         (vector (fx* 16 (u16vector-length data))
                 data)))))

(define-macro (make-complex-storage-classes)
  (define (symbol-concatenate . symbols)
    (string->symbol (apply string-append (map (lambda (s)
                                                (if (string? s)
                                                    s
                                                    (symbol->string s)))
                                              symbols))))
  (define construct
    (lambda (size)
      (let ((prefix (string-append "c" (number->string (fx* 2 size))))
            (floating-point-prefix (string-append "f" (number->string size))))
        `(define ,(symbol-concatenate prefix '-storage-class)
           (make-storage-class
            ;; getter
            (lambda (body i)
              (make-rectangular (,(symbol-concatenate floating-point-prefix 'vector-ref) body (fx* 2 i))
                                (,(symbol-concatenate floating-point-prefix 'vector-ref) body (fx+ (fx* 2 i) 1))))
            ;; setter
            (lambda (body i obj)
              (,(symbol-concatenate floating-point-prefix 'vector-set!) body (fx* 2 i)         (real-part obj))
              (,(symbol-concatenate floating-point-prefix 'vector-set!) body (fx+ (fx* 2 i) 1) (imag-part obj)))
            ;; checker
            (lambda (obj)
              (and (complex? obj)
                   (inexact? (real-part obj))
                   (inexact? (imag-part obj))))
            ;; maker
            (lambda (n val)
              (let ((l (fx* 2 n))
                    (re (real-part val))
                    (im (imag-part val)))
                (let ((result (,(symbol-concatenate 'make-
                                                    floating-point-prefix
                                                    'vector)
                               l)))
                  (do ((i 0 (+ i 2)))
                      ((= i l) result)
                    (,(symbol-concatenate floating-point-prefix 'vector-set!) result i re)
                    (,(symbol-concatenate floating-point-prefix 'vector-set!) result (fx+ i 1) im)))))
            ;; copier
            ,(symbol-concatenate prefix 'vector-copy!)
            ;; length
            (lambda (body)
              (fxquotient (,(symbol-concatenate floating-point-prefix 'vector-length) body) 2))
            ;; default
            0.+0.i
            ;; data?
            (lambda (data)
              (and (,(symbol-concatenate floating-point-prefix 'vector?) data)
                   (fxeven? (,(symbol-concatenate floating-point-prefix 'vector-length) data))))
            ;; data->body
            (lambda (data)
              (if (and (,(symbol-concatenate floating-point-prefix 'vector?) data)
                       (fxeven? (,(symbol-concatenate floating-point-prefix 'vector-length) data)))
                  data
                  (error ,(symbol->string
                           (symbol-concatenate
                            "Expecting a "
                            floating-point-prefix 'vector
                            " with an even number of elements passed to "
                            "(storage-class-data->body "
                            prefix '-storage-class
                            "): "))
                         data))))))))
  (let ((result
         `(begin
            ,@(map construct
                   '(32 64)))))
    result))

(define (c64vector-copy! to at from start end)
  (f32vector-copy! to (fx* 2 at) from (fx* 2 start) (fx* 2 end)))

(define (c128vector-copy! to at from start end)
  (f64vector-copy! to (fx* 2 at) from (fx* 2 start) (fx* 2 end)))

(make-complex-storage-classes)

(define-macro (macro-make-representation->double name mantissa-width exponent-width exponent-bias)

  (define (append-symbols . args)
    (string->symbol
     (apply string-append (map (lambda (arg)
                                 (cond ((symbol? arg) (symbol->string arg))
                                       ((number? arg) (number->string arg))
                                       ((string? arg) arg)
                                       (else
                                        (apply error "append-symbols: unknown argument: " arg))))
                               args))))

  (let* ((exponent-mask (- (fxarithmetic-shift-left 1 exponent-width) 1))
         (mantissa-mask (- (fxarithmetic-shift-left 1 mantissa-width) 1))
         (2^mantissa-width (fxarithmetic-shift-left 1 mantissa-width))
         (result
          `(define (,(append-symbols name '->double) x)
             (let ((e (fxand ,exponent-mask (fxarithmetic-shift-right x ,mantissa-width)))
                   (m (fxand ,mantissa-mask x))
                   (s (fxarithmetic-shift-right x ,(+ mantissa-width exponent-width))))
               (cond ((fx= e ,exponent-mask)
                      (if (fxzero? m)
                          (if (fxzero? s) +inf.0 -inf.0)
                          +nan.0))
                     ((fx> e 0)
                      (let* ((abs-numerator (fx+ ,2^mantissa-width m))
                             (numerator (if (fxzero? s) abs-numerator (fx- abs-numerator))))
                        (flscalbn (fl* (fixnum->flonum numerator) ,(fl/ (fixnum->flonum 2^mantissa-width))) (fx- e ,exponent-bias))))
                     ((fxzero? m)
                      (if (fxzero? s) +0. -0.))
                     (else
                      (let* ((abs-numerator m)
                             (numerator (if (fxzero? s) abs-numerator (fx- abs-numerator))))
                        (flscalbn (fl* (fixnum->flonum numerator) ,(fl/ (fixnum->flonum 2^mantissa-width))) ,(fx- 1 exponent-bias)))))))))
    ;; (pp result)
    result))

(define-macro (macro-make-double->representation name mantissa-width exponent-width exponent-bias)

  (define (append-symbols . args)
    (string->symbol
     (apply string-append (map (lambda (arg)
                                 (cond ((symbol? arg) (symbol->string arg))
                                       ((number? arg) (number->string arg))
                                       ((string? arg) arg)
                                       (else
                                        (apply error "append-symbols: unknown argument: " arg))))
                               args))))

  (let* ((exponent-mask (- (fxarithmetic-shift-left 1 exponent-width) 1))
         (mantissa-mask (- (fxarithmetic-shift-left 1 mantissa-width) 1))
         (2^mantissa-width (fxarithmetic-shift-left 1 mantissa-width))
         (result
          `(define (,(append-symbols 'double-> name) x)

             (declare (inline))

             (define (construct-representation sign-bit biased-exponent mantissa)
               (fxior (fxarithmetic-shift-left sign-bit ,(+ exponent-width mantissa-width))
                      (fxior (fxarithmetic-shift-left biased-exponent ,mantissa-width)
                             mantissa)))

             (let ((sign-bit
                    (if (flnegative? (##flcopysign 1. x)) 1 0)))
               (cond ((not (flfinite? x))
                      (if (flnan? x)
                          (construct-representation sign-bit ,exponent-mask ,mantissa-mask)
                          ;; an infinity
                          (construct-representation sign-bit ,exponent-mask 0)))
                     ((flzero? x)
                      ;; a zero
                      (construct-representation sign-bit 0 0))
                     (else
                      ;; finite
                      (let ((exponent (flilogb x)))
                        (cond ((fx<=  ,(- exponent-mask exponent-bias) exponent)
                               ;; infinity, because the exponent is too large
                               (construct-representation sign-bit ,exponent-mask 0))
                              ((fx< ,(fx- exponent-bias) exponent)
                               ;; probably normal, finite in representation, unless overflow
                               (let ((possible-mantissa
                                      (##flonum->fixnum (flround (flscalbn (flabs x) (fx- ,mantissa-width exponent))))))
                                 (if (fx< possible-mantissa ,(fx* 2 2^mantissa-width))
                                     ;; no overflow
                                     (construct-representation sign-bit
                                                               (fx+ exponent ,exponent-bias)
                                                               (fxand possible-mantissa ,mantissa-mask))
                                     ;; overflow
                                     (if (fx= exponent ,exponent-bias)
                                         ;; maximum finite exponent, overflow to infinity
                                         (construct-representation sign-bit ,exponent-mask 0)
                                         ;; increase exponent by 1, mantissa is zero, no double rounding
                                         (construct-representation sign-bit (fx+ exponent ,(fx+ exponent-bias 1)) 0)))))
                              (else
                               ;; usally subnormal
                               (let ((possible-mantissa
                                      (##flonum->fixnum (flround (flscalbn (flabs x) ,(fx+ exponent-bias mantissa-width -1))))))
                                 (if (fx< possible-mantissa ,2^mantissa-width)
                                     ;; doesn't overflow to normal
                                     (construct-representation sign-bit 0 possible-mantissa)
                                     ;; overflow to smallest normal
                                     (construct-representation sign-bit 1 0))))))))))))
    ;; (pp result)
    result))

(macro-make-representation->double f16 10 5 15)
(macro-make-double->representation f16 10 5 15)

(define f16-storage-class
  (make-storage-class
   ;; getter
   (lambda (body i)
     (f16->double (u16vector-ref body i)))
   ;; setter
   (lambda (body i obj)
     (u16vector-set! body i (double->f16 obj)))
   ;; checker
   (lambda (obj)
     (flonum? obj))
   ;; maker
   (lambda (n val)
     (make-u16vector n (double->f16 val)))
   ;; copier
   u16vector-copy!
   ;; length
   (lambda (body)
     (u16vector-length body))
   ;; default
   0.
   ;; data?
   (lambda (data)
     (u16vector? data))
   ;; data->body
   (lambda (data)
     (if (u16vector? data)
         data
         (error "Expecting a u16vector passed to (storage-class-data->body f16-storage-class): " data)))))

(define f8-storage-class #f)

(define (%%indexer base lowers increments)
  (lambda args
    (fold +
          base
          (map (lambda (arg lower increment)
                 (* increment (- arg lower)))
               args lowers increments))))

(define (specialized-array? object)
  (and (array? object)
       (not (not (%%array-body object)))))

(define array-body %%array-body)

(define array-indexer %%array-indexer)

(define array-storage-class %%array-storage-class)

(define (array-empty? array)
  (interval-empty? (array-domain array)))

(define (%%compute-multi-index-increments lowers uppers)
  ;; lowers and uppers are lists of lower and upper bounds
  ;; This function returns all lowers first, then a list of
  ;; multi-indices where one of the lowers is incremented
  ;; if possible while staying in the domain.  The list of
  ;; incremented multi-indices is ordered so that the
  ;; indices that are incremented are listed from left to
  ;; right
  (if (null? lowers)
      (list lowers)
      (let* ((temp (%%compute-multi-index-increments (cdr lowers) (cdr uppers)))
             (lower (car lowers))
             (upper (car uppers))
             (next-index (+ lower 1)))
        (cons (cons lower (car temp))
              (cons (cons (if (< next-index upper)
                              next-index
                              lower)
                          (car temp))
                    (map (lambda (multi-index)
                           (cons lower multi-index))
                         (cdr temp)))))))

(define (array-packed? array)
  (or (interval-empty? (array-domain array))
      (let* ((domain
              (array-domain array))
             (indexer
              (array-indexer array))
             (lowers
              (interval-lower-bounds->list domain))
             (uppers
              (interval-upper-bounds->list domain))
             (incremented-lowers
              (%%compute-multi-index-increments lowers uppers))
             (base
              (apply indexer lowers)))
        (and (let loop ((lowers lowers)
                        (uppers uppers)
                        (incremented-lowers (cdr incremented-lowers)))
               ;; returns either #f or the increment
               ;; that the difference of indexers must equal.
               (if (null? lowers)
                   1
                   (let ((increment (loop (cdr lowers)
                                          (cdr uppers)
                                          (cdr incremented-lowers))))
                     (and increment
                          (or (and (eqv? 1 (- (car uppers) (car lowers)))
                                   ;; increment doesn't change
                                   increment)
                              (and (= (- (apply indexer (car incremented-lowers))
                                         base)
                                      increment)
                                   ;; multiply the increment by the difference in
                                   ;; the current upper and lower bounds and
                                   ;; return it.
                                   (* increment (- (car uppers) (car lowers)))))))))
             ;; return a proper boolean instead of the volume of the domain
             #t))))

(define (%%interval->basic-indexer interval)
  (if (zero? (interval-dimension interval))
      ;; general code doesn't work for zero-dimensional intervals
      (%%indexer 0 '() '())
      (do ((widths
            (reverse (vector->list (interval-widths interval)))
            (cdr widths))
           (increments
            (list 1)
            (cons (* (car increments) (car widths))
                  increments)))
          ((null? (cdr widths))
           (%%indexer 0 (interval-lower-bounds->list interval) increments)))))

(define (%%finish-specialized-array domain storage-class body indexer mutable?)
  (let* ((storage-class-getter
          (storage-class-getter storage-class))
         (storage-class-setter
          (storage-class-setter storage-class))
         (checker
          (storage-class-checker storage-class))
         (getter
          (lambda args
            (storage-class-getter body (apply indexer args))))
         (setter
          (and mutable?
               (lambda (item . args)
                 (if (checker item)
                     (storage-class-setter body (apply indexer args) item)
                     (error "cannot store item in array body" item body))))))
    (make-%%array domain
                  getter
                  setter
                  storage-class
                  body
                  indexer)))
    
(define (%%make-specialized-array interval storage-class initial-value)
  (let* ((body
          ((storage-class-maker storage-class)
           (interval-volume interval)
           initial-value))
         (indexer
          (%%interval->basic-indexer interval)))
    (%%finish-specialized-array interval
                                storage-class
                                body
                                indexer
                                #t)))

(define make-specialized-array
  (case-lambda
   ((interval)
    (make-specialized-array interval generic-storage-class))
   ((interval storage-class)
    (make-specialized-array interval storage-class (storage-class-default storage-class)))
   ((interval storage-class initial-value)
    (%%make-specialized-array interval
                              storage-class
                              initial-value))))

(define make-specialized-array-from-data
  (case-lambda
   ((data)
    (make-specialized-array-from-data data generic-storage-class (specialized-array-default-mutable?)))
   ((data storage-class)
    (make-specialized-array-from-data data storage-class (specialized-array-default-mutable?)))
   ((data storage-class mutable?)
    (let* ((body
            ((storage-class-data->body storage-class) data))
           (indexer
            (lambda (i) i))
           (domain
            (make-interval (vector ((storage-class-length storage-class) body)))))
      (%%finish-specialized-array domain
                                  storage-class
                                  body
                                  indexer
                                  mutable?)))))

(define list->array
  (case-lambda
   ((interval l)
    (list->array interval l generic-storage-class (specialized-array-default-mutable?)))
   ((interval l storage-class)
    (list->array interval l storage-class (specialized-array-default-mutable?)))
   ((interval l storage-class mutable?)
    (let* ((checker (storage-class-checker storage-class))
           (setter  (storage-class-setter  storage-class))
           (result  (%%make-specialized-array interval
                                              storage-class
                                              (storage-class-default storage-class)))
           (body    (%%array-body result))
           (n       (interval-volume interval))
           (l        (list-copy l)))
      (let loop ((i 0)
                 (local l))
        (if (null? local)
            (if (not mutable?)
                (%%array-freeze! result)
                result)
            (let ((item (car local)))
              (if (checker item)
                  (begin
                    (setter body i item)
                    (loop (fx+ i 1)
                          (cdr local)))
                  (error "Not all elements of the source can be manipulated by the storage class: "
                         storage-class item)))))))))

(define (%%array->reversed-list array)
  (interval-fold-left (array-getter array)
                      (lambda (a b) (cons b a))
                      '()
                      (array-domain array)))

(define (array->list array)
  (reverse (%%array->reversed-list array)))

(define vector->array
  (case-lambda
   ((interval v)
    (vector->array interval v generic-storage-class (specialized-array-default-mutable?)))
   ((interval v storage-class)
    (vector->array interval v storage-class (specialized-array-default-mutable?)))
   ((interval v storage-class mutable?)
    (let* ((v       (vector-copy v))
           (n       (vector-length v))
           (body    ((storage-class-maker storage-class)
                     n
                     (storage-class-default storage-class)))
           (checker (storage-class-checker storage-class))
           (setter  (storage-class-setter storage-class)))
      (do ((i 0 (fx+ i 1)))
          ((fx= i n)
           (%%finish-specialized-array interval
                                       storage-class
                                       body
                                       (%%interval->basic-indexer interval)
                                       mutable?))
        (let ((item (vector-ref v i)))
          (if (checker item)
              (setter body i (vector-ref v i))
              (error "Not all elements of the source can be manipulated by the storage class: "
                     storage-class item))))))))

(define (array->vector array)
  (let* ((reversed-elements
          (%%array->reversed-list array))
         (n
          (interval-volume (array-domain array)))
         (result
          (make-vector n)))
    (do ((i (fx- n 1) (fx- i 1))
         (l reversed-elements (cdr l)))
        ((fx< i 0) result)
      (vector-set! result i (car l)))))

(define list*->array
  (case-lambda
   ((dimension nested-list)
    (list*->array dimension nested-list generic-storage-class (specialized-array-default-mutable?)))
   ((dimension nested-list storage-class)
    (list*->array dimension nested-list storage-class (specialized-array-default-mutable?)))
   ((dimension nested-list storage-class mutable?)
    
    (define (shape-error)
      (error "list*->array: The second argument is not the right shape to be converted to an array of the given dimension: "
             dimension nested-list))

    (define (flatten-nested-list dimension nested-list)
      (case dimension
        ((0) (list nested-list))
        ((1) (list-copy nested-list))
        (else (concatenate (map (lambda (l) (flatten-nested-list (fx- dimension 1) l)) nested-list)))))

    (define (check-nested-list dimension nested-list)
      (if (eqv? dimension 0)
          '()
          (and (list? nested-list)
               (let ((len (length nested-list)))
                 (cond ((eqv? len 0)
                        '())
                       ((eqv? dimension 1)
                        (list len))
                       (else
                        (let* ((sublists
                                (map (lambda (l)
                                       (check-nested-list (fx- dimension 1) l))
                                     nested-list))
                               (first
                                (car sublists)))
                          (and first
                               (every (lambda (l)
                                        (equal? first l))
                                      (cdr sublists))
                               (cons len first)))))))))

    (let ((list*-dimensions
           (check-nested-list dimension nested-list)))
      (if (not list*-dimensions)
          (shape-error)
          ;; list*-dimension is a (possibly empty) list of positive integers
          (list->array (make-interval
                        (list->vector
                         (append list*-dimensions
                                 (make-list (fx- dimension (length list*-dimensions)) 0))))
                       (flatten-nested-list dimension nested-list)
                       storage-class
                       mutable?))))))

(define object->array
  (case-lambda
   ((object)
    (object->array object generic-storage-class (specialized-array-default-mutable?)))
   ((object storage-class)
    (object->array object storage-class (specialized-array-default-mutable?)))
   ((object storage-class mutable?)
    (list*->array 0 object storage-class mutable?))))

(define (array->list* array)
  
  (define (a->l a)
    (let ((dim (interval-dimension (array-domain a))))
      (case dim
        ((0) ((array-getter a)))
        ((1) (array->list a))
        (else
         (array->list
          (array-map a->l (array-curry a (fx- dim 1))))))))
  
  (a->l array))

(define vector*->array
  (case-lambda
   ((dimension nested-vector)
    (vector*->array dimension
                    nested-vector
                    generic-storage-class
                    (specialized-array-default-mutable?)))
   ((dimension nested-vector storage-class)
    (vector*->array dimension
                    nested-vector
                    storage-class
                    (specialized-array-default-mutable?)))
   ((dimension nested-vector storage-class mutable?)
    
    (define (shape-error)
      (error "vector*->array: The second argument is not the right shape to be converted to an array of the given dimension: "
             dimension nested-vector))
    
    (define (flatten-nested-vector dimension nested-vector)
      (case dimension
        ((0) (vector nested-vector))
        ((1) (vector-copy nested-vector))
        (else (vector-concatenate (map (lambda (v)
                                         (flatten-nested-vector (fx- dimension 1) v))
                                       (vector->list nested-vector))))))
    
    (define (check-nested-vector dimension nested-vector)
      (if (eqv? dimension 0)
          '()
          (and (vector? nested-vector)
               (let ((len (vector-length nested-vector)))
                 (cond ((eqv? len 0)
                        '())
                       ((eqv? dimension 1)
                        (list len))
                       (else
                        (let* ((sublists
                                (vector-map (lambda (l)
                                              (check-nested-vector (fx- dimension 1) l))
                                            nested-vector))
                               (first
                                (vector-ref sublists 0)))
                          (and first
                               (vector-every (lambda (l)
                                               (equal? first l))
                                             sublists)
                               (cons len first)))))))))
    
    (let ((vector*-dimensions
           (check-nested-vector dimension nested-vector)))
      (if (not vector*-dimensions)
          (shape-error)
          ;; vector*-dimension is a (possibly empty) list of positive integers
          (vector->array (make-interval
                          (list->vector
                           (append vector*-dimensions
                                   (make-list (fx- dimension (length vector*-dimensions)) 0))))
                         (flatten-nested-vector dimension nested-vector)
                         storage-class
                         mutable?))))))

(define (array->vector* array)
  
  (define (a->v a)
    (let ((dim (interval-dimension (array-domain a))))
      (case dim
        ((0) ((array-getter a)))
        ((1) (array->vector a))
        (else
         (array->vector
          (array-map a->v (array-curry a (fx- dim 1))))))))
  
  (a->v array))

(define (array-assign! destination source)
  (let ((destination-setter
         (array-setter destination))
        (source-getter
         (array-getter source))
        (domain
         (array-domain source))
        ;; we have a checker, might as well use it.
        (checker
         (if (specialized-array? destination)
             (storage-class-checker (array-storage-class destination))
             (lambda (item) #t))))
    (interval-for-each (lambda args
                         (let ((item (apply source-getter args)))
                           (if (checker item)
                               (apply destination-setter
                                      (apply source-getter args)
                                      args)
                               (error "array-assign!: Can't store item into array: " item destination))))
                       domain)))

(define (%%generalized-array->specialized-array array storage-class mutable?)
  (let* ((domain            (array-domain array))
         (reversed-elements (%%array->reversed-list array))
         (n                 (interval-volume domain))
         (body              ((storage-class-maker storage-class) n (storage-class-default storage-class)))
         (indexer           (%%interval->basic-indexer domain))
         (setter            (storage-class-setter storage-class))
         (checker           (storage-class-checker storage-class)))
    (let loop ((i (fx- n 1))
                   (l reversed-elements))
          (if (fx<= 0 i)
              (if (checker (car l))
                  (begin
                    (setter body i (car l))
                    (loop (fx- i 1)
                          (cdr l)))
                  (error "Not all elements of the source can be stored in destination: " array storage-class mutable?))
              (%%finish-specialized-array domain
                                          storage-class
                                          body
                                          indexer
                                          mutable?)))))

(define (%%->specialized-array array storage-class)
  (if (specialized-array? array)
      array
      (%%generalized-array->specialized-array array storage-class #f)))

(define array-copy
  (case-lambda
   ((array)
    (if (specialized-array? array)
        (array-copy array (array-storage-class array) (mutable-array? array))
        (array-copy array generic-storage-class (specialized-array-default-mutable?))))
   ((array storage-class)
    (if (specialized-array? array)
        (array-copy array storage-class (mutable-array? array))
        (array-copy array storage-class (specialized-array-default-mutable?))))
   ((array storage-class mutable?)
    (if (specialized-array? array)
        (let ((result
               (%%make-specialized-array (%%array-domain array)
                                         storage-class
                                         (storage-class-default storage-class))))
          (array-assign! result array)
          (if (not mutable?)
              (%%array-freeze! result)
              result))
        (%%generalized-array->specialized-array array
                                                storage-class
                                                mutable?)))))

(define array-copy! array-copy)

(define (%%compose-indexers old-indexer new-domain new-domain->old-domain)
  (if (interval-empty? new-domain)
      (lambda args
        (error "%%compose-indexers: indexer on empty interval should never be called: "
               old-indexer new-domain new-domain->old-domain))
      (let* ((lowers
              (interval-lower-bounds->list new-domain))
             (uppers
              (interval-upper-bounds->list new-domain))
             (multi-indices
              (%%compute-multi-index-increments lowers uppers))
             (computed-offsets-for-multi-indices
              (map (lambda (multi-index)
                     (call-with-values
                         (lambda ()
                           (apply new-domain->old-domain multi-index))
                       old-indexer))
                   multi-indices))
             (base
              (car computed-offsets-for-multi-indices))
             (increments
              (map (lambda (v)
                     (- v base))
                   (cdr computed-offsets-for-multi-indices))))
        (%%indexer base lowers increments))))

(define (specialized-array-share array
                                 new-domain
                                 new-domain->old-domain)
  (let ((old-domain        (%%array-domain       array))
        (old-indexer       (%%array-indexer      array))
        (body              (%%array-body         array))
        (storage-class     (%%array-storage-class array)))
    (%%finish-specialized-array new-domain
                                storage-class
                                body
                                (%%compose-indexers old-indexer new-domain new-domain->old-domain)
                                (mutable-array? array))))

(define (array-extract array new-domain)
  (cond ((specialized-array? array)
         (specialized-array-share array new-domain values))
        ((mutable-array? array)
         (make-array new-domain
                     (array-getter array)
                     (array-setter array)))
        (else
         (make-array new-domain
                     (array-getter array)))))

(define (array-tile A slice-widths)

  (define (%%vector-fold-left op id v)
    (let ((n (vector-length v)))
      (do ((i 0 (fx+ i 1))
           (id id (op id (vector-ref v i))))
          ((fx= i n) id))))

  (let* ((A-dim  (array-dimension A))
         (domain (array-domain A))
         (lowers (%%interval-lower-bounds domain))
         (uppers (%%interval-upper-bounds domain))
         (widths (interval-widths domain))
         (offsets (make-vector A-dim)))
    (do ((k 0 (fx+ k 1)))
        ((fx= k A-dim))
      (let ((S_k (vector-ref slice-widths k)))
        (if (exact-integer? S_k)
            (let* ((width_k          (vector-ref widths k))
                   (number-of-slices (quotient (+ width_k (- S_k 1)) S_k))
                   (slice-offsets    (make-vector (+ number-of-slices 1))))
              (vector-set! slice-offsets 0 (vector-ref lowers k))
              (do ((i 0 (fx+ i 1)))
                  ((fx= i number-of-slices)
                   (vector-set! slice-offsets
                                number-of-slices
                                (min (vector-ref uppers k)
                                     (vector-ref slice-offsets number-of-slices)))
                   (vector-set! offsets k slice-offsets))
                (vector-set! slice-offsets
                             (fx+ i 1)
                             (+ (vector-ref slice-offsets i) S_k))))
            (let* ((number-of-slices (vector-length S_k))
                   (slice-offsets    (make-vector (+ number-of-slices 1))))
              (vector-set! slice-offsets 0 (vector-ref lowers k))
              (do ((i 0 (fx+ i 1)))
                  ((fx= i number-of-slices)
                   (vector-set! offsets k slice-offsets))
                (vector-set! slice-offsets
                             (fx+ i 1)
                             (+ (vector-ref slice-offsets i)
                                (vector-ref S_k i))))))))
    (let ((result-domain
           (make-interval (vector-map (lambda (v)
                                        (- (vector-length v) 1))
                                      offsets))))
      (make-array result-domain
                  (lambda i
                    (let* ((i
                            (list->vector i))
                           (subdomain
                            (make-interval (vector-map (lambda (slice-offsets i) (vector-ref slice-offsets i)) offsets i)
                                           (vector-map (lambda (slice-offsets i) (vector-ref slice-offsets (fx+ i 1))) offsets i))))
                      (array-extract A subdomain)))))))
    

(define (array-translate array translation)

  (define (getter-translate getter translatio)
    (let ((translation-list (vector->list translation)))
      (lambda multi-index
        (apply getter (map - multi-index translation-list)))))
  
  (define (setter-translate setter translation)
    (let ((translation-list (vector->list translation)))
      (lambda (v . multi-index)
        (apply setter v (map - multi-index translation-list)))))
  
  (cond ((specialized-array? array)
         (specialized-array-share array
                                  (interval-translate (array-domain array) translation)
                                  (getter-translate values translation)))
        ((mutable-array? array)
         (make-array (interval-translate (array-domain array) translation)
                     (getter-translate (array-getter array) translation)
                     (setter-translate (array-setter array) translation)))
        (else
         (make-array (interval-translate (array-domain array) translation)
                     (getter-translate (array-getter array) translation)))))

(define array-rebase
  (case-lambda
   ((array)
    (array-rebase array (make-vector (array-dimension array) 0)))
   ((array new-lower-bounds)
    (array-translate
     array
     (vector-map - new-lower-bounds (%%interval-lower-bounds (array-domain array)))))))

(define (array-permute array permutation)

  (define (getter-permute getter permutation)
    (let ((permutation-inverse (%%permutation-invert permutation)))
      (lambda indices
        (apply getter (%%vector-permute->list (list->vector indices) permutation-inverse)))))
  
  (define (setter-permute setter permutation)
    (let ((permutation-inverse (%%permutation-invert permutation)))
      (lambda (v . indices)
        (apply setter v (%%vector-permute->list (list->vector indices) permutation-inverse)))))

  (cond ((specialized-array? array)
         (specialized-array-share array
                                  (interval-permute (array-domain array) permutation)
                                  (getter-permute values permutation)))
        ((mutable-array? array)
         (make-array (interval-permute (array-domain array) permutation)
                     (getter-permute (array-getter array) permutation)
                     (setter-permute (array-setter array) permutation)))
        (else
         (make-array (interval-permute (array-domain array) permutation)
                     (getter-permute (array-getter array) permutation)))))

(define array-reverse
  (case-lambda
   ((array)
    (array-reverse array (make-vector (array-dimension array) #t)))
   ((array flip?)
    
    (define (getter-reverse getter flip? interval)
      (let* ((flip?
              (vector->list flip?))
             (adjustment
              (map (lambda (u_k l_k)
                     (+ u_k l_k -1))
                   (interval-upper-bounds->list interval)
                   (interval-lower-bounds->list interval))))
        (lambda indices
          (apply getter (map (lambda (i adjustment flip?)
                               (if flip?
                                   (- adjustment i)
                                   i))
                             indices adjustment flip?)))))
    
    (define (setter-reverse setter flip? interval)
      (let* ((flip?
              (vector->list flip?))
             (adjustment
              (map (lambda (u_k l_k)
                     (+ u_k l_k -1))
                   (interval-upper-bounds->list interval)
                   (interval-lower-bounds->list interval))))
        (lambda (v . indices)
          (apply setter v (map (lambda (i adjustment flip?)
                                 (if flip?
                                     (- adjustment i)
                                     i))
                               indices adjustment flip?)))))
    
    (cond ((specialized-array? array)
           (specialized-array-share array
                                    (array-domain array)
                                    (getter-reverse values flip? (array-domain array))))
        ((mutable-array? array)
         (make-array (array-domain array)
                     (getter-reverse (array-getter array) flip? (array-domain array))
                     (setter-reverse (array-setter array) flip? (array-domain array))))
        (else
         (make-array (array-domain array)
                     (getter-reverse (array-getter array) flip? (array-domain array))))))))

(define (array-sample array scales)

  (define (getter-sample getter scales)
    (let ((scales (vector->list scales)))
      (lambda indices
        (apply getter (map * indices scales)))))

  (define (setter-sample setter scales)
    (let ((scales (vector->list scales)))
      (lambda (v . indices)
        (apply setter v (map * indices scales)))))

  (cond ((specialized-array? array)
         (specialized-array-share array
                                  (interval-scale (array-domain array) scales)
                                  (getter-sample values scales)))
        ((mutable-array? array)
         (make-array (interval-scale (array-domain array) scales)
                     (getter-sample (array-getter array) scales)
                     (setter-sample (array-setter array) scales)))
        (else
         (make-array (interval-scale (array-domain array) scales)
                     (getter-sample (array-getter array) scales)))))

(define array-insert-axis
  (case-lambda
   ((array k)
    (array-insert-axis array k 1))
   ((array k u_k)

    (define (getter-delete getter k)
      (lambda indices
        (apply getter (append (take indices k) (drop indices (+ k 1))))))

    (define (setter-delete setter k)
      (lambda (v . indices)
        (apply setter v (append (take indices k) (drop indices (+ k 1))))))

    (let ((new-domain (interval-insert-axis (array-domain array) k u_k)))
      (cond ((specialized-array? array)
             (specialized-array-share array
                                      new-domain
                                      (getter-delete values k)))
            ((mutable-array? array)
             (make-array new-domain
                         (getter-delete (array-getter array) k)
                         (setter-delete (array-setter array) k)))
            (else
             (make-array new-domain
                         (getter-delete (array-getter array) k))))))))

(define (array-curry array right-dimension)
  (call-with-values
      (lambda ()
        (interval-projections (array-domain array) right-dimension))
    (lambda (left-interval right-interval)
      (let ((getter (array-getter array))
            (setter (array-setter array)))
        (cond ((specialized-array? array)
               (make-array left-interval
                           (lambda left-multi-index
                             (specialized-array-share array
                                                      right-interval
                                                      (lambda right-multi-index
                                                        (apply values
                                                               (append left-multi-index
                                                                       right-multi-index)))))))
              ((mutable-array? array)
               (make-array left-interval
                           (lambda left-multi-index
                             (make-array right-interval
                                         (lambda right-multi-index
                                           (apply getter (append left-multi-index right-multi-index)))
                                         (lambda (v . right-multi-index)
                                           (apply setter v (append left-multi-index right-multi-index)))))))
              (else
               (make-array left-interval
                           (lambda left-multi-index
                             (make-array right-interval
                                         (lambda right-multi-index
                                           (apply getter (append left-multi-index right-multi-index))))))))))))


(define (%%specialize-function-applied-to-array-getters f array arrays)
  (let ((getters (map array-getter (cons array arrays))))
    (lambda multi-index
      (apply f (map (lambda (g) (apply g multi-index)) getters)))))

(define (array-map f array . arrays)
  (make-array (array-domain array)
              (%%specialize-function-applied-to-array-getters f array arrays)))

(define (array-for-each f array . arrays)
  (interval-for-each (%%specialize-function-applied-to-array-getters f array arrays)
                     (array-domain array)))

(define (%%interval-every f interval)
  (or (eqv? (interval-volume interval) 0)
      (let ((reversed-lowers (reverse (interval-lower-bounds->list interval)))
            (reversed-uppers (reverse (interval-upper-bounds->list interval))))
        (let loop ((reversed-args reversed-lowers)
                   (index (- (interval-volume interval) 1)))
          (if (eqv? index 0)
              (apply f (reverse reversed-args))
              (and (apply f (reverse reversed-args))
                   (loop (%%get-next-args reversed-args
                                          reversed-lowers
                                          reversed-uppers)
                         (- index 1))))))))

(define (%%interval-any f interval)
  (and (not (eqv? (interval-volume interval) 0))
      (let ((reversed-lowers (reverse (interval-lower-bounds->list interval)))
            (reversed-uppers (reverse (interval-upper-bounds->list interval))))
        (let loop ((reversed-args reversed-lowers)
                   (index (- (interval-volume interval) 1)))
          (if (eqv? index 0)
              (apply f (reverse reversed-args))
              (or (apply f (reverse reversed-args))
                  (loop (%%get-next-args reversed-args
                                         reversed-lowers
                                         reversed-uppers)
                        (- index 1))))))))

(define (array-every f array . arrays)
  (%%interval-every (%%specialize-function-applied-to-array-getters f array arrays)
                    (array-domain array)))

(define (array-any f array . arrays)
  (%%interval-any (%%specialize-function-applied-to-array-getters f array arrays)
                  (array-domain array)))

(define (array-fold-left op left-id array . arrays)
  (interval-fold-left (array-getter (apply array-map list array arrays))
                      (lambda (id elements)
                        (apply op id elements))
                      left-id
                      (array-domain array)))

(define (array-fold-right op right-id array . arrays)
  (interval-fold-right (array-getter (apply array-map list array arrays))
                       (lambda (elements id)
                         (apply op (append elements (list id))))
                       right-id
                       (array-domain array)))

(define array-reduce
  (let ((%%array-reduce-base (list 'base)))
    (lambda (sum A)
      (interval-fold-left (array-getter A)
                          (lambda (id a)
                            (if (eq? id %%array-reduce-base)
                                a
                                (sum id a)))
                          %%array-reduce-base
                          (array-domain A)))))

(define (array-inner-product A f g B)
  (array-outer-product
   (lambda (a b)
     (array-reduce f (array-map g a b)))
   (array-copy (array-curry A 1))
   (array-copy (array-curry (array-permute B (index-rotate (array-dimension B) 1)) 1))))

(define (array-outer-product combiner A B)
  (let* ((D_A            (array-domain A))
         (D_B            (array-domain B))
         (A_             (array-getter A))
         (B_             (array-getter B))
         (dim_A          (interval-dimension D_A))
         (result-domain  (interval-cartesian-product D_A D_B))
         (result-getter
          (lambda args
            (combiner (apply A_ (take args dim_A))
                      (apply B_ (drop args dim_A))))))
    (make-array result-domain result-getter)))

(define array-stack
  (case-lambda
   ((k arrays)
    (array-stack k arrays generic-storage-class (specialized-array-default-mutable?)))
   ((k arrays storage-class)
    (array-stack k arrays storage-class (specialized-array-default-mutable?)))
   ((k arrays storage-class mutable?)
    (let* ((arrays
            (list-copy arrays))
           (arrays
            (map (lambda (A)
                   (%%->specialized-array A storage-class))
                 arrays))
           (number-of-arrays
            (length arrays))
           (domain
            (array-domain (car arrays)))
           (result-domain
            (interval-insert-axis domain k number-of-arrays))
           (result-array
            (%%make-specialized-array result-domain
                                      storage-class
                                      (storage-class-default storage-class)))
           (permuted-and-curried-result
            (array-curry (array-permute result-array (index-first (interval-dimension result-domain) k))
                         (interval-dimension domain))))
      (array-for-each array-assign!
                      permuted-and-curried-result
                      (list->array (make-interval (vector number-of-arrays))
                                   arrays
                                   generic-storage-class
                                   #f))
      (if (not mutable?)
          (%%array-freeze! result-array)
          result-array)))))

(define array-stack! array-stack)

(define array-decurry
  (case-lambda
   ((A)
    (array-decurry A generic-storage-class (specialized-array-default-mutable?)))
   ((A storage-class)
    (array-decurry A storage-class (specialized-array-default-mutable?)))
   ((A storage-class mutable?)
    (let* ((A
            (%%->specialized-array (array-map (lambda (A)
                                                (%%->specialized-array A storage-class))
                                              A)
                                   generic-storage-class))
           (A_
            (array-getter A))
           (A_D
            (array-domain A))
           (first-domain
            (array-domain (apply A_ (interval-lower-bounds->list A_D))))
           (result-domain
            (interval-cartesian-product A_D first-domain))
           (result
            (%%make-specialized-array result-domain
                                      storage-class
                                      (storage-class-default storage-class)))
           (curried-result
            (array-curry result (interval-dimension first-domain))))
      (array-for-each array-assign! curried-result A)
      (if (not mutable?)
          (%%array-freeze! result)
          result)))))

(define array-decurry! array-decurry)

(define array-append
  (case-lambda
   ((k arrays)
    (array-append k arrays generic-storage-class (specialized-array-default-mutable?)))
   ((k arrays storage-class)
    (array-append k arrays storage-class (specialized-array-default-mutable?)))
   ((k arrays storage-class mutable?)
    (call-with-values
        (lambda ()
          (let loop ((result '(0))
                     (arrays arrays))
            (if (null? arrays)
                (values (reverse result) (car result))
                (let ((interval (array-domain (car arrays))))
                  (loop (cons (fx+ (car result)
                                   (- (interval-upper-bound interval k)
                                      (interval-lower-bound interval k)))
                              result)
                        (cdr arrays))))))
      (lambda (axis-subdividers kth-size)
        #;(pp (list array-append: axis-subdividers kth-size))
        (let* ((arrays
                (list-copy arrays))
               (arrays
                (map (lambda (A)
                       (%%->specialized-array A storage-class))
                     arrays))
               (first-array
                (car arrays))
               (lowers
                ;; the domains of the arrays differ only in the kth axis
                (interval-lower-bounds->vector (array-domain first-array)))
               (uppers
                (interval-upper-bounds->vector (array-domain first-array)))
               (result
                ;; the result array
                (%%make-specialized-array
                 (let ()
                   (vector-set! lowers k 0)
                   (vector-set! uppers k kth-size)
                   (make-interval lowers uppers))  ;; copies lowers and uppers
                 storage-class
                 (storage-class-default storage-class))))
          #;(pp (array-domain result))
          (let loop ((arrays arrays)
                     (subdividers axis-subdividers))
            (if (null? arrays)
                ;; we've assigned every array to the appropriate subarray of result
                (if (not mutable?)
                    (%%array-freeze! result)
                    result)
                (let ((array (car arrays)))
                  (vector-set! lowers k (car subdividers))
                  (vector-set! uppers k (cadr subdividers))
                  (array-assign!
                   (array-extract result (make-interval lowers uppers))
                   (array-rebase array lowers))
                  (loop (cdr arrays)
                        (cdr subdividers)))))))))))

(define array-append! array-append)

(define array-block
  (case-lambda
   ((A)
    (array-block A generic-storage-class (specialized-array-default-mutable?)))
   ((A storage-class)
    (array-block A storage-class (specialized-array-default-mutable?)))
   ((A storage-class mutable?)
    (let* ((A       (array-rebase (array-copy A)))  ;; evaluate all elements of A, and make lower bounds zero
           (A_D     (array-domain A))
           (A_dim   (interval-dimension A_D))
           (ks      (list->vector (iota A_dim)))
           (slice-offsets       ;; the indices in each direction where the "cuts" are
            (vector-map
             (lambda (k)        ;; the direction
               (let* ((pencil   ;; a pencil in that direction
                       ;; Amazingly, this works when A_dim is 1.
                       (apply (array-getter (array-curry (array-permute A (index-last A_dim k)) 1))
                              (make-list (fx- A_dim 1) 0)))
                      (pencil_
                       (array-getter pencil))
                      (pencil-size
                       (interval-width (array-domain pencil) 0))
                      (result   ;; include sum of all kth interval-widths in pencil
                       (make-vector (fx+ pencil-size 1) 0)))
                 (do ((i 0 (fx+ i 1)))
                     ((fx= i pencil-size) result)
                   (vector-set! result
                                (fx+ i 1)
                                (fx+ (vector-ref result i)
                                     (interval-width (array-domain (pencil_ i)) k))))))
             ks))
           (A
            (%%->specialized-array (array-map (lambda (A)
                                                (%%->specialized-array A storage-class))
                                              A)
                                   generic-storage-class))
           (A_
            (array-getter A))
           (result
            (%%make-specialized-array
             (make-interval
              (vector-map (lambda (v)
                            (vector-ref v (fx- (vector-length v) 1)))
                          slice-offsets))
             storage-class
             (storage-class-default storage-class))))
      (interval-for-each
       (lambda multi-index
         (let* ((vector-multi-index
                 (list->vector multi-index))
                (corner     ;; where the subarray will sit in the result array
                 (vector-map (lambda (i k)
                               (vector-ref (vector-ref slice-offsets k) i))
                             vector-multi-index
                             ks))
                (subarray
                 (apply A_ multi-index))
                (rebased-subarray  ;; rebase the subarray to corner
                 (array-rebase subarray corner)))
           (array-assign! (array-extract result (array-domain rebased-subarray))
                          rebased-subarray)))
       A_D)
      (if (not mutable?)
          (%%array-freeze! result)
          result)))))

(define array-block! array-block)

(define (array-ref A . multi-index)
  (apply (array-getter A) multi-index))

(define (array-set! A v . multi-index)
  (apply (array-setter A) v multi-index))

(define specialized-array-reshape
  (case-lambda
   ((array new-domain)
    (specialized-array-reshape array new-domain #f))
   ((array new-domain copy-on-failure?)

    (define (vector-filter p v)
      (let ((n (vector-length v)))
        (define (helper k i)
          (cond ((fx= k n)
                 (make-vector i))
                ((p k)
                 (let ((result (helper (fx+ k 1) (fx+ i 1))))
                   (vector-set! result i (vector-ref v k))
                   result))
                (else
                 (helper (fx+ k 1) i))))
        (helper 0 0)))

    (let* ((indexer
            (array-indexer array))
           (domain
            (array-domain array))
           (lowers
            (%%interval-lower-bounds domain))
           (uppers
            (%%interval-upper-bounds domain))
           (dims
            (vector-length lowers))
           (sides
            (vector-map (lambda (u l) (- u l)) uppers lowers))
           (lowers
            (interval-lower-bounds->list domain))
           (uppers
            (interval-upper-bounds->list domain))
           (incremented-lowers
            (%%compute-multi-index-increments lowers uppers))
           (base
            (apply indexer (car incremented-lowers)))
           (strides
            (list->vector (map (lambda (args)
                                 (fx- (apply indexer args) base))
                               (cdr incremented-lowers))))
           (filtered-strides
            (vector-filter (lambda (i)
                             (not (eqv? 1 (vector-ref sides i))))
                           strides))
           (filtered-sides
            (vector-filter (lambda (i)
                             (not (eqv? 1 (vector-ref sides i))))
                           sides))
           (new-sides
            (vector-map (lambda (u l) (- u l))
                        (%%interval-upper-bounds new-domain)
                        (%%interval-lower-bounds new-domain)))
           ;; Notation from the NumPy code
           (newdims
            new-sides)
           (olddims
            filtered-sides)
           (oldstrides
            filtered-strides)
           (newnd
            (vector-length new-sides))
           (newstrides
            (make-vector newnd 0))
           (oldnd
            (vector-length filtered-sides)))
      ;; In the following loops, the error call is in tail position
      ;; so it can be continued.
      ;; From this point on we're going to closely follow NumPy's code
      (let loop-1 ((oi 0)
                   (oj 1)
                   (ni 0)
                   (nj 1))
        (if (and (fx< ni newnd)
                 (fx< oi oldnd))
            ;; We find a minimal group of adjacent dimensions from left to right
            ;; on the old and new intervals with the same volume.
            ;; We then check to see that the elements in the old array of these
            ;; dimensions are evenly spaced, so an affine map can
            ;; cover them.
            (let loop-2 ((nj nj)
                         (oj oj)
                         (np (vector-ref newdims ni))
                         (op (vector-ref olddims oi)))
              (if (not (fx= np op))
                  (if (fx< np op)
                      (loop-2 (fx+ nj 1)
                              oj
                              (fx* np (vector-ref newdims nj))
                              op)
                      (loop-2 nj
                              (fx+ oj 1)
                              np
                              (fx* op (vector-ref olddims oj))))
                  (let loop-3 ((ok oi))
                    (if (fx< ok (fx- oj 1))
                        (if (not (fx= (vector-ref oldstrides ok)
                                      (fx* (vector-ref olddims    (fx+ ok 1))
                                           (vector-ref oldstrides (fx+ ok 1)))))
                            (if copy-on-failure?
                                (specialized-array-reshape
                                 (array-copy array)
                                 new-domain
                                 #f)
                                (error "specialized-array-reshape: Requested reshaping is impossible: " array new-domain))
                            (loop-3 (fx+ ok 1)))
                        (begin
                          (vector-set! newstrides (fx- nj 1) (vector-ref oldstrides (fx- oj 1)))
                          (let loop-4 ((nk (fx- nj 1)))
                            (if (fx< ni nk)
                                (begin
                                  (vector-set! newstrides (fx- nk 1) (fx* (vector-ref newstrides nk)
                                                                          (vector-ref newdims nk)))
                                  (loop-4 (fx- nk 1)))
                                (loop-1 oj
                                        (fx+ oj 1)
                                        nj
                                        (fx+ nj 1)))))))))
            ;; The NumPy code then sets the strides of the last
            ;; dimensions with side-length 1 to a value, we leave it zero.
            (%%finish-specialized-array new-domain
                                        (array-storage-class array)
                                        (array-body array)
                                        (%%indexer base
                                                   (vector->list (%%interval-lower-bounds new-domain))
                                                   (vector->list newstrides))
                                        (mutable-array? array))))))))