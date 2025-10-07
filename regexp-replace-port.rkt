#lang racket
(provide regexp-replace-port)

;; (regexp-replace-port in from to) -> input-port?
;;   in   : input-port?
;;   from : (or/c regexp? pregexp? string? bytes?)  ; anything accepted by regexp-replace*
;;   to   : (or/c string? bytes? procedure?)        ; same as regexp-replace*
;;
;; Returns a fresh input port that, when read, yields the content of `in`
;; with every line transformed by (regexp-replace* from to).
;;
;; Notes:
;;  * Reads the underlying port as text (lines), encodes UTF-8 for bytes.
;;  * Preserves original line structure. If the final line has no terminator,
;;    none is added.
(define (regexp-replace-port in from to)
  (define buf #"" )         ; current byte buffer to serve reads from
  (define buf-i 0)          ; next unread index into buf
  (define eof? #f)          ; have we reached EOF on `in`?

  ;; Pull the next line from `in`, transform it, and stash UTF-8 bytes in buf.
  (define (refill!)
    (cond
      [eof? (set! buf #"") (set! buf-i 0) 'eof]
      [else
       (define line (read-line in 'any))       ; returns string or eof
       (cond
         [(eof-object? line)
          (set! eof? #t)
          (set! buf #"")
          (set! buf-i 0)
          'eof]
         [else
          ;; Did we just read a line terminator? `read-line` drops it,
          ;; so we re-add exactly one "\n" to preserve line structure.
          ;; (If the original file used CRLF, Racket’s text decoding
          ;; normalizes to a single newline in text mode.)
          (define replaced (regexp-replace* from line to))
          (define b (string->bytes/utf-8 (string-append replaced "\n")))
          (set! buf b)
          (set! buf-i 0)
          'ok])]))

  ;; Core read function for make-input-port: fill `dst` with available bytes.
  (define (read-into! dst-bytes)
    (let loop ()
      (define remaining (- (bytes-length buf) buf-i))
      (cond
        [(positive? remaining)
         (define n (min (bytes-length dst-bytes) remaining))
         (bytes-copy! dst-bytes 0 buf buf-i (+ buf-i n))
         (set! buf-i (+ buf-i n))
         n]
        [else
         (case (refill!)
           [(ok) (loop)]
           [(eof) eof])])))

  ;; Create the custom input port. We let Racket handle peeking automatically.
  (make-input-port
   'regexp-replace-port
   read-into!
   #f
   (lambda () (close-input-port in))))

;; --- tiny demo ---
(module+ test
  (define src (open-input-string "abXab\nXabX\nlastX"))
  (define p   (regexp-replace-port src #rx"ab" "CD"))
  (display (port->string p))
  ;; => "CDXCD\nXCDX\nlastX"
  )
