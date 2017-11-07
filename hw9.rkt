#lang pl 09

(define (Y f)
  ((lambda (x) (x x))
   (lambda (x) (f (lambda (z) ((x x) z))))))

; rewrite define/rec uses Y combinator to enable recursive definition
; of a function
(rewrite (define/rec (f x ...) body)
         => (define f
              (let ([g (Y (lambda (f)
                            (lambda (_)
                              (lambda (x ...)
                                (let ([f (f #f)]) body)))))])
                (g #f))))

; (: ackermann : Natural Natural -> Natural )
; Given two natural numbers m and n, returns the
; computational result of the two-argument Ackermann function
(define/rec (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1) (ackermann m (- n 1)))]))

; (: fib : Natural -> Natural)
; Given a natural number, return the n-th fibonacci number
(define/rec (fib n)
  (cond
    ((= 1 n) 1)
    ((= 2 n) 1)
    (else (+ (fib (- n 1)) (fib (- n 2))))))

; rewrite letfuns uses Y combinator to enable definition of
; mutual recursive functions
(rewrite (letfuns ([(f x ...) E] ...) B)
         => (let ([g (Y (lambda (funs)
                          (lambda (name)
                            (match name
                              ['f (lambda (x ...)
                                    (let ((f (funs 'f)) ...) E))] ...))))])
              (let ([f (g 'f)] ...)
                B)))



;; test define/rec
(test (ackermann 3 3) => 61)
(test (fib 5) => 5)

;; test letfuns
(test (letfuns ([(even? n) (if (= n 0) #t (odd?  (- n 1)))]
                [(odd?  n) (if (= n 0) #f (even? (- n 1)))])
               (or (even? 123) (odd? 120) (even? 120))))
;; an extended example
(define scan
  (letfuns ([(start str)  (loop (explode-string str) 0)]
            [(loop l n)   (match l
                            [(list)
                             (zero? n)]
                            [(cons 'open more)
                             (loop more (add1 n))]
                            [(cons 'close more)
                             (and (> n 0) (loop more (sub1 n)))]
                            [(cons (number: m) more)
                             (nums more m n)]
                            [(cons _ more)
                             (loop more n)])]
            [(nums l m n) (match l
                            [(cons (number: m1) more)
                             (and (< m m1) (nums more m1 n))]
                            [else (loop l n)])])
           start))
(test (scan "(()123(246x12)) (blah)"))
(test (not (scan "(1232)")))
(test (not (scan "()(")))
(test (not (scan "())")))

(define minutes-spent 230)