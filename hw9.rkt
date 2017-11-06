#lang pl 09

(define (Y f)
  ((lambda (x) (x x))
   (lambda (x) (f (lambda (z) ((x x) z))))))

;(define ackermann
;  (Y (lambda (ackermann)
;       (lambda (m n)
;         (cond [(zero? m) (+ n 1)]
;               [(zero? n) (ackermann (- m 1) 1)]
;               [else      (ackermann (- m 1)
;                                     (ackermann m (- n 1)))])))))

;(define ackermann
;  (let ([g (Y (lambda (ackermann)
;                (lambda (_) ; we ignore this argument
;                  (lambda (m n)
;                    (let ([ackermann (ackermann #f)])
;                      (lambda (m n)
;                        (cond [(zero? m) (+ n 1)]
;                              [(zero? n) (ackermann (- m 1) 1)]
;                              [else      (ackermann (- m 1)
;                                                    (ackermann m (- n 1)))])))))))])
;    (g #f)))

(rewrite (define/rec (f x ...) body)
         => (define f
              (let ([g (Y (lambda (f)
                            (lambda (_)
                              (lambda (x ...)
                                (let ([f (f #f)])
                                  body)))))])
                (g #f))))

(define/rec (ackermann m n)
  (cond [(zero? m) (+ n 1)]
        [(zero? n) (ackermann (- m 1) 1)]
        [else      (ackermann (- m 1) (ackermann m (- n 1)))]))
(test (ackermann 3 3) => 61)