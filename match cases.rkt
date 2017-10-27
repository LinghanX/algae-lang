#lang racket

(define sample "{bind {{x 1} {y 2}} {+ x y}}")

(match sample
  [(list 'bind (list some ...) body)
       ('bind some body)]
       [else (error 'parse-sexpr "bad `bind' syntax in ~s" sample)])