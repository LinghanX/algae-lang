#lang pl 07

(define-type BRANG
  [Num  Number]
  [Add  BRANG BRANG]
  [Sub  BRANG BRANG]
  [Mul  BRANG BRANG]
  [Div  BRANG BRANG]
  [Id   Symbol]
  [With Symbol BRANG BRANG]
  [Bind (Listof Symbol) (Listof BRANG) BRANG]
  [Bind* (Listof BRANG) (Listof BRANG)]
  [Fun  (Listof Symbol) BRANG]
  [Call BRANG (Listof BRANG)])

(: parse-sexpr : Sexpr -> BRANG)
;; parses s-expressions into BRANGs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(symbol: name) (Id name)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: names) ...) body)
        (if (null? names)
          (error 'parse-sexpr "`fun' with no arguments in ~s" sexpr)
          (Fun names (parse-sexpr body)))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(cons 'bind more)
     (match sexpr
       [(list 'bind (list (list (symbol: ids) (sexpr: exprs)) ...) body)
       (Bind ids (map parse-sexpr exprs) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `bind' syntax in ~s" sexpr)])]
    [(cons 'bind* more)
     (match sexpr
       [(list 'bind (list (symbol: pairs) ...) body)
       (Bind* pairs (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `bind*' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(cons 'call more)
     (match sexpr
       [(list 'call fun arg args ...)
        (Call (parse-sexpr fun) (map parse-sexpr (cons arg args)))]
       [else (error 'parse-sexpr "missing arguments to `call' in ~s"
                    sexpr)])]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(parse "{bind {{x 1} {y 2}} {+ x y}}")