#lang pl 04

#| BNF for the ALGAE language:
     <ALGAE> ::= <num>
               | True
               | False
               | { +  <ALGAE> ... }
               | { *  <ALGAE> ... }
               | { -  <ALGAE> <ALGAE> ... }
               | { /  <ALGAE> <ALGAE> ... }
               | { <  <ALGAE> <ALGAE>}
               | { =  <ALGAE> <ALGAE>}
               | { <= <ALGAE> <ALGAE>}
               | { with { <id> <ALGAE> } <ALGAE> }
               | <id>
               | { if <ALGAE> <ALGAE> <ALGAE> }
               | { not <ALGAE> }
               | { and <ALGAE> <ALGAE> }
               | { or <ALGAE> <ALGAE> }
|#

;; ALGAE abstract syntax trees
(define-type ALGAE
  [Num  Number]
  [Bool Boolean]
  [Add  (Listof ALGAE)]
  [Mul  (Listof ALGAE)]
  [Sub  ALGAE (Listof ALGAE)]
  [Div  ALGAE (Listof ALGAE)]
  [Id   Symbol]
  [Less ALGAE ALGAE]
  [Equal ALGAE ALGAE]
  [LessEq ALGAE ALGAE]
  [With Symbol ALGAE ALGAE]
  [If ALGAE ALGAE ALGAE])

(: parse-sexpr : Sexpr -> ALGAE)
;; parses s-expressions into ALGAEs
(define (parse-sexpr sexpr)
  ;; utility for parsing a list of expressions
  (: parse-sexprs : (Listof Sexpr) -> (Listof ALGAE))
  (define (parse-sexprs sexprs) (map parse-sexpr sexprs))
  (match sexpr
    [(number: n)    (Num n)]
    ['True (Bool #t)]
    ['False (Bool #f)]
    [(symbol: id) (Id id)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'if more)
     (match sexpr
       [(list 'if condition true-part false-part)
        (If (parse-sexpr condition)
            (parse-sexpr true-part)
            (parse-sexpr false-part))]
       [else (error 'parse-sexpr "bad `if' syntax in ~s" sexpr)])]
    [(list '+ args ...)     (Add (parse-sexprs args))]
    [(list '* args ...)     (Mul (parse-sexprs args))]
    [(list '- fst args ...) (Sub (parse-sexpr fst) (parse-sexprs args))]
    [(list '/ fst args ...) (Div (parse-sexpr fst) (parse-sexprs args))]
    [(list '< fst second)   (Less (parse-sexpr fst) (parse-sexpr second))]
    [(list '= fst second)   (Equal (parse-sexpr fst) (parse-sexpr second))]
    [(list '<= fst second)   (LessEq (parse-sexpr fst) (parse-sexpr second))]
    ;; syntax replace for "or" "and" "not"
    [(list 'not expr)        (If (parse-sexpr expr) (Bool #f) (Bool #t))]
    [(list 'and expr1 expr2) (If (parse-sexpr expr1)
                                 (parse-sexpr expr2)
                                 (Bool #f))]
    [(list 'or expr1 expr2) (If (parse-sexpr expr1)
                                (Bool #t)
                                (parse-sexpr expr2))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> ALGAE)
;; parses a string containing an ALGAE expression to an ALGAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

#| Formal specs for `subst':
   (`N' is a <num>, 'B is a True/False `E1', `E2' are <ALGAE>s,
    `x' is some <id>, `y' is a
   *different* <id>)
      N[v/x]                = N
      B[v/x]                = True/False
      {+ E ...}[v/x]        = {+  E[v/x] ...}
      {* E ...}[v/x]        = {*  E[v/x] ...}
      {- E1 E ...}[v/x]     = {-  E1[v/x] E[v/x] ...}
      {/ E1 E ...}[v/x]     = {/  E1[v/x] E[v/x] ...}
      {< E1 E2}[v/x]        = {<  E1[v/x] E2[v/x]}
      {= E1 E2}[v/x]        = {=  E1[v/x] E2[v/x]}
      {<= E1 E2}[v/x]       = {<= E1[v/x] E2[v/x]}
      y[v/x]                = y
      x[v/x]                = v
      {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
      {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
      {if COND E1 E2}[v/x]  = {if COND[v/x] E1[v/x] E2[v/x]}
      for "or" "and" "not" do the same as + - * / < = <=
|#

(: subst : ALGAE Symbol ALGAE -> ALGAE)
;; substitutes the second argument with the third argument in the
;; first argument, as per the rules of substitution; the resulting
;; expression contains no free instances of the second argument
(define (subst expr from to)
  ;; convenient helper -- no need to specify `from' and `to'
  (: subst* : ALGAE -> ALGAE)
  (define (subst* x) (subst x from to))
  ;; helper to substitute lists
  (: substs* : (Listof ALGAE) -> (Listof ALGAE))
  (define (substs* exprs) (map subst* exprs))
  (cases expr
    [(Num n)        expr]
    [(Bool n)       expr]
    [(Add args)     (Add (substs* args))]
    [(Mul args)     (Mul (substs* args))]
    [(Sub fst args) (Sub (subst* fst) (substs* args))]
    [(Div fst args) (Div (subst* fst) (substs* args))]
    [(Less fst second) (Less (subst* fst) (subst* second))]
    [(Equal fst second) (Equal (subst* fst) (subst* second))]
    [(LessEq fst second) (LessEq (subst* fst) (subst* second))]
    [(Id name)      (if (eq? name from) to expr)]
    [(With bound-id named-expr bound-body)
     (With bound-id
           (subst* named-expr)
           (if (eq? bound-id from)
               bound-body
               (subst* bound-body)))]
    [(If condition true-part false-part)
     (If (subst* condition) (subst* true-part) (subst* false-part))]))

#| Formal specs for `eval':
     eval(N)            = N
     eval(True)         = true(#t)
     eval(False)        = false(#f)
     eval({+ E ...})    = evalN(E) + ...
     eval({* E ...})    = evalN(E) * ...
     eval({- E})        = -evalN(E)
     eval({/ E})        = 1/evalN(E)
     eval({- E1 E ...}) = evalN(E1) - (evalN(E) + ...)
     eval({/ E1 E ...}) = evalN(E1) / (evalN(E) * ...)
     eval({< E1 E2})    = evalN(E1) < evalN(E2)
     eval({= E1 E2})    = evalN(E1) = evalN(E2)
     eval({<= E1 E2})   = evalN(E1) <= evalN(E2)
     eval(id)           = error!
     eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
     evalN(E) = eval(E) if it is a number, error otherwise
     eval({< E1 E2})    = true(#t)    if evalB(E1) < evalB(E2)
                        | false(#f)   if evalB(E1) >= evalB(E2)
     eval({<= E1 E2})   = true(#t)    if evalB(E1) <= evalB(E2)
                        | false(#f)   if evalB(E1) > evalB(E2)
     eval({= E1 E2})    = true(#t)    if evalB(E1) = evalB(E2)
                        | false(#f)   if evalB(E1) != evalB(E2)
     evalB(E) = eval(E) if it is a boolean, error otherwise
     eval({if COND E1 E2}) = eval(E1) if evalB(COND) is true(#t)
     eval({if COND E1 E2}) = eval(E2) if evalB(COND) is false(#f)
     ;; fake element in "or" "and" "not", use syntax transform
     eval({not E})      = eval({if E False True})
     eval({and E1 E2})  = eval({if E1 E2 False})
     eval({or E1 E2})   = eval({if E1 True E2})
|#

(: eval-number : ALGAE -> Number)
;; helper for `eval': verifies that the result is a number
(define (eval-number expr)
  (let ([result (eval expr)])
    (if (number? result)
        result
        (error 'eval-number "need a number when evaluating ~s, but got ~s"
               expr result))))

(: eval-boolean : ALGAE -> Boolean)
;; helper for 'eval': verifies that the result is a boolean
(define (eval-boolean expr)
  (let ([result (eval expr)])
    (if (boolean? result)
        result
        (error 'eval-boolean "need a boolean when evaluating ~s, but got ~s"
               expr result))))

(: value->algae : (U Number Boolean) -> ALGAE)
;; converts a value to an ALGAE value (so it can be used with `subst')
(define (value->algae val)
  (cond [(number? val) (Num val)]
        [(boolean? val) (Bool val)]
        ;; Note: a `cond' doesn't make much sense now, but it will when
        ;; we extend the language with booleans.  Also, since we use
        ;; Typed Racket, the type checker makes sure that this function
        ;; is never called with something that is not in its type, so
        ;; there's no need for an `else' branch like
        ;;     [else (error 'value->algae "unexpected value: ~s" val)]
        ;; (Strictly speaking, there's no need for the last predicate
        ;; (which is the only one here until you extend this), but it's
        ;; left in for clarity.)
        ))

(: sub-helper : Number Number -> Number)
;; helper method to cope with Racket's mechanism for foldl
(define (sub-helper a b) (- b a))

(: div-helper : Number Number -> Number)
;; helper method to cope with Racket's mechanism for foldl
(define (div-helper a b) (/ b a))

(: eval : ALGAE -> (U Number Boolean))
;; evaluates ALGAE expressions by reducing them to numbers
(define (eval expr)
  (cases expr
    [(Num n) n]
    [(Bool n) n]
    [(Add args)
     (foldl + 0 (map eval-number args))]
    [(Mul args)
     (foldl * 1 (map eval-number args))]
    [(Sub fst args)
     (foldl sub-helper (eval-number fst) (map eval-number args))]
    [(Div fst args)
     (foldl div-helper (eval-number fst) (map eval-number args))]
    [(Less fst second) (< (eval-number fst) (eval-number second))]
    [(Equal fst second) (= (eval-number fst) (eval-number second))]
    [(LessEq fst second) (<= (eval-number fst) (eval-number second))]
    [(With bound-id named-expr bound-body)
     (eval (subst bound-body
                  bound-id
                  ;; see the above `value->algae' helper
                  (value->algae (eval named-expr))))]
    [(If condition true-part false-part)
     (if (eval-boolean condition)
         (eval true-part)
         (eval false-part))]
    [(Id name) (error 'eval "free identifier: ~s" name)]))

(: run : String -> (U Number Boolean))
;; evaluate an ALGAE program contained in a string
(define (run str)
  (eval (parse str)))

;; tests (for simple expressions)
(test (run "5") => 5)
(test (run "{+ 5 5}") => 10)
(test (run "{* 5 5}") => 25)
(test (run "{/ 5 5}") => 1)
(test (run "{with {x {+ 5 5}} {+ x x}}") => 20)
(test (run "{with {x 5} {+ x x}}") => 10)
(test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => 14)
(test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => 4)
(test (run "{with {x 5} {+ x {with {x 3} 10}}}") => 15)
(test (run "{with {x 5} {+ x {with {x 3} x}}}") => 8)
(test (run "{with {x 5} {+ x {with {y 3} x}}}") => 10)
(test (run "{with {x 5} {with {y x} y}}") => 5)
(test (run "{with {x 5} {with {x x} x}}") => 5)
(test (run "{with something else blah blah blah}") =error> "bad `with' syntax")
(test (run "{intentionally bad}") =error> "bad syntax")
(test (run "{with {z 5} {* x 3 y}}") =error> "free identifier")

;; test cases for Part 1
(test (run "{* 5 1 2}") => 10)
(test (run "{+ 1 2 3 4 5}") => 15)
(test (run "{/ {* 10 5} {* 5 2} 5}") => 1)
(test (run "{+}") => 0)
(test (run "{*}") => 1)
(test (run "{/ 3}") => 3)
(test (run "{- 1}") => 1)
;; test with combine with arithmetic operator
(test (run "{with {c {/ 1 5}} {+ {* 20 c} 6}}") => 10) ;; 10 = 20 * 1/5 + 6
(test (run "{with {x {/ 1 3}} {with {y {/ 1 9}} {/ x y}}}") => 3)
(test (run "{with {False True} {with {y False} y}}") => #f) 

;; test cases for Part 2

;; the base syntax
(test (run "True") => #t)
(test (run "False") => #f)
;; the comparator
(test (run "{< 2 3}") => #t)
(test (run "{<= 4 4}") => #t)
(test (run "{<= 57 56}") => #f)
(test (run "{= 9 9}") => #t)
;; test the type check
(test (run "{< 81 False}") =error>
      "need a number when evaluating (Bool #f), but got #f")
;; combine comparator and with statement
(test (run "{with {a {* 12 13}} {with {b {< 157 a}} b}}") => #f)
(test (run "{with {x {* 14 7}} {<= 99 x}}") => #f)
(test (run "{with {x 6} {= 36 {* x 6}}}") => #t)
;; test basic if statement
(test (run "{if {< 4 6} 45 True}") => 45)
;; test if statement combine with statement
(test (run "{with {x {* 11 5}} {with {y {* 6 9}} {if {< x y} 8 9} }}") => 9)
(test (run "{with {x 6} {with {y {if {= x 7} 6 False}} {if y 0 1} }}") => 1)
;; test if syntax error
(test (run "{if cond true-part false-part more}") =error>
      "parse-sexpr: bad `if' syntax in (if cond true-part false-part more)")
(test (run "{if {< 1 2}}") =error>
      "parse-sexpr: bad `if' syntax in (if (< 1 2))")
;; test if type check
(test (run "{if {+ 1 2} 11 12}") =error>
      (string-append "eval-boolean: need a boolean when evaluating"
                     " (Add ((Num 1) (Num 2))), but got 3"))

;; test cases for Part 3
(test (run "{not {= 1 1}}") => #f)
(test (run "{not False}") => #t)
(test (run "{and True True}") => #t)
(test (run "{and False True}") => #f)
(test (run "{and True False}") => #f)
(test (run "{and False False}") => #f)
(test (run "{or False False}") => #f)
(test (run "{or True False}") => #t)
(test (run "{or False True}") => #t)
(test (run "{or True True}") => #t)
;; make sure the "or", "and" are lazy evaluated
(test (run "{and {< 5 4} {+ 4 True}}") => #f)
(test (run "{or {= 1 1} {if 4 8 9}}") => #t)

(define minutes-spent 50)