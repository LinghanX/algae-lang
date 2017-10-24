#lang pl 06

;; ** The Brang interpreter, using environments

#|
The grammar:
  <BRANG> ::= <num>
            | { + <BRANG> <BRANG> }
            | { - <BRANG> <BRANG> }
            | { * <BRANG> <BRANG> }
            | { / <BRANG> <BRANG> }
            | { with { <id> <BRANG> } <BRANG> }
            | <id>
            | { fun { <id> <id> ... } <BRANG> }
            | { call <BRANG> <BRANG> <BRANG> ... }

Evaluation rules:
  eval(N,env)                = N
  eval({+ E1 E2},env)        = eval(E1,env) + eval(E2,env)
  eval({- E1 E2},env)        = eval(E1,env) - eval(E2,env)
  eval({* E1 E2},env)        = eval(E1,env) * eval(E2,env)
  eval({/ E1 E2},env)        = eval(E1,env) / eval(E2,env)
  eval(x,env)                = lookup(x,env)
  eval({with {x E1} E2},env) = eval(E2,extend(x,eval(E1,env),env))
  eval({fun {x} E},env)      = <{fun {x} E}, env>
  eval({call E1 E2},env1)
           = eval(Ef,extend(x,eval(E2,env1),env2))
                             if eval(E1,env1) = <{fun {x} Ef}, env2>
           = error!          otherwise
|#

(define-type BRANG
  [Num  Number]
  [Add  BRANG BRANG]
  [Sub  BRANG BRANG]
  [Mul  BRANG BRANG]
  [Div  BRANG BRANG]
  [Id   Symbol]
  [With Symbol BRANG BRANG]
  [Fun  (Listof Symbol) BRANG]
  [Call BRANG (Listof BRANG)])

(: parse-sexpr : Sexpr -> BRANG)
;; parses s-expressions into BRANGs
(define (parse-sexpr sexpr)
  (match sexpr
    [(number: n)    (Num n)]
    [(cons 'with more)
     (match sexpr
       [(list 'with (list (symbol: name) named) body)
        (With name (parse-sexpr named) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
    [(cons 'fun more)
     (match sexpr
       [(list 'fun (list (symbol: first-name) (symbol: rest-names) ...) body)
        (Fun (cons first-name rest-names) (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'call fun more ...)
     (if (null? more) (error 'parse-sexpr "call need argument: ~s" sexpr)
         (Call (parse-sexpr fun) (map parse-sexpr more)))]
    [(symbol: name) (Id name)]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; ** The CORE interpreter, using environments

#|
The grammar:
  <CORE> ::= <num>
            | { + <CORE> <CORE> }
            | { - <CORE> <CORE> }
            | { * <CORE> <CORE> }
            | { / <CORE> <CORE> }
            | { with { <id> <CORE> } <CORE> }
            | <id>
            | { fun { <id> } <CORE> }
            | { call <CORE> <CORE> }

Evaluation rules:
  eval(N,env)                = N
  eval({+ E1 E2},env)        = eval(E1,env) + eval(E2,env)
  eval({- E1 E2},env)        = eval(E1,env) - eval(E2,env)
  eval({* E1 E2},env)        = eval(E1,env) * eval(E2,env)
  eval({/ E1 E2},env)        = eval(E1,env) / eval(E2,env)
  eval(x,env)                = lookup(x,env)
  eval({with {x E1} E2},env) = eval(E2,extend(x,eval(E1,env),env))
  eval({fun {x} E},env)      = <{fun {x} E}, env>
  eval({call E1 E2},env1)
           = eval(Ef,extend(x,eval(E2,env1),env2))
                             if eval(E1,env1) = <{fun {x} Ef}, env2>
           = error!          otherwise
|#

(define-type CORE
  [CNum  Number]
  [CAdd  CORE CORE]
  [CSub  CORE CORE]
  [CMul  CORE CORE]
  [CDiv  CORE CORE]
  ;; the integer value is the index
  [CRef  Integer]
  ;; only contain function body, the name is not needed
  [CFun  CORE]
  ;; first is the function value, second is the parameter to function
  [CCall CORE CORE])

;; Types for environments, values, and a lookup function for core

(define-type CVAL
  [CNumV Number]
  ;; there is no need for an parameter name
  [CFunV CORE ENV])

(define-type ENV = (Listof CVAL))

;; can be designed as an function Symbol -> Integer
;; however, using an symbol list is easier to debug than clojure by composing
;; functions
(define-type DE-ENV = (Listof Symbol))

(: var->index-helper : DE-ENV Symbol Integer -> Integer)
(define (var->index-helper de-env symbol depth)
  (match de-env
    [(cons first rest)
     (if (eq? first symbol)
         depth
         (var->index-helper rest symbol (add1 depth)))]
    ['() (error 'var-binding "unbound identifier: ~s" symbol)]))

(: var->index : DE-ENV Symbol -> Integer)
(define (var->index de-env symbol)
  (var->index-helper de-env symbol 0))

(: do-empty-env : DE-ENV)
(define do-empty-env '())

(: do-extend : DE-ENV Symbol -> DE-ENV)
(define (do-extend de-env symbol)
  (cons symbol de-env))

(: CNumV->number : CVAL -> Number)
;; convert a CORE runtime numeric value to a Racket one
(define (CNumV->number val)
  (cases val
    [(CNumV n) n]
    [else (error 'arith-op "expected a number, got: ~s" val)]))

(: Carith-op : (Number Number -> Number) CVAL CVAL -> CVAL)
;; gets a Racket numeric binary operator, and uses it within a NumV
;; wrapper
(define (Carith-op op val1 val2)
  (CNumV (op (CNumV->number val1) (CNumV->number val2))))

(: Ceval : CORE ENV -> CVAL)
;; evaluates CORE expressions by reducing them to values
(define (Ceval expr env)
  (cases expr
    [(CNum n) (CNumV n)]
    [(CAdd l r) (Carith-op + (Ceval l env) (Ceval r env))]
    [(CSub l r) (Carith-op - (Ceval l env) (Ceval r env))]
    [(CMul l r) (Carith-op * (Ceval l env) (Ceval r env))]
    [(CDiv l r) (Carith-op / (Ceval l env) (Ceval r env))]
    [(CRef index) (list-ref env index)]
    [(CFun bound-body)
     (CFunV bound-body env)]
    [(CCall fun-expr arg-expr)
     (let* ([Cfval (Ceval fun-expr env)]
            [Argument (Ceval arg-expr env)])
       (cases Cfval
         [(CFunV bound-body f-env)
          (Ceval bound-body
                (cons Argument f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                            Cfval)]))]))

;; the preprocessor transform brang ast to core ast using helper defined above
(: preprocessor : BRANG -> CORE)
(define (preprocessor brang) (brang->core brang do-empty-env))

(: brang->core : BRANG DE-ENV -> CORE)
(define (brang->core brang de-env)
  (: recur : BRANG -> CORE)
  ;; a shortcur from (brang->core x de-env) to (recur x)
  (define (recur x) (brang->core x de-env))
  (cases brang
    [(Num n) (CNum n)]
    [(Add br1 br2) (CAdd (recur br1) (recur br2))]
    [(Sub br1 br2) (CSub (recur br1) (recur br2))]
    [(Mul br1 br2) (CMul (recur br1) (recur br2))]
    [(Div br1 br2) (CDiv (recur br1) (recur br2))]
    [(Id name) (CRef (var->index de-env name))]
    [(With name def body)
     ;; delegate the with statement into a call of lambda expression
     (recur (Call (Fun (list name) body) (list def)))]
    [(Fun param body) (build-cfun param body de-env)]
    [(Call fexpr argument) (build-ccall fexpr (reverse argument) de-env)]))

;; helper function for recursively build the CFun and CCall with more arguments
;; this is used to build function call, transform:
;; λ(a b c d) E -> λ(a)λ(b)λ(c)λ(d) E
(: build-cfun : (Listof Symbol) BRANG DE-ENV -> CORE)
(define (build-cfun params body de-env)
  (if (null? params)
      (brang->core body de-env)
      (CFun (build-cfun (rest params)
                        body
                        (do-extend de-env (first params))))))

;; helper function, need a reverse to call on arg-exprs before pass to
;; this function to get right passing order, THIS FUNCTION DO:
;; {call F A B C D} to {call {call {call {call F D} C} B} A}
(: build-ccall : BRANG (Listof BRANG) DE-ENV -> CORE)
(define (build-ccall fexpr arg-exprs de-env)
  (if (null? arg-exprs)
      (brang->core fexpr de-env)
      (CCall (build-ccall fexpr (rest arg-exprs) de-env)
             (brang->core (first arg-exprs) de-env))))

;; defines the run, actually the run can return an closure of function
(: run : String -> (U Number CVAL))
(define (run str)
  (let ([result (Ceval (preprocessor (parse str)) '())])
    (cases result
      [(CNumV n) n]
      [(CFunV core env) result])))
 
;; tests for Flang

(test (run "{call {fun {x} {+ x 1}} 4}")
      => 5)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {call add3 1}}")
      => 4)
(test (run "{with {add3 {fun {x} {+ x 3}}}
              {with {add1 {fun {x} {+ x 1}}}
                {with {x 3}
                  {call add1 {call add3 x}}}}}")
      => 7)
(test (run "{with {identity {fun {x} x}}
              {with {foo {fun {x} {+ x 1}}}
                {call {call identity foo} 123}}}")
      => 124)
(test (run "{with {x 3}
              {with {f {fun {y} {+ x y}}}
                {with {x 5}
                  {call f 4}}}}")
      => 7)
(test (run "{call {with {x 3}
                    {fun {y} {+ x y}}}
                  4}")
      => 7)
(test (run "{call {call {fun {x} {call x 1}}
                        {fun {x} {fun {y} {+ x y}}}}
                  123}")
      => 124)

;; more tests for the language
(test (run "{- {* 5 7} {/ 68 2}}") => 1)
(test (run "{call {fun {x} {fun {y} {+ x y}}} 8}") =>
      (CFunV (CAdd (CRef 1) (CRef 0)) (list (CNumV 8))))

;; test unbound identifier exception
(test (run "{call {call {fun {x} y} 6} 8}")
      =error> "var-binding: unbound identifier: y")
;; test error with form
(test (run "{with {x 6} with {y 7} {+ x y}}") =error>
      "parse-sexpr: bad `with' syntax in (with (x 6) with (y 7) (+ x y))")
;; test error fun form
(test (run "{fun {x} {y} {+ x y}}") =error>
      "parse-sexpr: bad `fun' syntax in (fun (x) (y) (+ x y))")
;; test bad syntax by using a call with zero argument
(test (run "{call {fun {x} x}}") =error>
      "parse-sexpr: call need argument: (call (fun (x) x))")
;; test bad syntax
(test (run "{add bcd sad edc}") =error>
      "parse-sexpr: bad syntax in (add bcd sad edc)")
;; test runtime type error
(test (run "{+ {fun {x} x} 2}") =error>
      "arith-op: expected a number, got: (CFunV (CRef 0) ())")
(test (run "{call 1 2}") =error>
      "eval: `call' expects a function, got: (CNumV 1)")

;; test functions that take many arguments
(test (run "
{call
  {call
    {fun {a b c d}
      {fun {e f g}
        {/ {+ a {+ b {+ c {+ d {+ e {+ f g}}}}}} 7}
      }
    }
    1 2 3 4
  }
  5 6 7
}") => 4)

(test (run "{call {fun {x y z h} {+ {* x y} {/ z h}}} 3 4 18 6}")
      => (+ (* 3 4) (/ 18 6)))