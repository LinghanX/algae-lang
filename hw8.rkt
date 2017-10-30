#lang pl 08

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
            | { call <BRANG> <BRANG> <BRANG> ... }
            | { if0 <BRANG> <BRANG> <BRANG> }
            | <FUN-EXPR>
            | { rec { <id> <FUN-EXPR> } <BRANG> }
  <FUN-EXPR> ::= { fun { <id> <id> ... } <BRANG> }

Transform rules (from BRANG to CORE syntax):
  trans(N,de-env)                = N
  trans({+ E1 E2},de-env)        = trans(E1,de-env) + trans(E2,de-env)
  trans({- E1 E2},de-env)        = trans(E1,de-env) - trans(E2,de-env)
  trans({* E1 E2},de-env)        = trans(E1,de-env) * trans(E2,de-env)
  trans({/ E1 E2},de-env)        = trans(E1,de-env) / trans(E2,de-env)
  trans(x,de-env)                = map-to-index(x,de-env)
  trans({with {x E1} E2},de-env)
        = trans({call {fun {x} E2} E1})
  trans({fun {x} E}, de-env)     = cfun {trans(E, extend(x, de-env))}
  trans({fun {x1 x2 x3 ...} E},de-env)
        = trans({fun {x1} {fun {x2} {fun {x3} ... E  } ... }}
  trans({call FE E},de-env) = {ccall trans(FE, de-env) trans(E, de-env)}
  trans({call FE E1 E2 E3 ...},de-env)
        = trans({call ... {call {call {call {FE} E1} E2} E3} ... }, de-env)
  trans({rec {t fun {x1 x2 x3 ...} F} E}, de-env)
        = trans({with {t {call Y {fun {t x1 x2 x3 ...} F}}} E}, de-env)
        where Y is Y combinator
  trans({if0 C TE FE}, de-env) =
        {cif0 trans(C, de-env) trans(TE, de-env) trans(FE, de-env)}
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
  [Call BRANG (Listof BRANG)]
  ;; {rec {id {fun {lst...} f-body} body} will transform to
  ;; (WRec id lst f-body body)
  [WRec Symbol (Listof Symbol) BRANG BRANG]
  [If0 BRANG BRANG BRANG])

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
    [(cons 'rec more)
     (match sexpr
       [(list 'rec (list (symbol: id) fun-expr) body)
        (cases (parse-sexpr fun-expr)
          [(Fun params f-body) (WRec id params f-body (parse-sexpr body))]
          [else (error 'parse-sexpr "non-fun form in `rec': ~s" sexpr)])]
       [else (error 'parse-sexpr "bad `rec' syntax in ~s" sexpr)])]
    [(cons 'if0 more)
     (match sexpr
       [(list 'if0 cond-expr true-expr false-expr)
        (If0 (parse-sexpr cond-expr)
             (parse-sexpr true-expr)
             (parse-sexpr false-expr))]
       [else (error 'parse-sexpr "bad `if' syntax in ~s" sexpr)])]
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
            | { cif0 <CORE> <CORE> <CORE> }

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
  eval({cif0 CE TE FE}, env)
           = eval(TE, env)   if eval(CE, env) == 0
           = eval(FE, env)   if eval(CE, env) is not zero or not number type
       the evaluation of TE and FE is lazy evaluated, only eval after CE is
       evaluated, when CE is eval 0, FE is not evaluated, vise versa for TE
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
  [CCall CORE CORE]
  [CIf0  CORE CORE CORE])

;; Types for environments, values, and a lookup function for core

(define-type CVAL
  [CNumV Number]
  ;; there is no need for an parameter name
  [CFunV CORE ENV])

(define-type ENV = (Listof CVAL))

(define-type DE-ENV = (Symbol -> Integer))

(: de-empty-env : DE-ENV)
(define (de-empty-env name)
  (error 'var-binding "unbound identifier: ~s" name))

(: de-extend : DE-ENV Symbol -> DE-ENV)
(define (de-extend de-env symbol)
  (lambda (name)
    (if (eq? name symbol)
        0
        (+ 1 (de-env name)))))

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

(: eval : CORE ENV -> CVAL)
;; evaluates CORE expressions by reducing them to values
(define (eval expr env)
  (cases expr
    [(CNum n) (CNumV n)]
    [(CAdd l r) (Carith-op + (eval l env) (eval r env))]
    [(CSub l r) (Carith-op - (eval l env) (eval r env))]
    [(CMul l r) (Carith-op * (eval l env) (eval r env))]
    [(CDiv l r) (Carith-op / (eval l env) (eval r env))]
    [(CRef index) (list-ref env index)]
    [(CFun bound-body)
     (CFunV bound-body env)]
    [(CCall fun-expr arg-expr)
     (let* ([Cfval (eval fun-expr env)]
            [Argument (eval arg-expr env)])
       (cases Cfval
         [(CFunV bound-body f-env)
          (eval bound-body
                (cons Argument f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                      Cfval)]))]
    [(CIf0 cond true-expr false-expr)
     (define cond-value (eval cond env))
     (if (equal? (CNumV 0) cond-value)
         (eval true-expr env)
         (eval false-expr env))]))

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
    [(Id name) (CRef (de-env name))]
    [(With name def body)
     ;; delegate the with statement into a call of lambda expression
     (recur (Call (Fun (list name) body) (list def)))]
    [(Fun param body) (build-cfun param body de-env)]
    [(Call fexpr argument) (build-ccall fexpr (reverse argument) de-env)]
    [(WRec id param f-body body)
     (recur (With id
                  (Call Y-comb (list (Fun (cons id param) f-body)))
                  body))]
    [(If0 cond true-expr false-expr)
     (CIf0 (recur cond) (recur true-expr) (recur false-expr))]))

;; the preprocessor transform brang ast to core ast using helper defined above
(: preprocess : BRANG DE-ENV -> CORE)
(define preprocess brang->core)

;; helper function for recursively build the CFun and CCall with more arguments
;; this is used to build function call, transform:
;; λ(a b c d) E -> λ(a)λ(b)λ(c)λ(d) E
(: build-cfun : (Listof Symbol) BRANG DE-ENV -> CORE)
(define (build-cfun params body de-env)
  (if (null? params)
      (brang->core body de-env)
      (CFun (build-cfun (rest params)
                        body
                        (de-extend de-env (first params))))))

;; helper function, need a reverse to call on arg-exprs before pass to
;; this function to get right passing order, THIS FUNCTION DO:
;; {call F A B C D} to {call {call {call {call F D} C} B} A}
(: build-ccall : BRANG (Listof BRANG) DE-ENV -> CORE)
(define (build-ccall fexpr arg-exprs de-env)
  (if (null? arg-exprs)
      (brang->core fexpr de-env)
      (CCall (build-ccall fexpr (rest arg-exprs) de-env)
             (brang->core (first arg-exprs) de-env))))

;; defined the cached Y combinator
(: Y-comb : BRANG)
(define Y-comb (parse "
{fun {f} 
  {call 
    {fun {x} {call f {fun {n} {call x x n}}}}
    {fun {x} {call f {fun {n} {call x x n}}}}
  }
}"))

;; defines the run, actually the run can return an closure of function
(: run : String -> (U Number CVAL))
(define (run str)
  (let ([result (eval (preprocess (parse str) de-empty-env) '())])
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

;; test for recur and if0 syntax
(test (run "
{rec
  {fact
    {fun {x} {if0 x
                  1
                  {* x {call fact {- x 1}}}
             }
    }
  }
  {call fact 8}}") => 40320)
(test (run "{if0 {- 4 4} 8 9}") => 8)
(test (run "{rec {w {fun {x} {call w x}}} {if0 w 4 5}}") => 5)

;; test for the laziness of if
(test (run "{call {if0 {+ 1 1}
                       {rec {w {fun {x} {call w x}}} {call w 4}}
                       {fun {a b} {- a b}}}
            5 6}") => -1)

;; test error of if0 and rec
;; test bad syntax of if0 statement
(test (run "{if0 1 2 3 4}") =error>
      "parse-sexpr: bad `if' syntax in (if0 1 2 3 4)")
(test (run "{if0 1 2}") =error> "parse-sexpr: bad `if' syntax in (if0 1 2)")
;; error in form of rec
(test (run "{rec {f {+ 1 2} {+ 3 4}} {call f f}}") =error>
      "parse-sexpr: bad `rec' syntax in (rec (f (+ 1 2) (+ 3 4)) (call f f))")
;; error in non-function syntax in rec
(test (run "{rec {f {+ 1 2}} {+ f 4}}") =error>
      "parse-sexpr: non-fun form in `rec': (rec (f (+ 1 2)) (+ f 4))")
;; tests for not capturing 'Y
(test (run "{rec {Y {fun {n}
                      {if0 n 1 {* n {call Y {- n 1}}}}}}
              {call Y 5}}")
      => 120)
(test (run "{rec {fact {fun {Y}
                         {if0 Y 1 {* Y {call fact {- Y 1}}}}}}
              {call fact 5}}")
      => 120)