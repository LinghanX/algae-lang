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
            | { fun { <id> } <BRANG> }
            | { call <BRANG> <BRANG> }

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
  [Fun  Symbol BRANG]
  [Call BRANG BRANG])

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
       [(list 'fun (list (symbol: name)) body)
        (Fun name (parse-sexpr body))]
       [else (error 'parse-sexpr "bad `fun' syntax in ~s" sexpr)])]
    [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
    [(list 'call fun arg)
                       (Call (parse-sexpr fun) (parse-sexpr arg))]
    [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

(: parse : String -> BRANG)
;; parses a string containing a BRANG expression to a BRANG AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

;; Types for environments, values, and a lookup function

(define-type ENV
  [EmptyEnv]
  [Extend Symbol VAL ENV])

(define-type VAL
  [NumV Number]
  [FunV Symbol BRANG ENV])

(: lookup : Symbol ENV -> VAL)
;; lookup a symbol in an environment, return its value or throw an
;; error if it isn't bound
(define (lookup name env)
  (cases env
    [(EmptyEnv) (error 'lookup "no binding for ~s" name)]
    [(Extend id val rest-env)
     (if (eq? id name) val (lookup name rest-env))]))

(: NumV->number : VAL -> Number)
;; convert a BRANG runtime numeric value to a Racket one
(define (NumV->number val)
  (cases val
    [(NumV n) n]
    [else (error 'arith-op "expected a number, got: ~s" val)]))

(: arith-op : (Number Number -> Number) VAL VAL -> VAL)
;; gets a Racket numeric binary operator, and uses it within a NumV
;; wrapper
(define (arith-op op val1 val2)
  (NumV (op (NumV->number val1) (NumV->number val2))))

(: eval : BRANG ENV -> VAL)
;; evaluates BRANG expressions by reducing them to values
(define (eval expr env)
  (cases expr
    [(Num n) (NumV n)]
    [(Add l r) (arith-op + (eval l env) (eval r env))]
    [(Sub l r) (arith-op - (eval l env) (eval r env))]
    [(Mul l r) (arith-op * (eval l env) (eval r env))]
    [(Div l r) (arith-op / (eval l env) (eval r env))]
    [(With bound-id named-expr bound-body)
     (eval bound-body
           (Extend bound-id (eval named-expr env) env))]
    [(Id name) (lookup name env)]
    [(Fun bound-id bound-body)
     (FunV bound-id bound-body env)]
    [(Call fun-expr arg-expr)
     (let ([fval (eval fun-expr env)])
       (cases fval
         [(FunV bound-id bound-body f-env)
          (eval bound-body
                (Extend bound-id (eval arg-expr env) f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                            fval)]))]))

(: run : String -> Number)
;; evaluate a BRANG program contained in a string
(define (run str)
  (let ([result (eval (parse str) (EmptyEnv))])
    (cases result
      [(NumV n) n]
      [else (error 'run "evaluation returned a non-number: ~s"
                   result)])))

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
  [CId   Symbol]
  [CWith Symbol CORE CORE]
  [CFun  Symbol CORE]
  [CCall CORE CORE])

(: Cparse-sexpr : Sexpr -> CORE)
;; parses s-expressions into COREs
(define (Cparse-sexpr csexpr)
  (match csexpr
    [(number: n)    (CNum n)]
    [(symbol: name) (CId name)]
    [(cons 'with more)
     (match csexpr
       [(list 'with (list (symbol: name) named) body)
        (CWith name (Cparse-sexpr named) (Cparse-sexpr body))]
       [else (error 'Cparse-sexpr "bad `with' syntax in ~s" csexpr)])]
    [(cons 'fun more)
     (match csexpr
       [(list 'fun (list (symbol: name)) body)
        (CFun name (Cparse-sexpr body))]
       [else (error 'Cparse-sexpr "bad `fun' syntax in ~s" csexpr)])]
    [(list '+ lhs rhs) (CAdd (Cparse-sexpr lhs) (Cparse-sexpr rhs))]
    [(list '- lhs rhs) (CSub (Cparse-sexpr lhs) (Cparse-sexpr rhs))]
    [(list '* lhs rhs) (CMul (Cparse-sexpr lhs) (Cparse-sexpr rhs))]
    [(list '/ lhs rhs) (CDiv (Cparse-sexpr lhs) (Cparse-sexpr rhs))]
    [(list 'call fun arg)
                       (CCall (Cparse-sexpr fun) (Cparse-sexpr arg))]
    [else (error 'Cparse-sexpr "bad syntax in ~s" csexpr)]))

(: Cparse : String -> CORE)
;; parses a string containing a CORE expression to a CORE AST
(define (Cparse str)
  (Cparse-sexpr (string->sexpr str)))

;; Types for environments, values, and a lookup function

(define-type CENV
  [CEmptyEnv]
  [CExtend Symbol CVAL CENV])

(define-type CVAL
  [CNumV Number]
  [CFunV Symbol CORE CENV])

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

(: Clookup : Symbol CENV -> CVAL)
;; lookup a symbol in an environment, return its value or throw an
;; error if it isn't bound
(define (Clookup name env)
  (cases env
    [(CEmptyEnv) (error 'Clookup "no binding for ~s" name)]
    [(CExtend id val rest-env)
     (if (eq? id name) val (Clookup name rest-env))]))

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

(: Ceval : CORE CENV -> CVAL)
;; evaluates CORE expressions by reducing them to values
(define (Ceval expr env)
  (cases expr
    [(CNum n) (CNumV n)]
    [(CAdd l r) (Carith-op + (Ceval l env) (Ceval r env))]
    [(CSub l r) (Carith-op - (Ceval l env) (Ceval r env))]
    [(CMul l r) (Carith-op * (Ceval l env) (Ceval r env))]
    [(CDiv l r) (Carith-op / (Ceval l env) (Ceval r env))]
    [(CWith bound-id named-expr bound-body)
     (Ceval bound-body
           (CExtend bound-id (Ceval named-expr env) env))]
    [(CId name) (Clookup name env)]
    [(CFun bound-id bound-body)
     (CFunV bound-id bound-body env)]
    [(CCall fun-expr arg-expr)
     (let ([Cfval (Ceval fun-expr env)])
       (cases Cfval
         [(CFunV bound-id bound-body f-env)
          (Ceval bound-body
                (CExtend bound-id (Ceval arg-expr env) f-env))]
         [else (error 'eval "`call' expects a function, got: ~s"
                            Cfval)]))]))

(: Crun : String -> Number)
;; evaluate a CORE program contained in a string
(define (Crun str)
  (let ([result (Ceval (Cparse str) (CEmptyEnv))])
    (cases result
      [(CNumV n) n]
      [else (error 'run "evaluation returned a non-number: ~s"
                   result)])))

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


