#lang pl 17

(define-type Token = (U Symbol Integer))

;; A macro that defines a DFA language
(define-syntax automaton
  (syntax-rules (: ->)
    [(automaton init-state end
                [state : (input-sym -> new-state) ...]
                ...)
     (lambda (string)
       (: state : (Listof Token) -> Boolean)
       ...
       (define (state stream)
         (match stream
           ['() (eq? 'state 'end)]
           [(cons 'input-sym more) (new-state more)]
           ...
           [_ #f]))
       ...
       (init-state (explode-string string)))]))

#|(define-syntax pushdown
  (syntax-rules (: ->)
    [(pushdown init end
               [state : ((input-item)
                         (stack-item)
                         -> after-state addition) ...]
               ...)
     (lambda (string)
       (define (init stream stack)
         (match (list stream stack)
           [(list '() '()) (eq? 'after-state 'end)]
           [(list (list-rest fst rst)
                  (list-rest fst-stack rst-stack))
            (after-state rst (append 'addition stack))]
           ...
           [_ #f]))
       (init (append (explode-string string) '(*)) '(*)))]))|#

(define-syntax pushdown
  (syntax-rules (: ->)
    [(pushdown init end
               [state : ((input-ptn ...) (stack-ptn ...)
                                   -> new-state (addition ...)) ...]
               ...)
     (lambda (string)
       (: state : (Listof Token) (Listof Token) -> Boolean) ...
       (define state
         (lambda (stream stack)
           (match (list stream stack)
             [(list (list-rest 'input-ptn ... in-val)
                    (list-rest 'stack-ptn ... stack-val))
              (new-state in-val (append (list 'addition ...) stack-val))]
             ...
             [(list '(*) _) (eq? state end)]
             [(list '() _) (eq? state end)]
             [else #f])))
       ...
       (init (append (explode-string string) '(*)) '(*)))]))

(: cXr : String -> Boolean)
;; Identifies strings that match "c[ad]*r+"
(define cXr (automaton init end; `end' is the accepting state
                       [init : (c -> more)]
                       [more : (a -> more)
                             (d -> more)
                             (r -> end)]
                       [end  : (r -> end)]))

;; tests:
(test (cXr "cadr" ))
(test (cXr "cadadadadadadddddaaarrr"))
(test (not (cXr "ccadr")))
(test (not (cXr "c"))) ; BAD TEST!

(: div5 : String -> Boolean)
;; Determine whether a binary number is divisible by 5
(define div5
  (automaton mod0 mod0
             [mod0 : (0 -> mod0) (1 -> mod1)]
             [mod1 : (0 -> mod2) (1 -> mod3)]
             [mod2 : (0 -> mod4) (1 -> mod0)]
             [mod3 : (0 -> mod1) (1 -> mod2)]
             [mod4 : (0 -> mod3) (1 -> mod4)]))
(test (div5 ""))
(test (div5 "0"))
(test (div5 "000"))
(test (div5 (number->string 12345 2)))
(test (not (div5 (number->string 123453 2))))
(test (not (div5 "10011111")))

(: zeros=ones : String -> Boolean)
;; Identifies strings of n 0s followed by n 1s
(define zeros=ones
  (pushdown 0s end
            [0s  : ((0) ()  -> 0s  (A))
                 (()  ()  -> 1s  ())]
            [1s  : ((1) (A) -> 1s  ())
                 ((*) (*) -> end (*))]
            [end : (()  (*) -> end ())]))

;; tests:
(test (zeros=ones ""))
(test (zeros=ones "01"))
(test (zeros=ones "000111"))
(test (not (zeros=ones "0")))
(test (not (zeros=ones "11")))
(test (not (zeros=ones "10")))
(test (not (zeros=ones "00011")))
(test (not (zeros=ones "00101111")))

(: pair-parentheses : String -> Boolean)
(define pair-parentheses
  (pushdown A end
            [A  : ((open) ()  -> A  (open))
                 ((a)  ()  -> A  ())
                 ((close) (open) -> A ())
                 ((*) (*) -> end ())]
            [end : ]))

(test (pair-parentheses "aaaaaa"))
(test (not (pair-parentheses "(((((")))
(test (pair-parentheses "((((()))))"))
(test (pair-parentheses ""))
(test (pair-parentheses "(aa((aa(()aaa)a))aaaaa)"))

(: contains-a : String -> Boolean)
(define contains-a
  (pushdown
   B A
   [B : ((b) () -> B ())
        ((a) () -> A (a))]
   [A : ((b) () -> A ())
        ((a) () -> A (a))]))

(test (not (contains-a "bbbbbbb")))
(test (contains-a "bbbabbbaabb"))
;; find other input like c in aaaa'c'aaa will come to false
(test (not (contains-a "aaaacaaa")))

(define minutes-spent 253)