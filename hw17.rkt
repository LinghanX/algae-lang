#lang pl 17

(define-type Token = (U Symbol Integer))

;; A macro that defines a DFA language
(define-syntax automaton
  (syntax-rules (: -> end)
    [(automaton init-state end
                [state : (input-sym -> new-state) ...]
                ...)
     (lambda (string)
       (: state : (Listof Token) -> Boolean)
       ...
       (define (state stream)
         (match stream
           ['() (if (eq? 'state 'end) #t #f)]
           [(cons 'input-sym more) (new-state more)]
           ...
           [_ #f]))
       ...
       (init-state (explode-string string)))]))

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