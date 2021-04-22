#lang racket
(require redex)

; Syntax of parsing expressions
(define-language Peg
   (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Temrinal 
    (x variable-not-otherwise-mentioned))

; Syntax for a PEG grammar
(define-extended-language Grammar Peg
  [G ((x e) ...)] ; A grammar is a set of nonterminal definition
)

; Syntax for parsing expression evaluation
(define-extended-language evalPeg Grammar
  [E (e s)]
  [s (natural ...)
     ⊥])


(define-judgment-form evalPeg
  #:mode (eval I I O)
  #:contract (eval G E s)
  [(eval G (e_1 s) s_1)
   (side-condition (botton? s_1))
   --------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]
  
  
  [--------------------------------
   (eval G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (diff? natural_1 natural_2))
   --------------------------------
   (eval G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (eval G (natural_1 ()) ⊥)]
  
  )

(define-metafunction evalPeg
  [(botton? ⊥)       #f]
  [(botton? s_1)     #t])

(define-metafunction evalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 


(judgment-holds (eval () (1 (1 1 1)) s) s)
(judgment-holds (eval () (1 (2 1 1)) s) s)
(judgment-holds (eval () (1 ()) s) s)

(judgment-holds (eval () ((/ 1 2) (1 1 1)) s) s)
(judgment-holds (eval () ((/ 1 2) (2 1 1)) s) s) ;;

 