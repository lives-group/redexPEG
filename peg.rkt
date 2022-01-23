#lang racket
(require redex)
(require rackcheck)
(provide (all-defined-out))

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
#;(define-extended-language Grammar Peg
  [G ((x e) ...)] ; A grammar is a set of nonterminal definition
)

; Syntax for a PEG grammar
(define-extended-language Grammar Peg
  [G (x e G) ∅] ; A grammar is a set of nonterminal definition
)
; Syntax for parsing expression evaluation
(define-extended-language simpleEvalPeg Grammar
  [E (e s)]         ;An evaluation is comprised of a PEG and a input 
  [s (natural ...)  ; An input can be: * A squence of terminal symbols
     ⊥              ;                  * Booton, meaning an parser error 
     ε])            ;                  * Empty string (there is nothing to be consumed !)



; Judgment for a simple peg evaluation 
(define-judgment-form simpleEvalPeg
  #:mode (eval I I O)
  #:contract (eval G E s)
  
  ;Terminal
  [-------------------------------- 
   (eval G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (diff? natural_1 natural_2))
   --------------------------------
   (eval G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (eval G (natural_1 ()) ⊥)]

  ;Choice
  [(eval G (e_1 s) s_1)
   (side-condition (botton? s_1))
   --------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  [(eval G (e_2 s) s_1)
  (side-condition (botton? s_1))  
   -------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  [------------------------------
   (eval G ((/ e_1 e_2) ()) ⊥)]

  ;Sequence
  [(eval G (e_1 s) s_1)
   (eval G (e_2 s_1) s_2)
   -------------------------------
   (eval G ((• e_1 e_2) s) s_2)]

  [(eval G (e_1 s) ⊥)
   ------------------------------
   (eval G ((• e_1 e_2) s) ⊥)]

  ;Not
  [(eval G (e s) s_1)
   (side-condition (botton? s_1))
   -------------------------------
   (eval G ((! e) s) s)] ;; coloquei para na expressao 

  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((! e) s) ε)]


  ;Repetition
  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((* e) s) s)]

  [(eval G (e s) s_1)
   (side-condition (botton? s_1))
   (eval G ((* e) s_1) s_2)
   -------------------------------
   (eval G ((* e) s) s_2)]

  ;Non-Terminal
  #;[(lookup G x e)     
   (eval G (e s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  
  #;[(lookup G x ⊥)
   --------------------------------
   (eval G (x s) ⊥)]  
  
)

(define-metafunction simpleEvalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 

(define-metafunction simpleEvalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])
