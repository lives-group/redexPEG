#lang racket

(require redex)
(require "./peg.rkt")

(provide (all-defined-out))

; Syntax for a big-step PEG evaluation
(define-extended-language BigStep Grammar
  [E (e s)]         ;  An evaluation is comprised of a PEG and a input 
  [s (natural ...)  ;  An input can be: * A squence of terminal symbols
     ⊥             ;                   * Booton, meaning an parser error 
     ε])            ;                   * Empty string (there is nothing to be consumed !)


; Judgment for a simple peg evaluation 
(define-judgment-form BigStep
  #:mode (eval I I O)
  #:contract (eval G E s)
  
  ;Terminal
  [-------------------------------- 
   (eval G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (dismatch? natural_1 natural_2))
   --------------------------------
   (eval G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (eval G (natural_1 ()) ⊥)]
  
 ; choice 
  [(eval G (e_1 s) (natural ...))
;   (side-condition (botton? s_1))
   --------------------------------
   (eval G ((/ e_1 e_2) s) (natural ...))]

  [(eval G (e_1 s) ⊥)
   (eval G (e_2 s) s_1)
   -------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

 
  ;Sequence
  [(eval G (e_1 s) (natural ...))
   (eval G (e_2 (natural ...)) s_2)
   -------------------------------
   (eval G ((• e_1 e_2) s) s_2)]

  [(eval G (e_1 s) ⊥)
   ------------------------------
   (eval G ((• e_1 e_2) s) ⊥)]

  ;Not
  [(eval G (e s) (natural ...) )
   ;(side-condition (not-botton? s_1))
   -------------------------------
   (eval G ((! e) s) ⊥)]  

  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((! e) s) s)]

  ;Repetition
  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((* e) s) s)]

  [(eval G (e s) (natural ...))
   ;(side-condition (botton? s_1))
   (eval G ((* e) (natural ...)) s_2)
   -------------------------------
   (eval G ((* e) s) s_2)]

  ;Empty
  [-------------------------------
   (eval G (ε s) s)]

  ;Non-Terminal
  [(eval G ((lookupG G x) s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  
  #;[(lookupG G x ⊥)
     --------------------------------
     (eval G (x s) ⊥)]
  
  )

; Checks if natural_1 and natural_2 are different
(define-metafunction BigStep
  [(dismatch? natural_1 natural_1) #f]
  [(dismatch? natural_1 natural_2) #t]) 

; Checks if is botton
#;(define-metafunction BigStep
  [(not-botton? ⊥)        #f]
  [(not-botton? s_1)      #t])

