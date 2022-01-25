#lang racket
(require redex)
(require "./peg.rkt")
(provide (all-defined-out))
;; BIG STEP TROCAR NOME 
; Syntax for parsing expression evaluation
(define-extended-language WFevalPeg Grammar
  [E (e s)]
  [R e ⊥]
  [D S ⊥]
  [S 0 1])

; Syntax for TypedPeg
;; Γ -> list of variables of type τ
;; G -> Peg Grammar 
;; τ -> (b, H)
;; b -> T or F
;; H -> var
(define-extended-language TypedPeg Peg 
  [Γ ((x τ ) ...)]
  [τ (b H)]
  [b #t #f]
  [H (x ...)]
  )

; Helpers for TypedPeg
(define-metafunction TypedPeg
  [(∨ #t #f) #t]
  [(∨ #f #t) #t]
  [(∨ #t #t) #t]
  [(∨ #f #f) #f]
  )

;Helpers functions for TypedPeg

(define-metafunction TypedPeg
  [(∪ H_1 H_2 ) ,(set-union (term H_1) (term H_2))]
  )

(define-metafunction TypedPeg
  [(ΓLook ((x_1 τ_1) (x_2 τ_2) ...) x_1) τ_1]
  [(ΓLook ((x_1 τ_1) (x_2 τ_2) ...) x_3) (ΓLook ((x_2 τ_2) ...) x_3)] 
  )

(define-metafunction TypedPeg
  [(ins (b H) x) (b ,(set-union (list (term x)) (term H)))]
  )

; Judgment to find the type of a peg
; Return (b H) -> (nullable or not (list of vars))
(define-judgment-form TypedPeg
  #:mode (⊢ I I O)  
  #:contract (⊢ Γ e τ)

  [----------------------------"empty"
   (⊢ Γ ε (#t ()))]

  [----------------------------"terminal"
   (⊢ Γ number (#f ()))]

  [----------------------------"var"
   (⊢ Γ x (ins (ΓLook Γ x) x))]

  [(⊢ Γ e (b H))
   ----------------------------"rep"
   (⊢ Γ (* e) (#t H))]

  [(⊢ Γ e (b H))
   ----------------------------"not"
   (⊢ Γ (! e) (#t H))]

  [(⊢ Γ  e_1 (#t H_1))
   (⊢ Γ  e_2 (b H_2))
   ----------------------------"seq_1"
   (⊢ Γ (• e_1 e_2) (b (∪ H_1 H_2)))]

  [(⊢ Γ  e_1 (#f H_1))
   (⊢ Γ e_2 (b H_2))
   ----------------------------"seq_2"
   (⊢ Γ (• e_1 e_2) (#f H_1))]

  [(⊢ Γ  e_1 (b_1 H_1))
   (⊢ Γ e_2 (b_2 H_2))
   ----------------------------"alt"
   (⊢ Γ (/ e_1 e_2) ((∨ b_1 b_2) (∪ H_1 H_2)))]
  )


; Judgment to help verify the evaluation of a grammar
; Return true or false
(define-judgment-form WFevalPeg
  #:mode (↛ I I O)
  #:contract (↛ G D boolean)

  [-------------------------------
   (↛ G 0 #f)]
  
  [-------------------------------
   (↛ G 1 #t)]

  [-------------------------------
   (↛ G ⊥ #t)]

  [(↛ G D_1 #f)
   (↛ G D_2 #t)
   -------------------------------
   (↛ G (D_1 D_2) #f)]

  [(↛ G D_1 #t)
   (↛ G D_2 #f)
   -------------------------------
   (↛ G (D_1 D_2) #f)]
  )

                
; Judgment to verify if the grammar consumes a entry
; Return:
; 0: succed while consuming no input
; 1: succed while consuming at least one terminal
; ⊥: fail on some input
(define-judgment-form WFevalPeg 

  #:mode (⇀ I I O)
  #:contract (⇀ G e D)

  ;Empty
  [-------------------------------
   (⇀ G ε 0)]

  ;Terminal
  [-------------------------------
   (⇀ G natural 1)]

  [-------------------------------
   (⇀ G natural ⊥)]

  ;Non-Terminal
  [(lookup G x e)
   (⇀ G e D)
   -------------------------------
   (⇀ G x D)]

  #;[(lookup G x ⊥)
     -------------------------------
     (⇀ G x ⊥)]
 
  ;Sequence
  [(⇀ G e_1 0)
   (⇀ G e_2 0)
   -------------------------------
   (⇀ G (• e_1 e_2) 0)]

  [(⇀ G e_1 1)
   (⇀ G e_2 S)
   -------------------------------
   (⇀ G (• e_1 e_2) 1)]

  [(⇀ G e_1 0)
   (⇀ G e_2 1)
   -------------------------------
   (⇀ G (• e_1 e_2) 1)]

  [(⇀ G e_1 ⊥)
   -------------------------------
   (⇀ G (• e_1 e_2) ⊥)]
  
  [(⇀ G e_1 S)
   (⇀ G e_2 ⊥)
   -------------------------------
   (⇀ G (• e_1 e_2) ⊥)]

  ;Choice
  [(⇀ G e_1 S)
   -------------------------------
   (⇀ G (/ e_1 e_2) S)]
  
  [(⇀ G e_1 ⊥)
   (⇀ G e_2 D)
   -------------------------------
   (⇀ G (/ e_1 e_2) D)]

  ;Repetition
  [(⇀ G e 1)
   -------------------------------
   (⇀ G (* e) 1)]

  [(⇀ G e 0)
   -------------------------------
   (⇀ G (* e) 0)]

  ;Not
  [(⇀ G e S)
   -------------------------------
   (⇀ G (! e) ⊥)]

  [(⇀ G e ⊥)
   ;(side-condition (not-zero? e))
   -------------------------------
   (⇀ G (! e) 0)]
 
  [(⇀ G e ⊥)
   -------------------------------
   (⇀ G (! e) 1)]
  )

; Judgment to verify if a peg and a grammar are well-formed
; Return true or false
(define-judgment-form WFevalPeg 
  #:mode (WF I I O)
  #:contract (WF G e boolean)

  ;Empty
  [-------------------------
   (WF G ε #t)]

  ;Natural
  [-------------------------
   (WF G natural #t)]

  ;Non terminal
  [(lookup G x e)
   (WF G e #t)
   -------------------------
   (WF G x #t)]

  ;Sequence
  [(WF G e_1 #t)
   (⇀ G e_1 0)
   (WF G e_2 #t)
   -------------------------------
   (WF G (• e_1 e_2) #t)]

  [(WF G e_1 #t)
   (⇀ G e_1 ⊥) 
   ;(WF G e_2 #f)
   -------------------------------
   (WF G (• e_1 e_2) #t)]

  [(WF G e_1 #t)
   (⇀ G e_1 1)
   -------------------------------
   (WF G (• e_1 e_2) #t)]

  ;Choice
  [(WF G e_1 #t)
   (WF G e_2 #t)
   -------------------------------
   (WF G (/ e_1 e_2) #t)]

  ;Repetition
  #;[(⇀ G e 1)
     (WF G e #t)
     -------------------------------
     (WF G (* e) #t)]

  #;[(⇀ G e 0)
     -------------------------------
     (WF G (* e) #f)]

  [(⇀ G e D)
   (↛ G D boolean)
   -------------------------------
   (WF G (* e) boolean)]

  #;[(⇀ G e D)
     (↛ G D #f)
     -------------------------------
     (WF G (* e) #f)]

  #;[(⇀ G e ⊥)
     (WF G e #t)
     -------------------------------
     (WF G (* e) #t)]

  ;Not
  [(WF G e #t)
   -------------------------------
   (WF G (! e) #t)]
  )

; Judgment to look up for the value of some grammar
; Return the value (peg or fail)
(define-judgment-form WFevalPeg 
  #:mode (lookup I I O)
  #:contract (lookup G x R)
  
  [--------------------------------
   (lookup (x_1 e G) x_1 e)]

  [--------------------------------
   (lookup ∅ x ⊥)]

  [(lookup G x_2 R)
   (side-condition (diffs? x_1 x_2))
   --------------------------------
   (lookup (x_1 e_1 G) x_2 R)] 
  )

; Judgment to evaluate if a peg consumes a entry
; Return what left of the entry
(define-judgment-form simpleEvalPeg
  #:mode (evalWF I I O)
  #:contract (evalWF G E s)
  
  ;Terminal
  [-------------------------------- 
   (evalWF G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (diff? natural_1 natural_2))
   --------------------------------
   (evalWF G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (evalWF G (natural_1 ()) ⊥)]

  ;Empty
  [--------------------------------
   (evalWF G (ε s) s)]

  ;Choice
  [(evalWF G (e_1 s) s_1)
   (side-condition (botton? s_1))
   --------------------------------
   (evalWF G ((/ e_1 e_2) s) s_1)]

  [(evalWF G (e_2 s) s_1)
   (evalWF G (e_1 s) ⊥)  
   -------------------------------
   (evalWF G ((/ e_1 e_2) s) s_1)]

  #;[------------------------------
     (evalWF G ((/ e_1 e_2) ()) ⊥)]

  ;Sequence
  [(evalWF G (e_1 s) s_1)
   (evalWF G (e_2 s_1) s_2)
   -------------------------------
   (evalWF G ((• e_1 e_2) s) s_2)]

  [(evalWF G (e_1 s) ⊥)
   ------------------------------
   (evalWF G ((• e_1 e_2) s) ⊥)]

  ;Not
  [(evalWF G (e s) s_1)
   (side-condition (botton? s_1))
   -------------------------------
   (evalWF G ((! e) s) ⊥)]

  [(evalWF G (e s) ⊥)
   -------------------------------
   (evalWF G ((! e) s) s)]

  ;Repetition
  [(evalWF G (e s) ⊥)
   -------------------------------
   (evalWF G ((* e) s) s)]

  [(evalWF G (e s) s_1)
   (side-condition (botton? s_1))
   (evalWF G ((* e) s_1) s_2)
   -------------------------------
   (evalWF G ((* e) s) s_2)]

  ;Non-Terminal
  [(lookup G x e)     
   (evalWF G (e s) s_1)
   --------------------------------
   (evalWF G (x s) s_1)]
  
  [(lookup G x ⊥)
   --------------------------------
   (evalWF G (x s) ⊥)]
  )

;Helper function of the grammar WFevalPeg
#;(define-metafunction WFevalPeg
    [(is-WF x) ])

(define-metafunction WFevalPeg
  [(equals? x x) #t]
  [(equals? x e) #f])

#;(define-metafunction WFevalPeg
    [(diff? natural_1 natural_1) #f]
    [(diff? natural_1 natural_2) #t]) 

(define-metafunction WFevalPeg
  [(diffs? x_1 x_1) #f]
  [(diffs? x_1 x_2) #t])

(define-metafunction WFevalPeg
  [(empty? ()) #f]
  [(empty? s)  #t])

;Helper function of the grammar simpleEvalPeg
#;(define-metafunction simpleEvalPeg
    [(botton? ⊥)        #f]
    [(botton? s_1)      #t])

(define-metafunction simpleEvalPeg
  [(not-botton? ⊥)        #t]
  [(not-botton? s_1)      #f])



; Tests for TypedPeg judgment

;(judgment-holds (⊢ () ε τ) τ)
;(judgment-holds (⊢ () (! (/ 1 2)) τ) τ)
;(judgment-holds (⊢ ((A (#f ()))) A τ) τ)
;(judgment-holds (⊢ ((A (#f ())) (B (#t (A)))) B τ) τ)


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
   (eval G ((! e) s) ⊥)]  

  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((! e) s) s)]

  ;Repetition
  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((* e) s) s)]

  [(eval G (e s) s_1)
   (side-condition (botton? s_1))
   (eval G ((* e) s_1) s_2)
   -------------------------------
   (eval G ((* e) s) s_2)]

  ;Empty
  [-------------------------------
   (eval G (ε s) s)]

  ;Non-Terminal
  [(lookup G x e)     
   (eval G (e s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  
  [(lookup G x ⊥)
   --------------------------------
   (eval G (x s) ⊥)]  
  
  )


; Checks if natural_1 and natural_2 are different
(define-metafunction simpleEvalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 

; Checks if is botton
(define-metafunction simpleEvalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])



