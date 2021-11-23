#lang racket
(require redex)
(require "./peg.rkt")
(require "./reduction.rkt")
;(require "./WFverf.rkt")
(provide (all-defined-out))


; Syntax for parsing expression evaluation
(define-extended-language evalPeg Grammar
  [E (e s)]
  [R e ⊥]
  [D S ⊥]
  [S 0 1])

; Syntax for TypedPeg
(define-extended-language TypedPeg Peg 
  [Γ (τ ...)]
  [τ (b H)]
  [b #t #f]
  [H ∅ (x ...)]
  )



(define-judgment-form evalPeg
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

;TypedPeg
;Γ -> lista de variaveis e tipo τ
;G -> Gramatica peg
;τ -> (b, H)
;b -> T or F
;H -> var

(define-judgment-form TypedPeg
  #:mode (⊢ I I O)  
  #:contract (⊢ Γ e τ)

  [----------------------------"empty"
   (⊢ Γ ε (#t ∅))]

  [----------------------------"terminal"
   (⊢ Γ e (#f ∅))]

  [(⊢ Γ e (b H))
   ----------------------------"rep"
   (⊢ Γ (* e) (#f H))]

  [(⊢ Γ e (b H))
   ----------------------------"not"
   (⊢ Γ (! e) (#f H))]

  [(⊢ Γ  e_1 (#t H_1))
   (⊢ Γ  e_2 (b H_2))
   ----------------------------"seq_1"
   (⊢ Γ (• e_1 e_2) (b (H_1 H_2)))]


  [(⊢ Γ  e_1 (#f H_1))
   (⊢ Γ e_2 (b H_2))
   ----------------------------"seq_2"
   (⊢ Γ (• e_1 e_2) (b H_1))]

  
  [(⊢ Γ  e_1 (b_1 H_1))
   (⊢ Γ e_2 (b_2 H_2))
   ----------------------------"alt"
   (⊢ Γ (/ e_1 e_2) ((or b_1 b_2) (H_1 H_2)))]
  
  )
                
(define-judgment-form evalPeg 
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

(define-judgment-form evalPeg 
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

  
(define-judgment-form evalPeg ;usar no is-WF
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

(define-judgment-form evalPeg
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

  ;Empty
  [
   --------------------------------
   (eval G (ε s) s)]

  ;Choice
  [(eval G (e_1 s) s_1)
   (side-condition (botton? s_1))
   --------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  [(eval G (e_2 s) s_1)
   (eval G (e_1 s) ⊥)  
   -------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  #;[------------------------------
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

  ;Non-Terminal
  [(lookup G x e)     
   (eval G (e s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  
  [(lookup G x ⊥)
   --------------------------------
   (eval G (x s) ⊥)]
  )

#;(define-metafunction evalPeg
    [(is-WF x) ])


(define-metafunction evalPeg
  [(equals? x x) #t]
  [(equals? x e) #f])

(define-metafunction evalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 

(define-metafunction evalPeg
  [(diffs? x_1 x_1) #f]
  [(diffs? x_1 x_2) #t])

(define-metafunction evalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])

(define-metafunction evalPeg
  [(not-botton? ⊥)        #t]
  [(not-botton? s_1)      #f])

(define-metafunction evalPeg
  [(empty? ()) #f]
  [(empty? s)  #t])


(define-metafunction TypedPeg
  [(or #t #f) #t]
  [(or #f #t) #t]
  [(or #t #t) #t]
  [(or #f #f) #f]

  )