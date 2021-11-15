#lang racket
(require redex)
(require "./peg.rkt")
;(require "./reduction.rkt")
;(require "./WFverf.rkt")
(provide (all-defined-out))


; Syntax for parsing expression evaluation
(define-extended-language WFevalPeg Grammar
  [E (e s)]
  [R e ⊥]
  [D S ⊥]
  [S 0 1])



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

                
(define-judgment-form WFevalPeg ;usar esse no is-WF
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

  
(define-judgment-form WFevalPeg ;usar no is-WF
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
  [
   --------------------------------
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

#;(define-metafunction simpleEvalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])

(define-metafunction simpleEvalPeg
  [(not-botton? ⊥)        #t]
  [(not-botton? s_1)      #f])

(define-metafunction WFevalPeg
  [(empty? ()) #f]
  [(empty? s)  #t])