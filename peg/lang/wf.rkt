#lang racket

(require redex)
(require "../lang/peg.rkt")

(define-extended-language WFevalPeg Grammar
  [E (e s)]
  [R e ⊥]
  [D S ⊥]
  [S 0 1])

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
