#lang racket
(require redex)

(define-language Peg
   [E (• E E)
      (/ E E)
      (★ E)
      (! E)
      x
      string
      ϵ]
  [x variable-not-otherwise-mentioned]
  [G ((x E) G)
     ∅]
  [P (G E)]
   )

(define-extended-language  TypedPegExp Peg
  [hs (x hs)
      ∅]
  [τ  (boolean hs)]
  [Γ ∅ (x : τ Γ)]
  )


(define-judgment-form
  TypedPegExp
  #:mode (element I I O)
  #:contract (element hs x boolean)

  [ ---------------------------
    (element ∅ _ #f) ]
  
  [ (element hs     x_1 boolean)
    -------------------------------
    (element (x hs) x_1 (same x x_1 #t boolean)) ]
  )

(define-judgment-form
  TypedPegExp
  #:mode (cheat I I O)
  #:contract (cheat x x boolean)

  [ ---------------------------
    (cheat x_1 x_2 (samevar x_1 x_2)) ]
  
  )

(define-judgment-form
  TypedPegExp
  #:mode (types I I O)
  #:contract (types Γ E τ)

  [ ---------------------------
    (types Γ string (#f ∅) ) ]

   [ ---------------------------
    (types Γ ϵ (#t ∅) ) ]
  
  [(types Γ E_1 τ_1 )
   (types Γ E_2 τ_2 ) 
    ---------------------------
    (types Γ (• E_1 E_2) (⊗ τ_1 τ_2) ) ]

  [(types Γ E_1 τ_1 )
   (types Γ E_2 τ_2 ) 
    ---------------------------
    (types Γ (/ E_1 E_2) (⊕ τ_1 τ_2) ) ]

  [(types Γ E (_ hs))
    ---------------------------
    (types Γ (! E) (#t  hs) ) ]

  [(types Γ E (#f hs))
    ---------------------------
    (types Γ (★ E) (#t  hs) ) ]
  
  [
   (element hs x #f)
    ---------------------------
    (types (x : (boolean hs) Γ) x (boolean hs)  ) ]

   [(types Γ x (boolean hs))
     (cheat x_1 x #f)
    ---------------------------
    (types (x_1 : _ Γ) x (boolean hs)  ) ]
  
  )

#;(define-metafunction TypedPegExp
  ⊗ : τ τ -> τ
  [(⊗ ( boolean hs) ( boolean_1 hs_1)) ( (∧ boolean  boolean_1) (∪ hs (⇒ boolean hs_1))) ]
  )

(define-metafunction TypedPegExp
  ⊗ : τ τ -> τ
  [(⊗ ( #f hs) ( boolean_1 hs_1)) ( (∧ #t  boolean_1) hs ) ]
  [(⊗ ( #t hs) ( boolean_1 hs_1)) ( (∧ #f  boolean_1) (∪ hs  hs_1)) ]
  )

(define-metafunction TypedPegExp
  ⊕ : τ τ -> τ
  [(⊕ ( boolean hs) ( boolean_1 hs_1)) ( (∨ boolean  boolean_1) (∪ hs hs_1) ) ]
  )

(define-metafunction TypedPegExp
  ≠ : any any -> boolean
  [(≠ x x) #f]
  [(≠ x x_1) #t]
  )

(define-metafunction TypedPegExp
  ⇒ : boolean hs -> hs
  [(⇒ #f _) ∅]
  [(⇒ #t hs) hs]
  )

(define-metafunction TypedPegExp
  ∨ : boolean boolean -> boolean
  [(∨ #f #f) #f]
  [(∨ _ _) #t]
  )

(define-metafunction TypedPegExp
  ∧ : boolean boolean -> boolean
  [(∧ #t #t) #t]
  [(∧ _ _) #f]
  )

(define-metafunction TypedPegExp
  ¬ : boolean -> boolean
  [(¬ #t) #f]
  [(¬ #f) #t]
  )

(define-metafunction TypedPegExp
  samevar : x x -> boolean
  [(samevar x x) #t]
  [(samevar x _) #f]
 )

(define-metafunction TypedPegExp
  same : x x boolean boolean -> boolean 
  [(same x   x boolean boolean_1) boolean]
  [(same x_1 x boolean boolean_1) boolean_1]
  )

(define-metafunction TypedPegExp
  ccons : boolean x hs -> hs
  [(ccons #t x hs) hs]
  [(ccons #f x hs) (x hs)]
  )

(define-metafunction TypedPegExp
  ∪ : hs hs -> hs
  [(∪ ∅ hs)   hs]
  [(∪ (x hs)  hs_1) (ccons (∈ x hs_1) x (∪ hs hs_1))]
  )

(define-metafunction TypedPegExp
  ∈ : x hs -> boolean
  [(∈ _ ∅) #f]
  [(∈ x (x _)) #t]
  [(∈ x (x_1 hs)) (∈ x hs)]
  )

(define-metafunction TypedPegExp
  ∉ : x hs -> boolean
  [(∉ x hs) (¬ (∈ x hs))]
  )


; A collection of very weird examples !
;
; > (generate-term TypedPegExp #:satisfying (types Γ x τ) 1)
; '(types (U : (#f (W ∅)) (d : (#t ∅) (E : (#t ∅) ∅))) U (#f (U (W ∅))))
; > (generate-term TypedPegExp #:satisfying (types Γ x τ) 1)
; '(types (U : (#t (E ∅)) ∅) U (#t (U (E ∅))))