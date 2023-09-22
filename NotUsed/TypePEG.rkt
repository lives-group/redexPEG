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
   [G ((x E) ... )]
   [P (G E)]
   )

(define-extended-language  TypedPegExp Peg
  [hs (x ...)
      ∅]
  [τ  (boolean hs)]
  [Γ ∅ (x : τ Γ)]
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
   (side-condition (∉ x hs))
    ---------------------------
    (types (x : (boolean hs) Γ) x (boolean hs)  ) ]

   [(types Γ x (boolean hs))
     (side-condition (∉ x hs))
     (side-condition (≠ x_1 x))
    ---------------------------
    (types (x_1 : _ Γ) x (boolean hs)  ) ]
  
  )


(define-metafunction TypedPegExp
  ⊗ : τ τ -> τ
  [(⊗ ( boolean hs) ( boolean_1 hs_1)) ( (∧ boolean  boolean_1) (∪ hs (⇒ boolean hs_1))) ]
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
  ∪ : hs hs -> hs
  [(∪ ∅ ∅ ) ∅]
  [(∪ () () ) ∅]
  [(∪ ∅ (x_2 ...) ) (x_2 ...)]
  [(∪ () (x_2 ...) ) (x_2 ...)]
  [(∪ (x_1 ...) ∅)  (x_1 ...)]
  [(∪ (x_1 ...) ())  (x_1 ...)]
  [(∪ (x_1 ...) (x_2 ...)) ,(set-union (term (x_1 ...)) (term (x_2 ...)) ) ]
  )

(define-metafunction TypedPegExp
  ∈ : x hs -> boolean
  [(∈ _ ∅) #f]
  [(∈ _ ()) #f]
  [(∈ x x) #t]
  [(∈ x x_1) #f]
  [(∈ x (x x_2 ...)) #t]
  [(∈ x (x_1 x_2 ...)) (∈ x (x_2 ...))]
  )

(define-metafunction TypedPegExp
  ∉ : x hs -> boolean
  [(∉ x hs) (¬ (∈ x hs))]
  )
