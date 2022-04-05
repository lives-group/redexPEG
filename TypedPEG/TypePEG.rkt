#lang racket
(require redex)

(define-language Peg
   [E (• E E)
      (/ E E)
      (★ E)
      (¬ E)
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
    (types Γ (¬ E) (#t  hs) ) ]

  [(types Γ E (#f hs))
    ---------------------------
    (types Γ (★ E) (#t  hs) ) ]
  
  [(types Γ x (boolean hs) )
   (side-condition (∉ x hs))
    ---------------------------
    (types Γ x (boolean hs)  ) ]

  
  )


(define-metafunction TypedPegExp
  ⊗ : τ τ -> τ
  [(⊗ ( boolean (x ...)) ( boolean_1 (x_1 ...))) ( (∧ boolean  boolean_1) (∪ (x ...) (⇒ boolean (x_1 ...)))) ]
  )

(define-metafunction TypedPegExp
  ⊕ : τ τ -> τ
  [(⊕ ( boolean (x ...)) ( boolean_1 (x_1 ...))) ( (∨ boolean  boolean_1) (∪ (x ...) (x_1 ...)) ) ]
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
  [(∧ _ _) #t]
  )

(define-metafunction TypedPegExp
  ∪ : hs hs -> hs
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
  [(∉ x hs) ,(not (term (∈ x hs)) )]
  )
