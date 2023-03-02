#lang racket
(require redex)

(define-language Peg
  [E (• E E)
     (/ E E)
     (★ E)
     (! E)
     x
     natural
     ε
     τ]
  [C (• C E)
     (• τ C)
     (/ C E)
     (/ τ C)
     (* C)
     (! C)
     hole
     ]
  [x variable-not-otherwise-mentioned]
  [G ((x E) ... )]
  [P (G E)]
  
  [τ  (boolean hs)]
  [hs (x ...)
      ∅]
  [Γ ∅ (x : τ Γ)]
  )

(define-extended-language  TypedPegExp Peg
  
  )

(define typing
  (reduction-relation 
   Peg  

   (--> (in-hole C (Γ ε))
        (in-hole C (#t ∅)))
   (--> (in-hole C (Γ natural))
        (in-hole C (#f ∅)))
   (--> (in-hole C (Γ (• τ_1 τ_2)))
        (in-hole C (⊗ τ_1 τ_2)))
   (--> (in-hole C (Γ (/ τ_1 τ_2)))
        (in-hole C (⊕ τ_1 τ_2)))
   (--> (in-hole C (Γ (! (boolean hs))))
        (in-hole C (#t hs)))
   (--> (in-hole C (Γ (* (#f hs))))
        (in-hole C (#t hs)))
   (--> (in-hole C ((x_1 : (boolean hs) Γ) x_2))
        (in-hole C (boolean (∪ hs (x_1))))
        (side-condition (and (term (samevar x_1 x_2))
                              (not (term (∈ x_1 hs))))))

   )
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
  ccons : boolean x hs -> hs
  [(ccons #t x hs) hs]
  [(ccons #f x hs) (x hs)]
  )

(define-metafunction TypedPegExp
  samevar : x x -> boolean
  [(samevar x x) #t]
  [(samevar x _) #f]
 )


(apply-reduction-relation* typing (term (∅ ε)))
(apply-reduction-relation* typing (term (∅ 1)))
(apply-reduction-relation* typing (term (∅ (• 1 2))))
(apply-reduction-relation* typing (term (∅ (/ 1 2))))
(apply-reduction-relation* typing (term (∅ (! 1))))
(apply-reduction-relation* typing (term (∅ (* 1))))
(apply-reduction-relation* typing (term ((A : (#f ∅) ∅) A)))