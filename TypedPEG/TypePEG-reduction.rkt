#lang racket
(require redex)
(provide typing)

(define-language Peg
  [E (• E E)
     (/ E E)
     (* E)
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
  
  [hs (x ...)]
  [reduc (Γ G E)]
  [Γ ((x τ) ...)])

(define-extended-language  TypedPegExp Peg
  
  )

(define typing
  (reduction-relation 
   Peg
   #:domain reduc
   
   (--> (Γ G (in-hole C ε))
        (Γ G (in-hole C (#t ()))))

   (--> (Γ G (in-hole C natural))
        (Γ G (in-hole C (#f ()))))

   (--> (Γ G (in-hole C (• τ_1 τ_2)))
        (Γ G (in-hole C (⊗ τ_1 τ_2))))

   (--> (Γ G (in-hole C (/ τ_1 τ_2)))
        (Γ G (in-hole C (⊕ τ_1 τ_2))))

   (--> (Γ G (in-hole C (! (boolean hs))))
        (Γ G (in-hole C (#t hs))))

   (--> (Γ G (in-hole C (* (#f hs))))
        (Γ G (in-hole C (#t hs))))

   (--> (((x_1 τ_1)... (x (boolean hs)) (x_2 τ_2)...) G (in-hole C x))
        (((x_1 τ_1)... (x (boolean hs)) (x_2 τ_2)...) G (in-hole C (boolean (∪ (x) hs))))
        (where #f (∈ x hs))) ; colocar um type erro e discutir com o rodrigo
   )
  )


(define-metafunction TypedPegExp
  ⊗ : τ_1 τ_2 -> τ 
  [(⊗ (#f hs) ( boolean_1 hs_1))  ( (∧ #t  boolean_1) hs ) ]
  [(⊗ (#t hs) ( boolean_1 hs_1))  ( (∧ #f  boolean_1) (∪ hs  hs_1)) ])

(define-metafunction TypedPegExp
  ⊕ : τ τ -> τ
  [(⊕ ( boolean hs) ( boolean_1 hs_1)) ( (∨ boolean  boolean_1) (∪ hs hs_1) ) ])

(define-metafunction TypedPegExp
  ∨ : boolean boolean -> boolean
  [(∨ #f #f) #f]
  [(∨ _ _) #t])

(define-metafunction TypedPegExp
  ∧ : boolean boolean -> boolean
  [(∧ #t #t) #t]
  [(∧ _ _) #f])

(define-metafunction TypedPegExp
  ∪ : hs hs -> hs
  [(∪ () hs)   hs]
  [(∪ (x x_1 ...)  hs) (ccons (∈ x hs) x (∪ (x_1 ...) hs))])

(define-metafunction TypedPegExp
  ∈ : x hs -> boolean
  [(∈ _ ()) #f]
  [(∈ x (x x_1 ...)) #t]
  [(∈ x (x_1 x_2 ...)) (∈ x (x_2 ...))])

(define-metafunction TypedPegExp
  ccons : boolean x hs -> hs
  [(ccons #t x hs) hs]
  [(ccons #f x (x_1 ...)) (x x_1 ...)])

(define-metafunction TypedPegExp
  samevar : x x -> boolean
  [(samevar x x) #t]
  [(samevar x _) #f])

(display "1-")
(apply-reduction-relation* typing (term (() () ε)))
(display "2-")
(apply-reduction-relation* typing (term (() () 1)))
(display "3-")
(apply-reduction-relation* typing (term (() () (• 1 2))))
(display "4-")
(apply-reduction-relation* typing (term (() () (/ 1 2))))
(display "5-")
(apply-reduction-relation* typing (term (() () (! 1))))
(display "6-")
(apply-reduction-relation* typing (term (() () (* 1))))
(display "7-")
(apply-reduction-relation* typing (term (((A (#f (A)))) ((A 1)) A)))