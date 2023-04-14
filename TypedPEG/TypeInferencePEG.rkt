#lang racket

(require redex)

(provide all-defined-out)

(define-language Peg
  (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Temrinal 
  (x variable-not-otherwise-mentioned))

(define-extended-language Typed-Peg Peg
  [τ α
     (b S)
     (× τ τ)
     (+ τ τ)
     (★ τ)
     (! τ)]
  [t x
     b
     S
     τ]
  [C true
     false
     (t ≡ t)
     (∧ C C C ...)
     (∃ α C)
     (def x : τ in C)]
  [α x 
     (v natural)]
  [constraint τ t C]
  [S (x ...) ∅]
  [b #t
     #f]
  [x variable-not-otherwise-mentioned]
  [ψ ((x τ)...)]
  [φ ((τ (b S))...)]
  [ctx (ψ φ)]
  [exp (e τ) ]
  [reduc (ctx constraint)]
  [hs (x hs)
      ∅])

(define-extended-language Inference Typed-Peg
  [state-exp (ψ φ exp)]
  [state (ψ φ constraint)]
  )

(define n 0)
(define (inc)
  (let ([x n])
    (begin (set! n (+ 1 n)) x)))

#;(define-metafunction Inference
    ⊕ : τ τ -> τ
    [(⊕ ( boolean hs) ( boolean_1 hs_1))
     ( (∨ boolean  boolean_1) (∪ hs hs_1) ) ])

#;(define-metafunction Inference
    ⊗ : τ τ -> τ
    [(⊗ ( #f hs) ( boolean_1 hs_1)) ( (AND #t  boolean_1) hs ) ]
    [(⊗ ( #t hs) ( boolean_1 hs_1)) ( (AND #f  boolean_1) (∪ hs  hs_1)) ])

#;(define-metafunction Inference
    ∨ : boolean boolean -> boolean
    [(∨ #f #f) #f]
    [(∨ _ _) #t])

#;(define-metafunction Inference
    AND : boolean boolean -> boolean
    [(AND #t #t) #t]
    [(AND _ _) #f])

#;(define-metafunction Inference
    ¬ : boolean -> boolean
    [(¬ #t) #t]
    [(¬ #f) #t])

#;(define-metafunction Inference
    ast : boolean -> boolean
    [(ast #t) (error)]
    [(ast #f) #t])

#;(define-metafunction Inference
    ∪ : hs hs -> hs
    [(∪ ∅ hs)   hs]
    [(∪ (x hs)  hs_1) (ccons (∈ x hs_1) x (∪ hs hs_1))])


; tc -> trivial-constraints
(define-metafunction Inference
  tc : e τ -> C
  [(tc ε τ) (τ ≡ (#t ∅))]

  [(tc natural τ) (τ ≡ (#f ∅))]

  [(tc x τ) (x ≡ τ)]

  [(tc (/ e_1 e_2) τ) (∧ (∃ α_1 (tc e_1 α_1))
                         (∃ α_2 (tc e_2 α_2))
                         (τ ≡ (+ α_1 α_2)))
                      (where α_1 ,(term (v ,(inc))))
                      (where α_2 ,(term (v ,(inc))))]

  [(tc (• e_1 e_2) τ) (∧ (∃ α_1 (tc e_1 α_1))
                         (∃ α_2 (tc e_2 α_2))
                         (τ ≡ (× α_1 α_2)))
                      (where α_1 ,(term (v ,(inc))))
                      (where α_2 ,(term (v ,(inc))))]

  [(tc (! e_1) τ) (∧ (∃ α_1 (tc e_1 α_1))
                         (τ ≡ (! α_1)))
                    (where α_1 ,(term (v ,(inc))))]

  [(tc (* e_1) τ) (∧ (∃ α_1 (tc e_1 α_1))
                     (τ ≡ (★ α_1)))
                    (where α_1 ,(term (v ,(inc))))])


(term (tc ε (#t ∅)))
(term (tc 1 (#f ∅)))
(term (tc A (#f ∅)))
(term (tc (/ 2 2) τ))
(term (tc (• 1 2) (#f ∅)))
(term (tc (! 1) (#f ∅)))
(term (tc (* 1) (#t ∅)))
;(term (tc (() () ((* ε) (#t ∅))))) ; dá erro, mas é pra dar!
