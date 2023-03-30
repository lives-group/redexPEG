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
     (b S)]
  [t x
     b
     S
     τ]
  [C true
     false
     (t ≡ t)
     (C ∧ C)
     (∃α.C)
     (def x : τ in C)]
  [α x]
  [constraint τ t C]
  [S (x ...) ∅]
  [b #t
     #f]
  [x variable-not-otherwise-mentioned]
  [ψ ((x τ)...)]
  [φ ((τ (b S))...)]
  [ctx (ψ φ)]
  [exp (e τ) ]
  [reduc (ctx constraint)])

(define-extended-language Inference Typed-Peg
  [state-exp (ψ φ exp)]
  [state (ψ φ constraint)]
  )

; tc -> trivial-constraints
(define-metafunction Inference
  [(tc (ψ φ (ε τ))) (ψ φ (τ ≡ (#t ∅))) ]
  [(tc (ψ φ (natural τ))) (ψ φ (τ ≡ (#f ∅))) ]
  [(tc (ψ φ (x τ))) (ψ φ (x ≡ τ)) ]
  [(tc (ψ φ ((/ e e) τ))) (ψ φ (x ≡ τ)) ]
  [(tc (ψ φ ((/ e_1 e_2) τ))) (ψ φ (x ≡ τ)) ]
   ∃α_1.e_1 : α1 ∧ ∃α2.e2 : α2 ∧τ ≡ α1 ⊕α2
  )



(term (tc (() () (ε (#t ∅)))))
(term (tc (() () (1 (#f ∅)))))
(term (tc (() () (A (#f ∅)))))

