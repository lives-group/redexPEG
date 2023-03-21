#lang racket

#|
 X -> restrição ou tipo
 X barra -> sequeência de elementos
 X1 barra ∩ X2 barra = 0
 • -> mapeamento finito vazio
 m -> mapeamento finito
 m[x ↦ y] -> inserção/update de m com a chave x para o valor y
 p::m -> p = [x ↦ y] e m é um mapeamento qualquer

 t -> termo: não terminal (A)
             booleano (b)
             conjunto de não terminais (S)
             tipo (τ)
 τ -> variável de tipo (α)
      tipo concreto <b, S>

 C -> formula atomica: true
                       false
                       equação entre termos (t ≡ t)
                       conjunção (C ∧ C) 
                       quantificação existencial (∃α.C )
                       definição de tipo para não terminal (def A : τ in C)

 ψ -> mapeamento entre não terminal e seus respectivos tipos
 φ -> mapeamento entre variável de tipo e grond type
 ψ, φ ⊢ C ->  under the environments ψ and φ the constraint C holds
 uma restrição C é satisfeita se existe ψ  e φ tq ψ, φ ⊢ C
 duas restrições são equivalentes (C1 ≈ C2) se ∀ψ φ.ψ, φ ⊢ C1 ↔ ψ, φ ⊢ C2



|#


(require redex)

(provide Typed-Peg)

(define-language Typed-Peg
  [τ α
     ((b S)...)]
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
  [constraint τ t C]
  [S (x...)]
  [b #t
     #f]
  [x variable-not-otherwise-mentioned]
  [ψ ((x τ)...)]
  [φ ((τ (b S)) ...)]
  [ctx (ψ φ)]
  [reduc (ctx constraint)])

(define-judgment-form
  Typed-Peg
  #:mode (semantics I I I)
  #:contract (semantics ψ φ constraint)

  [ ---------------------------
    (semantics ψ φ #t ) ]

  [(side-condition (equalφ (b_2 S_2) (b_3 S_3)))
   (side-condition (equalτ τ τ_3))
   (side-condition (equalτ τ_2 τ_4))
   ---------------------------
   (semantics ψ ((τ (b_2 S_2))
                  (τ_1 (b_1 S_1))
                  (τ_2 (b_3 S_3)) ) (τ_3 ≡ τ_4) ) ]

  )


(define-metafunction Typed-Peg
  equalφ : (b S) (b S) -> boolean
  [(equalφ (b S) (b S)) #t]
  [(equalφ (b S) _) #f])

(define-metafunction Typed-Peg
  equalτ : τ τ -> boolean
  [(equalτ τ τ) #t]
  [(equalτ τ _) #f])


(define typing
  (reduction-relation 
   Typed-Peg
   #:domain reduc
   
   (--> (ctx true)
        (ctx #t))
   
   (--> ((ψ φ) (τ_1 ≡ τ_2))
        (ctx #t))
   )
  )
