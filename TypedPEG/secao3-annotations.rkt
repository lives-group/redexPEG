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
  [S (x...)]
  [b #t
     #f]
  [x variable-not-otherwise-mentioned]
  [ψ ((x τ)...)]
  [φ ((α (b S))...)]
  [ctx (ψ φ)])
