#lang racket
(require redex)
(require "./peg.rkt")
(require "./reduction.rkt")
(display "Testes\n")

(test-->> red
          (term (∅ ⊢ () (! (• 1 3)) ↓ (1 2 3) () ⊥ (0)))
          (term (∅ ⊢ () (! (• 1 3)) ↑ (1 2 3) () suc (0)))
)

(test-->> red
          (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))
          (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↑ (1 2 3) () ⊥ (0)))
)

(test-->> red
          (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0)))
          (term (∅ ⊢ () (* (• 1 2)) ↑ (1 3) (2 1 2 1 2 1) suc (0)))
)

(test-->> red
          (term (∅ ⊢ () (• (• 1 2) (! 0)) ↓ (1 2 3) () ⊥ (0)))
          (term (∅ ⊢ () (• (• 1 2) (! 0)) ↑ (3) (2 1) suc ((⊕ (⊕ 0)))))
)

#;(test-->> red 
          (term (   (A (/ (• 0 (• A 1)) ε)
                    (B (/ (• 1 (• B 2)) ε)
                    (C (/ 0 (/ 1 2))
                    (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                    ⊢ () S ↓ (0 1 2) () ⊥ (0)))
          (term
))
(test-results)
#|
pq
 (traces red (term ((A (/ (• 0 (• A 1)) ε)
                    (B (/ (• 1 (• B 2)) ε)
                    (C (/ 0 (/ 1 2))
                    (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                    ⊢ () S ↓ (0 1 2) () ⊥ (0))))

da resultado diferente de 
(apply-reduction-relation* red (term ((A (/ (• 0 (• A 1)) ε)
                    (B (/ (• 1 (• B 2)) ε)
                    (C (/ 0 (/ 1 2))
                    (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                    ⊢ () S ↓ (0 1 2) () ⊥ (0))))
|#