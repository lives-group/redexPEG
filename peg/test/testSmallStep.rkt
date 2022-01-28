#lang racket

(require redex)
(require "../lang/peg.rkt")
(require "../lang/smallStepSemantics.rkt")


(display "Tests of the small-step semantics \n")

(define (tests-reduction)
  ;TERMINAL
  (test-->> red
            (term (∅ ⊢ () 1 ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () 1 ↑ (2 3) (1) suc (1))))
  ;CHOICE + (REPETION + TERMINAL)
  (test-->> red
            (term (∅ ⊢ () (/ (* 1) 1) ↓ (1 1 1 1 2) () ⊥ (0)))
            (term (∅ ⊢ () (/ (* 1) 1) ↑ (2) (1 1 1 1) suc (4))))
  ;NOT + SEQUENCE
  (test-->> red
            (term (∅ ⊢ () (! (• 1 3)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (! (• 1 3)) ↑ (1 2 3) () suc (0)))
            )
  ;CHOICE + ((NOT + SEQUENCE) + SEQUENCE)
  (test-->> red
            (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↑ (1 2 3) () ⊥ (0)))
            )
  ;REPETION + SEQUENCE
  (test-->> red
            (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0)))
            (term (∅ ⊢ () (* (• 1 2)) ↑ (1 3) (2 1 2 1 2 1) suc (6)))
            )
  ;SEQUENCE + (SEQUENCE + NOT)
  (test-->> red
            (term (∅ ⊢ () (• (• 1 2) (! 0)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (• (• 1 2) (! 0)) ↑ (3) (2 1) suc (2))))

  ;NON-TERMINAL 
  (test-->> red 
            (term ((A (/ (• 0 (• A 1)) ε)
                      (B (/ (• 1 (• B 2)) ε)
                         (C (/ 0 (/ 1 2))
                            (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                   ⊢ () S ↓ (0 1 2) () ⊥ (0)))
            (term ((A
                    (/ (• 0 (• A 1)) ε)
                    (B
                     (/ (• 1 (• B 2)) ε)
                     (C
                      (/ 0 (/ 1 2))
                      (S
                       (•
                        (! (! A))
                        (• (* 0) (• B (! C))))
                       ∅))))
                   ⊢ () S ↑ () (2 1 0) suc (3))))
  (test-results))


(tests-reduction)

(define (reduction-right? exp)
  (= 1 (length (apply-reduction-relation red exp)))
  )




