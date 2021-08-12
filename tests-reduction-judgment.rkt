#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")
(require "./reduction.rkt")


(define (get-result l)

  (if (eq? (list-ref (car l) 7) 'suc)
      (list (list-ref (car l) 5))
      (list '⊥))

  )

;fazer uma meta funçao para verificar se uma gramatica é WF 
;(get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (1 3 3) () ⊥ (0)))


;(define (isWF ))



(display "\nTerminal\n")
(test-equal
 (judgment-holds (eval ∅ (1 (1 1 1)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () 1 ↓ (1 1 1) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ (1 (2 1 1)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () 1 ↓ (2 1 1) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ (1 ()) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () 1 ↓ () () ⊥ (0)))))
 )

(test-results)

(display "\nChoice\n")

(test-equal
 (judgment-holds (eval ∅ ((/ 1 2) (1 1 1)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (/ 1 2) ↓ (1 1 1) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((/ 1 2) (1 1 1)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (/ 1 2) ↓ (1 1 1) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((/ 1 2) (2 1 1)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (/ 1 2) ↓ (2 1 1) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((/ 1 2) ()) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (/ 1 2) ↓ () () ⊥ (0)))))
 )

(test-results)

(display "\nSequence\n")
(test-equal
 (judgment-holds (eval ∅ ((• 1 2) (1 2 3)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (1 2 3) () ⊥ (0)))))
 )
(test-equal
 (judgment-holds (eval ∅ ((• 1 2) (2 2 3)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (2 2 3) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((• 1 2) (1 1 3)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (1 1 3) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((• 1 2) ()) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ () () ⊥ (0)))))
 )

(test-results)

(display "\nNot\n")
(test-equal
 (judgment-holds (eval ∅ ((! 1) (1 2 3)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (! 1) ↓ (1 2 3) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((! (/ 1 2)) (1 2 3)) s) s)
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (! (/ 1 2)) ↓ (1 2 3) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((• (! 0) (• 1 2)) (1 2 3)) s) s) 
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (• (! 0) (• 1 2)) ↓ (1 2 3) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((/ (! (• 1 2)) (• 1 0)) (1 2 3)) s) s) 
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))))
 )


(test-results)

(display "\nRepetition\n")

(test-equal
 (judgment-holds (eval ∅ ((* 1) (1 1 1 1 2)) s) s) 
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (* 1) ↓ (1 1 1 1 2) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((* 1) (2)) s) s) 
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (* 1) ↓ (2) () ⊥ (0)))))
 )

(test-equal
 (judgment-holds (eval ∅ ((* 1) ()) s) s) 
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (* 1) ↓ () () ⊥ (0)))))
 )

(test-results)

(display "\nNon-terminal\n")

(test-equal
 (judgment-holds (eval (A (/ (• 0 (• A 1)) ε)
                          (B (/ (• 1 (• B 2)) ε)
                             (C (/ 0 (/ 1 2))
                                (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅)))) (S (0 1 2)) s) s)

 (get-result (apply-reduction-relation* red (term ((A (/ (• 0 (• A 1)) ε)
                                          (B (/ (• 1 (• B 2)) ε)
                                             (C (/ 0 (/ 1 2))
                                                (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                                       ⊢ () S ↓ (0 1 2) () ⊥ (0)))))
 )

(test-results)