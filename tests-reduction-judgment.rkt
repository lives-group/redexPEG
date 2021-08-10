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
;(get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (1 3 3) () ⊥ (0)))))

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
 (judgment-holds (eval ∅ ((* 1) ()) s) s) ;judgment retornando '(())
 (get-result (apply-reduction-relation* red (term (∅ ⊢ () (* 1) ↓ () () ⊥ (0)))))
 )

(test-results)
