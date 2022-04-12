#lang racket

(require redex)
(require rackunit)
(require rackcheck)
(require peg-gen)
(require "../lang/peg.rkt")
(require "../lang/bigStepSemantics.rkt")
(require "../lang/smallStepSemantics.rkt")

(test-equal (judgment-holds (eval (B 1 (A B ∅)) (A (1 2 3 4 5 6 7)) s) s) (list (term (2 3 4 5 6 7))))
(test-results)


;; Testing with redex-check

#;(redex-check Peg ;; Name of a language 
               ;(G ⊢ (C ...) e ↓ (natural ...) () D (0)) ;; Pattern
               ;; Racket expression that returns a boolean 
               )


(define (get-result l)

  (if (eq? (list-ref (car l) 7) 'suc)
      (list (list-ref (car l) 5))
      (list '⊥))

  )

(define (getGrammar e)
  (car e)
  )

(define (getExpression e)
  (car (cdr e))
  )

(define-property test-judgm-reduct ([peg  (gen:peg 3 5 2)])
  ;(display (get-result (apply-reduction-relation* red (term (,(getGrammar peg) ⊢ () ,(getExpression peg) ↓ (1 2 3) () ⊥ (0))))))
  (check-equal?  (judgment-holds (eval ,(getGrammar peg) ,((getExpression peg) (1 2 3)) s) s)  
                 (get-result (apply-reduction-relation* red (term (,(getGrammar peg) ⊢ () ,(getExpression peg) ↓ (1 2 3) () ⊥ (0))))))
  )
(check-property (make-config #:tests 20) test-judgm-reduct)


   