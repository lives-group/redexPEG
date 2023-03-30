#lang racket

(require redex)
(require rackunit)
(require rackcheck)
(require peg-gen)
(require "../lang/peg.rkt")
(require "../lang/bigStepSemantics.rkt")
(require "../lang/smallStepSemantics.rkt")

(require rackcheck
         typed-peg/core
         typed-peg/typing/infer
         typed-peg/typing/type
         typed-peg/typing/constraint
         typed-peg/tree
         rackunit)


(apply-reduction-relation* red (term (∅ ⊢ () 1 ↓ (1 2 3) () ⊥ (0))))


(define (getGrammar e)
  (car e)
  )

(define (getExpression e)
  (car (cdr e))
  )


;(check-property wellformed-ford)
;(check-property (make-config #:tests 20) wellformed-ford)
(define-property wellformed-ford ([peg  (gen:peg 10 10 4)])
  
  (define grammar (getGrammar peg))
  (define exp (getExpression peg))
  (println exp)
  (define test (term (,grammar ⊢ () ,exp ↓ (1 2 3) () ⊥ (0))))
  (define result (apply-reduction-relation* red test))
  (define expResult (list-ref (car result) 3))
  (println expResult)
  (define arrow (list-ref (car result) 4))
  (and (eq? arrow '↑) (eq? expResult exp))
  (display "\n")
  )