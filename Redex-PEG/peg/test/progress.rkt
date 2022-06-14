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

(define (getGrammar e)
  (car e))

(define (getExpression e)
  (car (cdr e)))

(define (gen:listNat n k)
  (if (eq? n 0) (gen:bind (gen:integer-in 0 k) (lambda (e) (gen:const (list e))) )
      (gen:bind (gen:listNat (- n 1) k)
                (lambda (xs) (gen:bind ( gen:integer-in 0 k)
                                       (lambda (x) (gen:const (list* x xs))))))))

(define Σ 5)
(define-property progress ([peg  (gen:peg 3 Σ 3)]
                                  [n (gen:integer-in 0 Σ)]
                                  [input (gen:listNat n 5)])

  (define result (apply-reduction-relation* red 
                                            (term (,(getGrammar peg) ⊢ () ,(getExpression peg) ↓ ,input () ⊥ (0)))))
  (and
     (equal? (list-ref (car result) 4) 
          '↑) 
     (equal? (list-ref (car result) 3)
          (getExpression peg))))

(check-property (make-config #:tests 500) progress)


  
  



