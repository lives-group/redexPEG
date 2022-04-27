#lang racket

(require redex)
(require rackunit)
(require rackcheck)
(require peg-gen)
(require "../lang/peg.rkt")
(require "../lang/bigStepSemantics.rkt")
(require "../lang/smallStepSemantics.rkt")


;; Testing with redex-check

#;(redex-check Peg                                         ;; Name of a language 
               ;(G ⊢ (C ...) e ↓ (natural ...) () D (0))   ;; Pattern
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

(define (gen:listNat n k)
  (if (eq? n 0) (gen:bind (gen:integer-in 0 k) (lambda (e) (gen:const (list e))) )
      (gen:bind (gen:listNat (- n 1) k)
                (lambda (xs) (gen:bind ( gen:integer-in 0 k)
                                       (lambda (x) (gen:const (list* x xs)) ) ))))
  )


;3 - numero de variaveis
;5 - numero de terminais
;2 - profundidade
(define-property test-judgm-reduct ([peg (gen:peg 3 5 2)]
                                    [n (gen:integer-in 0 10)]
                                    [input (gen:listNat n 5)])
  (check-equal?  (judgment-holds (eval ,(getGrammar peg) (,(getExpression peg) ,input) s) s)  
                 (get-result (apply-reduction-relation* red (term (,(getGrammar peg) ⊢ () ,(getExpression peg) ↓ ,input () ⊥ (0))))))
  )
(check-property (make-config #:tests 10000) test-judgm-reduct)


;(check-property (make-config #:tests 100000 #:deadline (+ (current-inexact-milliseconds) 3600000)) test-judgm-reduct)
