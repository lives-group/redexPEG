#lang racket

(require typed-peg/core
         typed-peg/typing/infer
         typed-peg/typing/type
         typed-peg/typing/constraint
         typed-peg/tree
         peg-gen
         rackcheck
         rackunit
         redex)

(require "./TypeInferencePEG.rkt")
(require "./TestsTypedPeg.rkt")


(define (get-G l)
  (import-gen-grm (car l)))

(define (get-expression l)
  (cadr l))

(define (get-type l)
  (caddr l))


(define (import-gen-grm l)
  (match l
    ['∅  null]
    [(list v e g) (cond
                    [(symbol? v) (cons (cons v (list e)) (import-gen-grm g))]
                    [else (error "Error while converting from random generated peg") ])]
    )
  )


(define (teste l)
  #;(apply-reduction-relation*
     constraint-solve
     (term (() ,(get-G l) (tc ,(get-expression l) (#f ())))))
  ;(term (() ,(get-G l) (tc ,(get-expression l) ())))
  (inferType (get-G l) (get-expression l))
  )


(define (findTrue l)
  (cond [(eq? l '()) #f]
        [(eq? (last (car l)) 'true) #t]
        [else (findTrue (cdr l))]
        )
  )

(define-property type-checks([peg  (gen:peg 3 5 2)])
  (println peg)
  (check-equal?  (testgen peg) (findTrue (teste peg)) )
  )

;(check-property (make-config #:tests 5) type-checks)

;(teste (last (sample (gen:peg 2 2 3) 1)))

;(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ())))))









#|


(term (tc ε (#t ∅)))
(term (tc 1 (#f ∅)))
(term (tc A (#f ∅)))
(term (tc (/ 2 2) τ))
(term (tc (• 1 2) (#f ∅)))
(term (tc (! 1) (#f ∅)))
(term (tc (* 1) (#t ∅)))
;(term (tc (() () ((* ε) (#t ∅))))) ; dá erro, mas é pra dar!
(term (tc (• (/ 1 3) 2) (#f ∅)))
(term (tc (* (/ 1 2)) (#f ∅)))
(term (tc (! (* (/ 1 2))) (#f ∅)))


(term (gc ∅ (#t ∅)))
(term (gc () (#t ∅)))
(term (gc ((A 1)) (#t ∅)))




(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc 1 (#f ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc A (#f ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc (/ 2 2) τ))))
(apply-reduction-relation* constraint-solve (term (() () (tc (* 2) τ))))



(define-metafunction Typed-Peg
  ∪ : φ (τ (b S)) -> φ
  [(∪ () (τ (b S)))   ((τ (b S)))]
  [(∪ ((τ_1 (b_1 S_1)) (τ_2 (_ _)) ...)  (τ (b S)))
   (ccons (∈ τ ((τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...))
          (τ (b S))
          (∪ ((τ_2 (b_2 S_2)) ...) (τ (b S))))])

(define-metafunction Typed-Peg
  ∈ : τ φ -> boolean
  [(∈ _ ()) #f]
  [(∈ τ ((τ (b_1 S_1)) (τ_2 (b_2 S_2)) ...)) #t]
  [(∈ τ ((τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...)) (∈ τ ((τ_2 (b_2 S_2)) ...))])


(define-metafunction Typed-Peg
  ccons : boolean (α τ) φ -> φ
  [(ccons #t (α τ) ((α_1 τ_1)... (α_2 τ_2) (α_3 τ_3) ...))
   ((α_1 τ_1)... (α_2 τ) (α_2 τ_3) ...)]
  [(ccons #f (α τ)
          ((α_1 τ_1) (α_2 τ_2) ...))
   ((α τ) (α_1 τ_1) (α_2 τ_2) ...)])

(define-metafunction Typed-Peg
  samevar : τ τ -> boolean
  [(samevar τ τ) #t]
  [(samevar τ _) #f])
|#
