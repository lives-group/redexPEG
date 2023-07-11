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

(require "./TypeInferencePEG-refactor-2.rkt")
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
  (inferType (get-G l) (get-expression l))
  )

(define (constraint-from-peggen peggen)
    (genConstraint (get-G peggen) (get-expression peggen))
  )


(define (findTrue l)
  (cond [(eq? l '()) #f]
        [else (or (last (car l)) (findTrue (cdr l)))]
        )
  )

(define-property type-checks([peg  (gen:peg 3 5 2)])
  (println peg)
  (check-equal?  (testgen peg) (findTrue (teste peg)) )
  )

(define-property simple-check ([peg  (gen:peg 3 2 2)])
  (println peg)
  (findTrue (teste peg)) 
  )


(check-property (make-config #:tests 15) type-checks)

;(teste (last (sample (gen:peg 2 2 3) 1)))

;(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ())))))


;peg = ((Q (• A J) (A (• ε 0) (J (• ε ε) ∅)))
;       (/ A 0)
;       ((J #t ()) (A #f ()) (Q #f (A))))

;peg = ((N (* (/ 0 2)) (A (/ (/ 2 0) (• N 2)) ∅)) (/ (• 1 ε) (• 2 ε)) ((A #f (N)) (N #t ())))
;peg = ((N (* (/ 0 2)) ∅) (• 1 ε) ( (N #t ())))