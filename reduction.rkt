#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")
(provide (all-defined-out))

(define-extended-language Reduct Peg
  (C (/ C e)
     (• C e)
     (* C)
     (! C)
     hole))


(define red
  (reduction-relation 
   Reduct
   ;#:domain (C s)

   ;Choice relation
   (--> (in-hole C (natural_1 (natural_1 natural ...)))
        (in-hole C (natural ...))
        "Terminal")
   (--> (in-hole C (natural_1 (natural_2 natural ...)))
        (in-hole C ⊥)
        ;(side-condition (not (equal? (term natural_1) (term natural_2))))
        "Terminal ⊥")
   (--> (in-hole C (natural_1 ()))
        (in-hole C ⊥)
        "Terminal () ⊥")
   (--> (in-hole C ((/ e_1 e_2) (natural ...)))
        (in-hole C (e_1 (natural ...)))
        "Alternancia-1")
   (--> (in-hole C ((/ e_1 e_2) (natural_1 natural ...)))
        (in-hole C (e_2 (natural_1 natural ...)))
        "Alternancia-2")

   )
  )

(traces red (term ((/ 1 2) (1 2 3))))

