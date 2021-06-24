#lang racket
(require redex)
(require "./peg.rkt")
;(require "./judgments.rkt")
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
   ;#:domain C 
   ;Choice relation
   (--> (in-hole C (/ e_1 e_2))
       ; (side-condition (equal? e_1 s))
        (in-hole C e_1)
        "Choice-fst")
;nao sei como eu coloco a entrada


   )
  )

