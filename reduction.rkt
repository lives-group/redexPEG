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
   
   ;Terminal
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

   ;Empty
   (--> (in-hole C (ε natural ...))
        (in-hole C (natural ...))
        "Empty")

   ;Choice
   (--> (in-hole C ((/ e_1 e_2) (e_1 natural ...)))
        (in-hole C ((/ e_1 e_2) (natural ...)))
        "Alternancia-1")

   (--> (in-hole C ((/ e_1 e_2) (e_2 natural ...)))
        (in-hole C ((/ e_1 e_2) (natural ...)))
        "Alternancia-2")
   
   (--> (in-hole C ((/ e_1 e_2) (e_3 natural ...))) ;caso nao haja mais matches mas ta fazendo coisa que nao precisa 
        (in-hole C (e_3 natural ...))
        "Alternancia-3") 
   
   ;Sequence

   (--> (in-hole C ((• e_1 e_2) (e_1 e_2 natural ...)))
        (in-hole C ((• e_1 e_2) (e_2 natural ...)))
        "Sequencia-1")

   (--> (in-hole C ((• e_1 e_2) (e_1 e_2 natural ...)))
        (in-hole C ((• e_1 e_2) (natural ...)))
        "Sequencia-2")

   (--> (in-hole C ((• e_1 e_2) (e_3 natural ...)))
        (in-hole C (e_3 natural ...))
        "Sequencia-3")

   

   ;Repetition

   (--> (in-hole C ((* e_1) (e_1 natural ...)))
        (in-hole C ((* e_1) (natural ...)))
        "Repetition-1")

   (--> (in-hole C ((* e_1) (e_2 natural ...)))
        (in-hole C (e_2 natural ...))
        "Repetition-2"
        ;(side-condition (diff? e_1 e_2)) ;como usa side contidion
        )
   )
  )
(define-metafunction Reduct
  [(diff? e_1 e_2) #t]
  [(diff? e_1 e_1)     #f])
;Choice
;(traces red (term ((/ 1 2) (1 2 3))))
;(traces red (term ((/ 1 2) (3 3 3))))

;Sequence
;(traces red (term ((• 1 2) (1 2 3))))

;Repetition
(traces red (term ((* 1) (1 1 1 1 2))))
