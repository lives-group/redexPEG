#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")
(provide (all-defined-out))

(define-extended-language Reduct Grammar 
  (C (/ C e)
     (/ e C)
     (• C e)
     (• e C)
     (* C)
     (! C)
     h)
  (D ⊥
     suc)
  (nat 0
       (⊕ nat))
  (dir ↑
       ↓)
  (state ((C ...) e dir s s D nat))  
  ;s1 lista de marcas, pontos da entrada que a gnt marcou
  ;s2 oq a gnt viu da entrada (consumiu)
  )
;seta pra cima - saindo da expressão - finalizou a analise
;seta pra baixo: entrando

;dir -> setinha
;state é o input e o output da red

(define red
  (reduction-relation 
   Reduct
   
   ;Terminal
   
   (--> ((C ...) natural_1 ↓ (natural_1 natural_2 ...) (natural_3 ...) D nat)
        ((C ...) natural_1 ↑ (natural_2 ...) (natural_1 natural_3 ...) suc (⊕ nat) )
        "Terminal")
   (--> ((C ...) natural_1 ↓ (natural_2 natural ...) s_1 D nat)
        ((C ...) natural_1 ↑ (natural_2 natural ...) s_1 ⊥ nat)
        (side-condition (term (diff? natural_1 natural_2)))      ;o resultado é um boolean
        "Terminal ⊥")
   (--> ((C ...) natural_1 ↓ () s_1 D nat)
        ((C ...) natural_1 ↑ () s_1 ⊥ nat)
        "Terminal () ⊥")

   ;Empty
   (--> ((C ...) ε ↓ (natural ...) s_1 D nat)
        ((C ...) ε ↑ (natural ...) s_1 suc nat)
        "Empty")
   #|
   quando falhar, a gnt tem que voltar até o nat ser 0.
quando ele ta saindo com bot ou entrando, vai voltando ate chegar na setinha pra baixo com 0.
faz voltar com a redução
quando tiver oplus, tira o oplus, tira de uma lista e coloca no começo da outra, até ter 0 no nat
ai muda a setinha pra cima e ver se da certo ou errado
|#
   ;Choice
   ;esquerdo deu certo: 
   (--> ((C ...) (/ e_1 e_2) ↓ (natural_1 ...) (natural ...) D nat)
        (((/ h e_2) C ...) e_1 ↓ (natural_1 ...) (natural ...) D nat) ;h serve tentar e e_2 para memorizar
        "Alternancia-1")

   (--> (((/ h e_2) C ...) e_1 ↑ (natural ...) (natural ...) suc (⊕ nat)) 
        ((C ...) (/ e_1 e_2) ↑ (natural ...) (natural ...) suc (⊕ nat))
        "Alternancia-1.1")
   
   (--> (((/ h e_2) C ...) e_1 ↑ (natural ...) s_1 ⊥ nat) 
        (((/ e_1 h) C ...) e_2 ↓ (natural ...) s_1 ⊥ nat)
        "Alternancia-1.2")
   
   (--> (((/ e_1 h) C ...) e_2 ↑ (natural ...) (natural ...) suc (⊕ nat)) 
        ((C ...) (/ e_1 e_2) ↑ (natural ...) (natural ...) suc (⊕ nat))
        "Alternancia-1.3")

   (--> (((/ e_1 h) C ...) e_2 ↑ (natural ...) s_1 ⊥ nat) 
        ((C ...) (/ e_1 e_2) ↑ (natural ...) s_1 ⊥ nat)
        "Alternancia-1.4")

   #|
   ;Sequence

   (--> ((C ...) (• e_1 e_2) ↓ (natural ...) D nat)
        (((• h e_2) C ...) e_1 ↓ (natural ...) D nat)
        "Sequencia-1")
   ;saindo do e_1 deu bom
   (--> (((• h e_2) C ...) e_1 ↑ (natural ...) suc)
        (((• e_1 h) C ...) e_2 ↓ (natural ...) suc)
        "Sequencia-2")
   
   ;saindo do e_1 deu ruim
   (--> (((• h e_2) C ...) e_1 ↑ (natural ...) ⊥)
        ((C ...) (• e_1 e_2) ↑ (natural ...) ⊥)
        "Sequencia-2.2")
   
   ;saindo do e_2 deu bom
   (--> (((• e_1 h) C ...) e_2 ↑ (natural ...) suc)
        ((C ...) (• e_1 e_2) ↑ (natural ...) suc)
        "Sequencia-3")
   ;saindo do e_2 deu ruim
   (--> (((• e_1 h) C ...) e_2 ↑ (natural ...) ⊥)
        ((C ...) (• e_1 e_2) ↑ (natural ...) ⊥)
        "Sequencia-3.3")

   

   ;Repetition

   (--> (in-hole (C ...)((* e_1) (e_1 natural ...)))
        (in-hole (C ...)((* e_1) (natural ...)))
        "Repetition-1")

   (--> (in-hole (C ...)((* e_1) (e_2 natural ...)))
        (in-hole (C ...)(e_2 natural ...))
        "Repetition-2"
        ;(side-condition (diff? e_1 e_2)) ;como usa side contidion
        )|#
   )
  )
(define-metafunction Reduct
  [(diff? e_1 e_1)     #f]
  [(diff? e_1 e_2)     #t])

;(display "\nAlternancia\n")
;(traces red (term (() 1 ↓ (1 2 3) () ⊥ 0)))
;(traces red (term (() 1 ↓ (2) suc)))
;(traces red (term (() 1 ↓ () suc)))
#|
(display "\nAlternancia\n")
(stepper red (term (() (/ 1 2) ↓ (1 2) ⊥)))
(stepper red (term (() (/ 1 2) ↓ (2 1) ⊥)))
(stepper red (term (() (/ 1 2) ↓ (3 1) ⊥)))
|#
;(stepper red (term (() (• 1 2) ↓ (1 2 3) ⊥)))
;(stepper red (term (() (/ (• 1 2) (• 1 3)) ↓ (1 3 3) ⊥))) ;dá errado pq ele n salva a entrada inicial

;Choice
(traces red (term (() (/ 1 2) ↓ (1 2 3) () ⊥ 0)))
(traces red (term (() (/ 1 2) ↓ (2 3) () ⊥ 0)))
;(traces red (term ((/ 1 2) (1 2 3))))
;(traces red (term ((/ 1 2) (3 3 3))))

;Sequence
;(traces red (term ((• 1 2) (1 2 3))))

;Repetition
;(traces red (term ((* 1) (1 1 1 1 2))))
