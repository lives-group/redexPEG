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
     (NT x)
     h)
  (D ⊥
     suc)
  (nat 0
       (⊕ nat))
  (dir ↑
       ↓)
  (state (G ⊢ (C ...) e dir s s D (nat ...)))  
  ;s1 lista de marcas, pontos da entrada que a gnt marcou
  ;s2 oq a gnt viu da entrada (consumiu)
  )
;seta pra cima - saindo da expressão - finalizou a analise
;seta pra baixo: entrando

;dir -> setinha
;state é o input e o output da red

;nat ser transformado em uma lista de numeros
;quando aparecer um choice, colocar um 0 na frente
;quando sair do choice com sucesso, tira o topo da lista

(define red
  (reduction-relation 
   Reduct
   
   ;Terminal
   
   (--> (G ⊢ (C ...) natural_1 ↓ (natural_1 natural_2 ...) (natural_3 ...) D (nat_1 nat_2 ...))
        (G ⊢ (C ...) natural_1 ↑ (natural_2 ...) (natural_1 natural_3 ...) suc ((⊕ nat_1) nat_2 ...))
        "Terminal")

   (--> (G ⊢ (C ...) natural_1 ↓ (natural_2 natural ...) s_1 D (nat ...))
        (G ⊢ (C ...) natural_1 ↑ (natural_2 natural ...) s_1 ⊥ (nat ...))
        (side-condition (term (diff? natural_1 natural_2)))      ;o resultado é um boolean
        "Terminal ⊥")

   (--> (G ⊢ (C ...) natural_1 ↓ () s_1 D (nat ...))
        (G ⊢ (C ...) natural_1 ↑ () s_1 ⊥ (nat ...))
        "Terminal () ⊥")

   ;Empty
   (--> (G ⊢ (C ...) ε ↓ (natural ...) s_1 D (nat ...))
        (G ⊢ (C ...) ε ↑ (natural ...) s_1 suc (nat ...))
        "Empty")
   #|
   quando falhar, a gnt tem que voltar até o (nat ...) ser 0.
quando ele ta saindo com bot ou entrando, vai voltando ate chegar na setinha pra baixo com 0.
faz voltar com a redução
quando tiver oplus, tira o oplus, tira de uma lista e coloca no começo da outra, até ter 0 no (nat ...)
ai muda a setinha pra cima e ver se da certo ou errado
|#
   ;Choice
   ;esquerdo deu certo: 
   (--> (G ⊢ (C ...) (/ e_1 e_2) ↓ (natural_1 ...) (natural ...) D (nat ...))
        (G ⊢ ((/ h e_2) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (0 nat ...)) ;h serve tentar e e_2 para memorizar
        "Alternancia-Entra")

   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural_1 ...) (natural_2 ...) suc (nat_1 nat_2 ...)) ;nat1 vai virar o quanto a gnt consumiu no e_1
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural_1 ...) (natural_2 ...) suc (nat_2 ...) nat_1)
        "Alternancia-SUC-first")
   
   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural ...) s_1 ⊥ (0 nat ...)) 
        (G ⊢ ((/ e_1 h) C ...) e_2 ↓ (natural ...) s_1 ⊥ (0 nat ...))
        "Alternancia-BOT-first")

   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ ((⊕ nat_1) nat_2 ...)) 
        (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ (nat_1 nat_2 ...)) 
        "Alternancia-BOT-first-restore")
   
   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural_1 ...) (natural_2 ...) suc (nat_1 nat_2 ...)) 
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural_1 ...) (natural_2 ...) suc (nat_2 ...))
        "Alternancia-SUC-second")

   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural ...) s_1 ⊥ (0 nat ...)) 
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural ...) s_1 ⊥ (nat ...))
        "Alternancia-BOT-second")

   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ ((⊕ nat_1) nat_2 ...)) 
        (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ (nat_1 nat_2 ...)) 
        "Alternancia-BOT-second-restore")

   ; quando ele sair dando suc, é pra guardar o quanto ele consumiu
   ;Sequence

   (--> (G ⊢ (C ...) (• e_1 e_2) ↓ (natural_1 ...) (natural ...) D (nat ...))
        (G ⊢ ((• h e_2) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (nat ...))
        "Sequencia-Entra")
   
   ;saindo do e_1 deu bom
   (--> (G ⊢ ((• h e_2) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural_3 ...) suc (nat ...))
        (G ⊢ ((• e_1 h) C ...) e_2 ↓ (natural_1 natural_2 ...) (natural_3 ...) suc (nat ...)) ;soma 1, pq ele consome 1
        "Sequencia-SUC-first")
   
   ;saindo do e_1 deu ruim
   (--> (G ⊢ ((• h e_2) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural_3 ...) ⊥ (nat ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 natural_2 ...) (natural_3 ...) ⊥ (nat ...))
        "Sequencia-BOT-first")
   
   ;saindo do e_2 deu bom
   (--> (G ⊢ ((• e_1 h) C ...) e_2 ↑ (natural_1 natural_2 ...) (natural_3 ...) suc (nat ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 natural_2 ...) (natural_3 ...) suc (nat ...))
        "Sequencia-SUC-second")
   
   ;saindo do e_2 deu ruim
   
   (--> (G ⊢ ((• e_1 h) C ...) e_2 ↑ (natural_1 natural_2 ...) (natural_3 natural_4 ...) ⊥ (nat ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 natural_2 ...) (natural_3 natural_4 ...) ⊥ (nat ...))
        "Sequencia-BOT-second")


   ;volta na repetição quando dá falha
   ;cada vez que a repet dá certo, podemos tirar do topo
   ;Repetition

   (--> (G ⊢ (C ...) (* e_1) ↓ (natural_1 natural_2 ...) (natural ...) D (nat ...))
        (G ⊢ ((* h) C ...) e_1 ↓ (natural_1 natural_2 ...) (natural ...) D (0 nat ...))
        "Repetition-Entra")
   
   (--> (G ⊢ ((* h) C ...) e_1 ↑ () (natural ...) suc (nat ...))
        (G ⊢ (C ...) (* e_1) ↑ () (natural ...) suc (nat ...))
        "Repetition-SUC-Sai")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural ...) suc (nat_1 nat_2 ...))
        (G ⊢ (C ...) (* e_1) ↓ (natural_1 natural_2 ...) (natural ...) suc (nat_2 ...))
        (side-condition (term (not (diff? e_1 natural_1))))
        "Repetition-SUC")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural ...) ⊥ (0 nat ...))
        (G ⊢ (C ...) (* e_1) ↑ (natural_1 natural_2 ...) (natural ...) suc (nat ...))
        "Repetition-BOT")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ (natural_2 ...) (natural_1 natural_3 ...) ⊥ ((⊕ nat_1) nat_2 ...))
        (G ⊢ ((* h) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural_3 ...) ⊥ (nat_1 nat_2 ...))
        "Repetition-BOT-restore")

  
   ;Not
   (--> (G ⊢ (C ...) (! e_1) ↓ (natural_1 ...) (natural ...) D   (nat ... ))
        (G ⊢ ((! h) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (0 nat ...))
        "Not-Entra")
 
   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 ...) (natural ...) suc (0 nat ...) nat_1) ;nat_1 é a info de quantos simbolos foram consumidos quando deu suc
        (G ⊢ (C ...) (! e_1) ↑ (natural_1 ...) (natural ...) ⊥ (nat_1 nat ...)) ;n é pra ser aqui, mas é essa ideia
        "Not-BOT")

   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) suc ((⊕ nat_1) nat_2 ...)) 
        (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) suc (nat_1 nat_2 ...)) 
        "Not-BOT-restore") ;
  
   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 ...) (natural ...) ⊥ (0 nat ...))
        (G ⊢ (C ...) (! e_1) ↑ (natural_1 ...) (natural ...) suc (nat ...))
        "Not-SUC")

   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ ((⊕ nat_1) nat_2 ...)) 
        (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ (nat_1 nat_2 ...)) 
        "Not-SUC-restore")

   ;corrigir TUDO.
   

   ;Non-terminals
   ;acho que ta tudo errado
   (--> (G ⊢ (C ...) x ↓ (natural_1 ...) (natural ...) D (nat ...))  
        (G ⊢ ((NT x) C ...) (lookup G x) ↓ (natural_1 ...) (natural ...) D (nat ...))
        "Non-terminals-entra")

   (--> (G ⊢ ((NT x) C ...) e ↑ (natural_1 ...) (natural ...) D (nat ...))  
        (G ⊢ (C ...) x ↑ (natural_1 ...) (natural ...) D (nat ...))
        "Non-terminals-sai")


   )
  )

(define-metafunction Reduct
  [(diff? e_1 e_1)     #f]
  [(diff? e_1 e_2)     #t]

  )

(define-metafunction Reduct
  
  [(lookup (x e G) x) e]
  [(lookup (x_1 e G) x_2) (lookup G x_2)]
  [(lookup ∅ x) ,(error 'lookup "not found: ~e" (term x))]
  )


;Terminal
;(traces red (term (∅ ⊢ () 1 ↓ (1 2 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () 1 ↓ (2 3) () ⊥ (0))))

;Choice
;(traces red (term (∅ ⊢ () (/ 1 2) ↓ (1 2 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (/ 1 2) ↓ (2 3) () ⊥ (0))))

;Sequence
;(traces red (term (∅ ⊢ () (• 1 3) ↓ (1 2 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (• (• 1 2) (• 1 3)) ↓ (1 2 1 5 5) () ⊥ (0))))

;Repetition
;(traces red (term (∅ ⊢ () (* 1) ↓ (1 1 1 1 2) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (* 1) ↓ (1 1 1 1) () ⊥ (0))))

;Not
;(traces red (term (∅ ⊢ () (! 1) ↓ (1 1 2) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (! 2) ↓ (1 1 2) () ⊥ (0))))

;ALTERNANCIA COM REPETIÇÃO E TERMINAL
;(traces red (term (∅ ⊢ () (/ (* 1) 1) ↓ (1 1 1 1 2) () ⊥ (0))))

;SEQUENCIAS E ALTERNANCIAS
;(traces red (term (∅ ⊢ () (• 1 (• 2 (/ (• 3 4) (• 3 5)))) ↓ (1 2 3 5) () ⊥ (0))))

;ALTERNANCIA COM SEQUENCIA
;(traces red (term (∅ ⊢ () (/ (• 1 2) (• 1 3)) ↓ (1 3 3) () ⊥ (0))))

;NON-TERMINAL
;(traces red (term ((A 2 ∅) ⊢ () A ↓ (2 3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () A ↓ (3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () B ↓ (2 3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () (/ A 1) ↓ (1 1 2 3) () ⊥ (0))))

;(stepper red (term (∅ ⊢ () (• (! 0) (• 1 2)) ↓ (1 2 3) () ⊥ (0)))) ;esse da certo
;(traces red (term (∅ ⊢ () (• (• 1 2) (! 0)) ↓ (1 2 3) () ⊥ (0)))) ;esse no meio da umas bifurcações mas no final da certo
;(stepper red (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))); esse da certo tb

;(traces red (term (∅ ⊢ () (! 1) ↓ (1 2 3) () ⊥ (0))))
;(stepper red (term (∅ ⊢ () (! (• 1 3)) ↓ (1 2 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (* (! (• 1 2))) ↓ (1 3) () ⊥ (0))))


#;(stepper red (term ((A (/ (• 0 (• A 1)) ε)
                    (B (/ (• 1 (• B 2)) ε)
                    (C (/ 0 (/ 1 2))
                    (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                    ⊢ () S ↓ (0 1 2) () ⊥ (0))))

#;(stepper red (term ((A (/ (• 0 A) ε) ∅)
                    ⊢ () (! (/ (• 0 0) ε)) ↓ (0 0 0 1 2) () ⊥ (0))))


(stepper red (term (∅ ⊢ () (/ (• (/ (• 0 0) (/ (• 0 1) (• 0 2))) (• 1 3)) (• 0 1)) ↓ (0 1 1 4) () ⊥ (0))))



                    