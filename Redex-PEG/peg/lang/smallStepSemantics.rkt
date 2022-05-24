#lang racket
; This module defines a small step semantics for PEG 

(require redex)
(require "../lang/peg.rkt")
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
  (dir ↓
       ↑)
  (s (natural ...))
  (state (G ⊢ (C ...) e dir s_1 s_2 D (natural ...))) 
  )
;up-arrow - coming out of the expression - finished the analysis
;down-arrow: entering

;dir -> setinha
;state é o input e o output da red

;nat ser transformado em uma lista de numeros
;quando aparecer um choice, colocar um 0 na frente
;quando sair do choice com sucesso, tira o topo da lista

(define-metafunction Reduct
  input-grammar : state -> G ;type
  [(input-grammar (G ⊢ (C ...) e dir s_1 s_2 D (natural ...))) G])

(define-metafunction Reduct
  input-peg : state -> e
  [(input-peg (G ⊢ (C ...) e dir s_1 s_2 D (natural ...))) e])

(define-metafunction Reduct
  input-result : state -> s
  [(input-result (G ⊢ (C ...) e dir s_1 s_2 ⊥ (natural ...))) ⊥]
  [(input-result (G ⊢ (C ...) e dir s_1 s_2 D (natural ...))) s_1])

(define-metafunction Reduct
  input-term : state -> s
  [(input-term (G ⊢ (C ...) e dir s_1 s_2 D (natural ...))) s_1])

; 
(define red
  (reduction-relation 
   Reduct
   #:domain state
   ;Terminal
   
   (--> (G ⊢ (C ...) natural_1 ↓ (natural_1 natural_2 ...) (natural_3 ...) D (natural_4 natural_5 ...))
        (G ⊢ (C ...) natural_1 ↑ (natural_2 ...) (natural_1 natural_3 ...) suc ((inc natural_4) natural_5 ...))
        "Terminal")

   (--> (G ⊢ (C ...) natural_1 ↓ (natural_2 natural ...) s_1 D (natural_3 ...))
        (G ⊢ (C ...) natural_1 ↑ (natural_2 natural ...) s_1 ⊥ (natural_3 ...))
        (side-condition (term (diff-exp? natural_1 natural_2)))     
        "Terminal ⊥")

   (--> (G ⊢ (C ...) natural_1 ↓ () s_1 D (natural_2 ...))
        (G ⊢ (C ...) natural_1 ↑ () s_1 ⊥ (natural_2 ...))
        "Terminal () ⊥")

   ;Empty
   (--> (G ⊢ (C ...) ε ↓ (natural ...) s_1 D (natural_1 ...))
        (G ⊢ (C ...) ε ↑ (natural ...) s_1 suc (natural_1 ...))
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
   (--> (G ⊢ (C ...) (/ e_1 e_2) ↓ (natural_1 ...) (natural ...) D (natural_2 ...))
        (G ⊢ ((/ h e_2) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (0 natural_2 ...)) ;h serve tentar e e_2 para memorizar
        "Choice-In")

   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural_1 ...) (natural_2 ...) suc (natural_3 natural_4 natural_5 ...))
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural_1 ...) (natural_2 ...) suc ((⊕ natural_3 natural_4) natural_5 ...))
        "Choice-SUC-first")
   
   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural ...) s_1 ⊥ (0 natural_2 ...)) 
        (G ⊢ ((/ e_1 h) C ...) e_2 ↓ (natural ...) s_1 ⊥ (0 natural_2 ...))
        "Choice-BOT-first")

   (--> (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ (natural_3 natural_4 ...)) 
        (G ⊢ ((/ h e_2) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ ((dec natural_3) natural_4 ...))
        (side-condition (term (diff-exp? natural_3 0)))
        "Choice-BOT-first-restore")
   
   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural_1 ...) (natural_2 ...) suc (natural_3 natural_4 natural_5 ...)) 
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural_1 ...) (natural_2 ...) suc ((⊕ natural_3 natural_4) natural_5 ...))
        "Choice-SUC-second")

   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural ...) s_1 ⊥ (0 natural_1 ...)) 
        (G ⊢ (C ...) (/ e_1 e_2) ↑ (natural ...) s_1 ⊥ (natural_1 ...))
        "Choice-BOT-second")

   (--> (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ (natural_3 natural_4 ...)) 
        (G ⊢ ((/ e_1 h) C ...) e_2 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ ((dec natural_3) natural_4 ...))
        (side-condition (term (diff-exp? natural_3 0)))
        "Choice-BOT-second-restore")

   ;Sequence

   (--> (G ⊢ (C ...) (• e_1 e_2) ↓ (natural_1 ...) (natural ...) D (natural_2 ...))
        (G ⊢ ((• h e_2) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (natural_2 ...))
        "Sequence-In")
   
   ;saindo do e_1 deu bom
   (--> (G ⊢ ((• h e_2) C ...) e_1 ↑ (natural_1 ...) (natural_3 ...) suc (natural_4 ...))
        (G ⊢ ((• e_1 h) C ...) e_2 ↓ (natural_1 ...) (natural_3 ...) suc (natural_4 ...)) 
        "Sequence-SUC-first")
   
   ;saindo do e_1 deu ruim
   (--> (G ⊢ ((• h e_2) C ...) e_1 ↑ (natural_1 ...) (natural_3 ...) ⊥ (natural_4 ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 ...) (natural_3 ...) ⊥ (natural_4 ...))
        "Sequence-BOT-first")
   
   ;saindo do e_2 deu bom
   (--> (G ⊢ ((• e_1 h) C ...) e_2 ↑ (natural_1 ...) (natural_3 ...) suc (natural_4 ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 ...) (natural_3 ...) suc (natural_4 ...))
        "Sequence-SUC-second")
   
   ;saindo do e_2 deu ruim
   
   (--> (G ⊢ ((• e_1 h) C ...) e_2 ↑ (natural_1 ...) (natural_3 ...) ⊥ (natural_5 ...))
        (G ⊢ (C ...) (• e_1 e_2) ↑ (natural_1 ...) (natural_3 ...) ⊥ (natural_5 ...))
        "Sequence-BOT-second")


   ;volta na repetição quando dá falha
   ;cada vez que a repet dá certo, podemos tirar do topo


   ;Repetition

   (--> (G ⊢ (C ...) (* e_1) ↓ s_1 s_2 D (natural_4 ...))
        (G ⊢ ((* h) C ...) e_1 ↓ s_1 s_2 D (0 natural_4 ...))
        "Repetition-In")
   
   #;(--> (G ⊢ ((* h) C ...) e_1 ↑ () (natural ...) suc (natural_4 ...))
        (G ⊢ (C ...) (* e_1)   ↑ () (natural ...) suc (natural_4 ...))
        "Repetition-SUC-Out")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ s_1 (natural ...) suc (natural_3 natural_4 natural_5 ...))
        (G ⊢ ((* h) C ...) e_1 ↓ s_1 (natural ...) suc (0 (⊕ natural_3 natural_4) natural_5 ...))
        "Repetition-SUC")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ s_1 s_2 ⊥ (0 natural_4 ...))
        (G ⊢ (C ...) (* e_1) ↑ s_1 s_2 suc (natural_4 ...))
        "Repetition-BOT")

   (--> (G ⊢ ((* h) C ...) e_1 ↑ (natural_2 ...) (natural_1 natural_3 ...) ⊥ (natural_4 natural_5 ...))
        (G ⊢ ((* h) C ...) e_1 ↑ (natural_1 natural_2 ...) (natural_3 ...) ⊥ ((dec natural_4) natural_5 ...))
        (side-condition (term (diff-exp? natural_4 0)))
        "Repetition-BOT-restore")

  
   ;Not

   (--> (G ⊢ (C ...) (! e_1) ↓ (natural_1 ...) (natural ...) D   (natural_4 ... ))
        (G ⊢ ((! h) C ...) e_1 ↓ (natural_1 ...) (natural ...) D (0 natural_4 ...))
        "Not-In")
 
   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 ...) (natural ...) suc (0 natural_4 ...))
        (G ⊢ (C ...) (! e_1) ↑ (natural_1 ...) (natural ...) ⊥ (natural_4 ...))
        "Not-BOT")

   #;(--> (G ⊢ ((! h) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) suc (natural_3 natural_4 ...)) 
        (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) suc ((dec natural_3) natural_4 ...))
        (side-condition (term (diff-exp? natural_3 0)))
        "Not-BOT-restore")
  
   (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 ...) (natural ...) ⊥ (0 natural_4 ...))
        (G ⊢ (C ...) (! e_1) ↑ (natural_1 ...) (natural ...) suc (natural_4 ...))
        "Not-SUC")

   #;(--> (G ⊢ ((! h) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) ⊥ (natural_3 natural_4 ...)) 
        (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) ⊥ ((dec natural_3) natural_4 ...))
        (side-condition (term (diff-exp? natural_3 0)))
        "Not-SUC-restore")

    (--> (G ⊢ ((! h) C ...) e_1 ↑ (natural ...) (natural_1 natural_2 ...) D (natural_3 natural_4 ...)) 
        (G ⊢ ((! h) C ...) e_1 ↑ (natural_1 natural ...) (natural_2 ...) D ((dec natural_3) natural_4 ...))
        (side-condition (term (diff-exp? natural_3 0)))
        "Not-restore")

   

   ;Non-terminals

   (--> (G ⊢ (C ...) x ↓ (natural_1 ...) (natural ...) D (natural_4 ...))  
        (G ⊢ ((NT x) C ...) (lookup-red G x) ↓ (natural_1 ...) (natural ...) D (natural_4 ...))
        "NonTerminals-In")

   (--> (G ⊢ ((NT x) C ...) e ↑ (natural_1 ...) (natural ...) D (natural_4 ...))  
        (G ⊢ (C ...) x ↑ (natural_1 ...) (natural ...) D (natural_4 ...))
        "NonTerminals-Out")


   )
  )

(define-metafunction Reduct
  [(diff-exp? e_1 e_1)     #f]
  [(diff-exp? e_1 e_2)     #t]

  )

(define-metafunction Reduct
  
  [(lookup-red (x e G) x) e]
  [(lookup-red (x_1 e G) x_2) (lookup-red G x_2)]
  [(lookup-red ∅ x) ,(error 'lookup-red "not found: ~e" (term x))]
  )

(define-metafunction Reduct
  [(inc natural)   ,(add1 (term natural))]
  )


(define-metafunction Reduct
  [(dec natural)   ,(sub1 (term natural))]
  )

(define-metafunction Reduct
  [(⊕ natural_1 natural_2)   ,(+ (term natural_1) (term natural_2))]
  )

;Terminal
;(stepper red (term (∅ ⊢ () 1 ↓ (1 2 3) () ⊥ (0))))
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
;(stepper red (term (∅ ⊢ () (/ (• 1 2) (• 1 3)) ↓ (1 3 3) () ⊥ (0))))

;NON-TERMINAL
;(traces red (term ((A 2 ∅) ⊢ () A ↓ (2 3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () A ↓ (3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () B ↓ (2 3 4 5 6 7) () ⊥ (0))))
;(traces red (term ((A 2 ∅) ⊢ () (/ A 1) ↓ (1 1 2 3) () ⊥ (0))))

;(stepper red (term (∅ ⊢ () (• (! 0) (• 1 2)) ↓ (1 2 3) () ⊥ (0)))) ;esse da certo
;(traces red (term (∅ ⊢ () (• (• 1 2) (! 0)) ↓ (1 2 3) () ⊥ (0)))) 
;(stepper red (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))); esse da certo tb

;(traces red (term (∅ ⊢ () (! 1) ↓ (1 2 3) () ⊥ (0))))
;(stepper red (term (∅ ⊢ () (! (• 1 3)) ↓ (1 2 3) () ⊥ (0))))
;(traces red (term (∅ ⊢ () (* (! (• 1 2))) ↓ (1 3) () ⊥ (0))))


#;(stepper red (term ((C (• (* B) (/ B A))
                    (B (• (/ 2 ε) (• A 2))
                    (A (* (• 1 ε))
                    ∅) ) ) 
                    ⊢ () (/ B 2)
                    ↓ (2 1) () ⊥ (0))))

#;(stepper red (term ((A (/ (• 0 A) ε) ∅)
                    ⊢ () (! (/ (• 0 0) ε)) ↓ (0 0 0 1 2) () ⊥ (0))))
;(stepper red (term (∅ ⊢ () (/ (• (/ (• 0 0) (/ (• 0 1) (• 0 2))) (• 1 3)) (• 0 1)) ↓ (0 1 1 4) () ⊥ (0))))
;(apply-reduction-relation* red (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0))))

#;(with-atomic-rewriters
   (['natural "N"]
    ['h "_"])
    (render-reduction-relation red))

#;(with-atomic-rewriters
   (['natural "N"]
    [(string->symbol "...") ""])
    (render-reduction-relation red))

#;(with-compound-rewriter
   'G
   (λ (lws)
     (define a (list-ref lws 3))
     (list (list-ref lws 1) (list-ref lws 2) a "L"))
   (render-reduction-relation red))


(with-compound-rewriter
   'G
   (λ (lws)
     (define G (list-ref lws 1))
     (define ⊢ (list-ref lws 2))
     (define C (list-ref lws 3))
     (define e (list-ref lws 4))
     (define dir (list-ref lws 5))
     (define s1 (list-ref lws 6))
     (define s2 (list-ref lws 7))
     (define D (list-ref lws 8))
     (define nat (list-ref lws 9))
     (list G ⊢ C e dir s1 s2 D nat))
   (render-reduction-relation red))

