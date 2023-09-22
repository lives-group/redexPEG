#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")
(require "./reduction.rkt")
(require "./WFverf.rkt")

(display "Testes\n")

(define (tests-reduction)
  ;TERMINAL
  (test-->> red
            (term (∅ ⊢ () 1 ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () 1 ↑ (2 3) (1) suc (1))))
  ;ALTERNANCIA + (REPETIÇÃO + TERMINAL)
  (test-->> red
            (term (∅ ⊢ () (/ (* 1) 1) ↓ (1 1 1 1 2) () ⊥ (0)))
            (term (∅ ⊢ () (/ (* 1) 1) ↑ (2) (1 1 1 1) suc (4))))
  ;NOT + SEQUENCIA
  (test-->> red
            (term (∅ ⊢ () (! (• 1 3)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (! (• 1 3)) ↑ (1 2 3) () suc (0)))
            )
  ;ALTERNANCIA + ((NOT + SEQUENCIA) + SEQUENCIA)
  (test-->> red
            (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (/ (! (• 1 2)) (• 1 0)) ↑ (1 2 3) () ⊥ (0)))
            )
  ;REPETIÇÃO + SEQUENCIA ----> LOOP
  (test-->> red
            (term (∅ ⊢ () (* (• 1 2)) ↓ (1 2 1 2 1 2 1 3) () ⊥ (0)))
            (term (∅ ⊢ () (* (• 1 2)) ↑ (1 3) (2 1 2 1 2 1) suc (6)))
            )
  ;SEQUENCIA + (SEQUENCIA + NOT)
  (test-->> red
            (term (∅ ⊢ () (• (• 1 2) (! 0)) ↓ (1 2 3) () ⊥ (0)))
            (term (∅ ⊢ () (• (• 1 2) (! 0)) ↑ (3) (2 1) suc (2))))

  ;NON-TERMINAL 
  (test-->> red 
            (term ((A (/ (• 0 (• A 1)) ε)
                      (B (/ (• 1 (• B 2)) ε)
                         (C (/ 0 (/ 1 2))
                            (S (• (! (! A)) (• (* 0) (• B (! C)))) ∅))))
                   ⊢ () S ↓ (0 1 2) () ⊥ (0)))
            (term ((A
                    (/ (• 0 (• A 1)) ε)
                    (B
                     (/ (• 1 (• B 2)) ε)
                     (C
                      (/ 0 (/ 1 2))
                      (S
                       (•
                        (! (! A))
                        (• (* 0) (• B (! C))))
                       ∅))))
                   ⊢ () S ↑ () (2 1 0) suc (3))))
  (test-results))


;(tests-reduction)


(define (reduction-right? exp)
  (= 1 (length (apply-reduction-relation red exp)))
  )

#;(redex-check Reduct       
               #:satisfying (is-WF (input-grammar state) (input-peg state))             
               (not (eq? (term (input-result (apply-reduction-relation red (term state)))))
                    (term ⊥))
               #:attempts 1000)


;documentar tudo isso
;fazer uma metafunction para mascarar o gerador, metafunction receber o parametro do gerador, para o gerador pegar uma peg valida(WF
;satisfying de uma metafunction
;fazer uma função que verifica se o termo tá com a setinha pra baixo e se atende nosso is-WF
(display "\nRedex-Check WF?\n")
(redex-check Reduct
             ;(G ⊢ (C ...) e ↓ (natural ...) () D (0))
             #:satisfying (WF? state)              
             (equal? (term (input-result ,(car (apply-reduction-relation* red (term state)))))
                  (car (judgment-holds (eval (input-grammar state) ((input-peg state) (input-term state)) s) s)))
             #:attempts 10000)

(redex-check Reduct
             (G ⊢ (C ...) e ↓ (natural ...) () D (0))
             ;#:satisfying (WF? (G e ))             
             (equal? (term (input-result ,(car (apply-reduction-relation* red (term (G ⊢ (C ...) e ↓ (natural ...) () D (0)))))))
                  (car (judgment-holds (eval G (e (natural ...)) s) s)))
             #:attempts 10000)

#;(redex-check Reduct
             
               #:satisfying (WF (input-grammar state) (input-peg state))
               (not (eq? (term (input-result (apply-reduction-relation red (term state)))))
                    (term ⊥))
               #:attempts 1000)
;nao usar o WF
;usar o eval e comparar com o da reduct

#;(redex-check Reduct
               state
               (reduction-right? (term state))
               #:attempts 1000)

#;(redex-check Reduct
               #:satisfying (WF (input-grammar state) (input-peg state))
             
               #:attempts 10000)


