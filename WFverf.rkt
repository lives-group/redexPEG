#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")
(require "./reduction.rkt")


;implementar o algoritmo do artigo do ford?
;usar o judgment wf para obter resultados imediatos
;receber uma gramatica e expressão para verificar se tá WF.
;função auxiliar - vamos precisar? 
;colocar numa lista qualquer as exp que a gnt acha que é bem formada
;final a lista é igual a 1 -> testar
;fazer uma meta funçao para verificar se uma gramatica é WF 
;(get-result (apply-reduction-relation* red (term (∅ ⊢ () (• 1 2) ↓ (1 3 3) () ⊥ (0)))

;fazer um extend-language e criar uma funçao que verifica as coisas?
;como colocar a gramatica


(define (get-exp l type)

  (if (eq? type "j")
      (list (list-ref (list-ref (car l) 2) 0))
      (list (list-ref (car l) 3))
      )
  )

(define (is-WF e type);vai vir a expressao por exemplo (/ (/ 1 2) 2)

  (define exp (get-exp e type))
  (print (car exp))
  (if (not (null? exp))
      (cond [(number? (car exp)) (display "\nNatural WF\n")]
            [(eq? (car exp) (term ε)) #t]
            [(eq? exp (term (! e))) (is-WF exp type)]
            [(eq? exp (term (* e))) (is-WF exp type)]
            [(eq? exp (term (• e_1 e_2))) (is-WF exp type)]
            [(eq? (car exp) '(/ e_1 e_2)) (and (is-WF (term e_1) type) (is-WF (term e_2) type))]            
            [else "Blub"]
            )
      "Blubb")
  )

(is-WF '((eval ∅ (1 (2 1 1)) s) s) "j")
(is-WF '((∅ ⊢ () (/ 1 2) ↓ (2 1 1) () ⊥ (0))) "r")