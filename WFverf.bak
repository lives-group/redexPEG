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

(define (is-WF exp);vai vir a expressao por exemplo (/ (/ 1 2) 2)

(if (not (empty? exp))
  (if (eq? (list-ref (car exp) 0) natural)
      (is-WF (cdr exp))
      
      
      
  )
)

)
(is-WF (list '(/ (/ 1 2) 2)))