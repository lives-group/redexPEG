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
;lembrar dos testes que deram errado

#;(define (get-exp l)

  (if (eq? type "j")
      (list (list-ref (list-ref (car l) 2) 0))
      (list (list-ref (car l) 3))
      )
  )
(define (verf-rep exp) ;VERIFICAR OQ CONSOME NO REP
 (if (eq? (judgment-holds (⇀ ∅ exp D) D) (term 1)) ;acho que isso ta errado
    (display "deu true no verf-rep") ;#t
    (display exp) ;#f
  )
)

#;(define (verf-seq exp)
(if (eq? )

  )
)

(define (is-WF exp);vai vir a expressao por exemplo (G (/ (/ 1 2) 2))

;  (define exp (get-exp e type))
 ; (print (car exp))
  (if (not (null? exp))
      (cond [(number? (car exp))                       #t]
            [(eq? (car exp) (term ε))                  #t]
            [(eq? (list-ref (list-ref (car exp) 2) 0) (term (!)))         (is-WF (list-ref (car exp) 2))] ;NAO SEI PQ TA DANDO ERRADO NAO CONSIGO PEGAR O ! DA EXP
            [(eq? exp (term (G (* e_1))))         (verf-rep exp)]
            [(eq? exp (term (G (• e_1 e_2)))) #t] ;usar o judgment ⇀ pra testar se consome algo (judgment-hold ⇀ ∅ (• e_1 e_2)) 
            [(eq? (car exp) (term (G (/ e_1 e_2)))) (and (is-WF (term e_1)) (is-WF (term e_2)))]            
            [else "Deu errado"]
            )

      "null")
  )

