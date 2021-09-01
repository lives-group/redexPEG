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


(define (get-exp e)

  (if (eq? (list-ref (car e) 0) (term ∅))
      (list-ref (car e) 1)
      (car e))
      
  )

#;(define (verf-seq exp) ;VERIFICAR OQ CONSOME NA SEQUENCIA
  
    ;(print (judgment-holds (⇀ ∅ ,exp D) D))
    (if (eq? (judgment-holds (⇀ ∅ ,exp D) D) (list '(1 ⊥)))
        #f
        #t
        )
    )

(define (verf-judg exp) ;VERIFICAR OQ CONSOME NA SEQUENCIA
  
  ;(print (judgment-holds (⇀ ∅ ,exp D) D))
  (if (member 0 (judgment-holds (⇀ ∅ ,exp D) D))
      #f
      #t
      )
  )



(define (verf-rep exp) ;VERIFICAR OQ CONSOME NO REP
  ;(print (judgment-holds (⇀ ∅ ,exp D) D))
  (define result (judgment-holds (⇀ ∅ ,exp D) D))
  (if (eq? result '(⊥)) 
      #f
      #t
      )
  )

(define (is-WF e);vai vir a expressao por exemplo (G (/ (/ 1 2) 2))
  
  ;exp -> list
  (define exp (get-exp e))
  (define id (car exp))
  
  (print exp)
  (display " - ")
  (if (eq? '∅ (car (car e)));verifica se é empty o G 
      (if (not (null? exp))
          (cond [(number? id)                             #t]
                [(eq? id (term ε))                        #t]
                [(eq? id (term !))                        (is-WF (list (list-ref exp 1)))]
                [(eq? id (term /))                        (and (is-WF (list (list (list-ref exp 1)))) (is-WF (list (list (list-ref exp 2)))))] 
                [(eq? id (term •))                        (and (is-WF (list (list (list-ref exp 1))))
                                                               (or (verf-judg   (list-ref exp 1)) (is-WF (list (list (list-ref exp 2))))))] ;usar o judgment ⇀ pra testar se consome algo (judgment-hold ⇀ ∅ (• e_1 e_2)) 
                [(eq? id (term *))                        (and (is-WF (list (list (list-ref exp 1))))
                                                               (verf-judg exp))]
            
                ;nao terminal colocar o judgment no lookup    
                [else "Deu errado"]
                )

          "null")
  
      (is-WF (judgment-holds (lookup (car (car e)) exp R) R));ta dando errado
      )
  )

#;(define-metafunction Reduct
    [(consome? e_1 e_1)     (judgment-holds (⇀ ∅ exp D) D)]
    [(consome? e_1 e_2)     #t]

    )
;testar mais
(is-WF (list '(∅ (1))))
(is-WF (list '(∅ (ε))))
(is-WF (list '(∅ (! (1)))))
(is-WF (list '(∅ (/ 1 2))))
(is-WF (list '(∅ (/ (/ 1 2) 2))))
(is-WF (list '(∅ (! (/ 1 2)))))
(is-WF (list '(∅ (• 1 2)))) 
(is-WF (list '(∅ (* ε))))    
(is-WF (list '(∅ (* (! 0)))))