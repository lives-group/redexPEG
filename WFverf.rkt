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


(define (verf-judg exp) ;VERIFICAR OQ CONSOME NA SEQUENCIA
  
  ;(print (judgment-holds (⇀ ∅ ,exp D) D))
  (if (member 0 (judgment-holds (⇀ ∅ ,exp D) D))
      #f
      #t
      )
  )

(define (verf-judg-nt grammar exp) ;VERIFICAR OQ CONSOME NO NAO TERMINAL
  
  (print exp)
  (display " - ")
  (if (member (term ⊥) (judgment-holds (lookup ,grammar ,exp R) R))
      #f
      #t
      )
  )

#;(define (get-exp e)

    (if (eq? (list-ref (car e) 0) (term ∅))
        (list-ref (car e) 1)
        (car e))
      
    )

(define (is-WF grammar e) ;vai vir a expressao por exemplo (G (/ (/ 1 2) 2))
  
  (if (list? e)
      (let ((id (car e)))
        (cond [(eq? id '/)  (and (is-WF grammar (cadr e)) (is-WF grammar (caddr e)))]
              [else (display "Deu ruim") #f]
              )

        )
      (cond [(number? e) #t]
            [(eq? e 'ε)  #t]
            [else (display "Nao Terminal")#f]
            )
      )
#|
  #;(define exp (get-exp e))
  #;(define id (car e))
  
  (print exp)
  (display " - ")

  ;(if (eq? '∅ grammar);verifica se é empty o G 
  (if (not (null? exp))
      (cond [(number? id)                             #t]
            [(eq? id (term ε))                        #t]
            [(eq? id (term !))                        (is-WF grammar (list (list-ref exp 1)))]
            [(eq? id '/)                        (and (is-WF grammar (list (list (list-ref exp 1)))) (is-WF grammar (list (list (list-ref exp 2)))))] 
            [(eq? id (term •))                        (and (is-WF grammar (list (list (list-ref exp 1))))
                                                           (or (verf-judg   (list-ref exp 1)) (is-WF grammar (list (list (list-ref exp 2))))))] ;usar o judgment ⇀ pra testar se consome algo (judgment-hold ⇀ ∅ (• e_1 e_2)) 
            [(eq? id (term *))                        (and (is-WF grammar (list (list (list-ref exp 1))))
                                                           (verf-judg exp))]
              
            [else (display "Deu ruim\n") #f];Non terminal
            )

      "null")
  ;(is-WF (judgment-holds (lookup ,(car (car e)) ,exp R) R));ta dando errado
  )
  |#
)
;FUNÇÃO QUE INICIA TUDO - define a gramática e verifica por ela
(define (inicio e)
  (define grammar (car (car e)))
  (define exp (list-ref (car e) 1))
  ;(define exp (get-exp e))
  
  (print grammar)
  ;(print e)
  (display " - ")

  (if (eq? (term ∅) grammar)
      (is-WF grammar e)
      (verf-judg-nt grammar (car exp)))

  )

;testar mais
(is-WF '∅ '(/ 1 2))
(is-WF '∅ '(/ (/ (/ 1 2) 1) 2))
(is-WF '∅ '(/ (/ (/ 1 2) 1) (/ 1 2)))
#|
(display "\nTerminal\n")
(inicio (list '(∅ (1))))

(display "\nEmpty\n")
(inicio (list '(∅ (ε))))

(display "\nNot\n")
(inicio (list '(∅ (! (1)))))
(inicio (list '(∅ (! (/ 1 2)))))

(display "\nAlternancia\n")
(inicio (list '(∅ (/ 1 2))))
(inicio (list '(∅ (/ (/ 1 2) 2))))

(display "\nSequência\n")
(inicio (list '(∅ (• 1 2))))

(display "\nRepetição\n")
(inicio (list '(∅ (* ε))))    
(inicio (list '(∅ (* (! 0)))))

(display "\nNão Terminal\n")
(inicio (list '((A 2 ∅) (A))))
(inicio (list '((A 2 ∅) (C))))
(inicio (list '((B 1 (A B ∅)) (B))))
(inicio (list '((B 1 (A B ∅)) (C))))
(inicio (list '((A (• 1 A) ∅) (A))))
(inicio (list '((A (• A 1) ∅) (A))))
|#