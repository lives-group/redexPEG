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


(define (zero⇀? grammar exp) ;VERIFICAR OQ CONSOME NA SEQUENCIA PASSAR A GRAMATICA 
  
  ;(print (judgment-holds (⇀ ∅ ,exp D) D))
  (if (member 0 (judgment-holds (⇀ ,grammar ,exp D) D))
      #f
      #t
      )
  )

(define (verf-judg-nt grammar exp) ;VERIFICAR OQ CONSOME NO NAO TERMINAL

  (define result (judgment-holds (lookup ,grammar ,exp R) R))
  
  ;(print result)
  (if (member (term ⊥) (judgment-holds (lookup ,grammar ,exp R) R));;
      #f
      (car result) ;ele sai do lookup como uma lista, ex.: '(ε), precisamos do termo puro, então fazemos o car
      )
  )

#;(define (get-exp e)

    (if (eq? (list-ref (car e) 0) (term ∅))
        (list-ref (car e) 1)
        (car e))
      
    )

(define (is-WF grammar e) ;vai vir a expressao por exemplo (G (/ (/ 1 2) 2))

  (print e)
  (display " - ")
  (if (list? e)
      (let ((id (car e)))
        (cond [(eq? id '/)  (and (is-WF grammar (cadr e)) (is-WF grammar (caddr e)))]
              [(eq? id '•)  (and (is-WF grammar (cadr e))
                                 (or (zero⇀? grammar (cadr e))
                                     (is-WF grammar (caddr e))))] ;usar o judgment ⇀ pra testar se consome algo (judgment-hold ⇀ ∅ (• e_1 e_2)) ]
              [(eq? id '!)  (is-WF grammar (cadr e))]
              [(eq? id '*)  (and (is-WF grammar (cadr e))
                                 ;verifica se a grammar é ∅, se n for, usa o resultado do verf-judg-nt pra verificar o judgment do *
                                 ;pra ele n usar o não terminal puro.
                                 (zero⇀? grammar (cadr e)))]; passar a grammar no verf-judg para nao precisar de verf a gramatica
              [else (display "Deu ruim com lista") #f] 
              )

        )
      (cond [(number? e) #t]
            [(eq? e 'ε)  #t]
            [(not (eq? grammar '∅)) (is-WF grammar (verf-judg-nt grammar e))] 
            [else (display "Deu ruim sem lista") #f]
            )
      )
 
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
;concertar o tchutchu tilt

(display "\nAlternancia\n")
(is-WF '∅ '(/ 1 2))
(is-WF '∅ '(/ (/ (/ 1 2) 1) 2))
(is-WF '∅ '(/ (/ (/ 1 2) 1) (/ 1 2)))

(display "\nSequência\n")
(is-WF '∅ '(• 1 2))

(display "\nNot\n")
(is-WF '∅ '(! (• 1 2)))

(display "\nRepetição\n")
(is-WF '∅ '(* (• 1 2)))
(is-WF '∅ '(* ε))

(display "\nNão Terminal\n")

(is-WF '(B ε ∅) 'B) ;ta dando errado pq na linha 71 ta testando se consome 0, o empty consome 0 ai ta dando #f nao era pra dar
(is-WF '(B 1 ∅) 'B)
(is-WF '(B ε (A B ∅)) '(* B))
(is-WF '(B 1 (A B ∅)) '(/ B A))
(is-WF '(B 1 (A B ∅)) '(/ A B))
(is-WF '(B 1 (A ε ∅)) '(/ (* A) B))
;(is-WF '(A (• A 1) ∅) 'A) ;CUIDADO!


(display "\n Testes \n")
(is-WF '∅ '(• 0 (* (/ (! 1) 2))))
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