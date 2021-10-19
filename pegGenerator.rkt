#lang racket
(require redex)
(require "./peg.rkt")
(define +Gen (make-pseudo-random-generator))
(require rackcheck)

#;(define-metafunction Peg
    [(Gpeg natural) peg]
  
    )
;trocar o nome desse arq aqui que testee ta mt feio

;n -> lista de nomes de nao terminais
;L -> lista
;P -> profundidade lista
;Σ -> lista de elementos de um alfabeto
(define (Gpeg n L P Σ)
  
  (if (equal? P 0) 
      (random 10 +Gen)
      (display "lol")
      )

  )

(define myGen (make-pseudo-random-generator))

(define (genPeg Σ p n L)
  (if (equal? p 0)
      (gen:choice (gen:one-of Σ) (gen:const 'ε))
      (gen:choice (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1) ) n L) (lambda (s) (gen:const  `(• ,t ,s)) ) ) ) )
                  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L) (lambda (s) (gen:const  `(/ ,t ,s))) ) ) )
                  (gen:bind (genPeg Σ (- p 1) n L)
                            (lambda (t) (gen:const `(! ,t)) ))
                  (gen:bind (genPeg Σ (- p 1) n L)
                            (lambda (t) (gen:const `(* ,t)) ))
                  (gen:one-of n)
                  )
      )  
  )

;definir quantos nao terminais
;pra cada n terminal damos o genPeg
; e -> peg correspondente pra pegar os NT e achar a gramática
;receber a lista de gramática - L
;usar o map pra gerar uma peg pra cada nt
;é pra gerar bem formada já
;usa o is-WF ??

;gerar uma expressão pro nt: verifica se a exp é bem formada (se caso a exp tiver um nt tbm, verifica se o não terminal ja existe.....)


(define (genGramar Σ p n L e rep grammar)
  
  (if (and  (not (empty? e)) (member (car (list e)) n) )
      (genGrammar Σ p n L (rest (list e)) (list rep (car (list e))) (cons grammar (cons (car (list e))
                                                                         (sample (genPeg Σ (car (sample (gen:one-of '(0 1 2)) 1)) n L) 1))))
      (if (empty? e)
          "null";;retorna null pq cdr do e fica '()
          (genGrammar Σ p n L (rest e) rep grammar))      )
      
  )

(define (genGrammar Σ p n L e rep grammar)
  
  (map (lambda (i)
         (cons i (sample (genPeg Σ p n L) 1)))
         n)
      
  )


;n -> numero de NT
(define (genSymbols n)
  (define cont (build-list n values))
  (map (lambda (i)
         (string->symbol (format "X~a" i)))
       cont)
  )

(define (genEntrada)
  (gen:choice (gen:one-of '(0 1 2 3 4 5 6 7 8 9)) (gen:const 'ε))
  )


(define (genState Σ p n L cont)
  (define peg (sample (genPeg Σ p n L) cont))
  (define grammar '∅)
  (define grammar2 (genGrammar Σ p n L (car peg) '() grammar))
  (define entrada (sample (gen:one-of '(0 1 2 3)) cont))

  (list (cons grammar2 grammar)  '⊢ '() (car peg) '↓ entrada '() '⊥ '(0))
  )
;n -> numero de nao terminal
;L -> lista
;p -> profundidade lista
;Σ -> lista de elementos de um alfabeto
;cont -> deve ser 1

;(sample (gen:one-of '(a b c)) 10)
(display "\nGera Peg\n")
(sample (genPeg '(0 1 2) 1 (genSymbols 3) '()) 1)
(cdr (sample (genPeg '(A B C) 1 (genSymbols 3) '()) 1))

(display "\nGera Gramática\n")
(genGrammar '(0 1 2) 1 (genSymbols 3) '() (sample (genPeg '(0 1 2) 1 (genSymbols 3) '()) 1) '() '())

(display "\nGera Estado\n")
(genState '(0 1 2) 1 (genSymbols 3) '() 1)
(genState '(0 1 2) 1 (genSymbols 3) '() 1)
(genState '(0 1 2) 2 (genSymbols 3) '() 1)
(genState '(0 1 2) 3 (genSymbols 3) '() 1)
(genState '(0 1 2) 3 (genSymbols 3) '() 1)


