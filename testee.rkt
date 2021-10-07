#lang racket
(require redex)
(require "./peg.rkt")
(define +Gen (make-pseudo-random-generator))
(require rackcheck)

#;(define-metafunction Peg
    [(Gpeg natural) peg]
  
    )
;trocar o nome desse arq aqui que testee ta mt feio

;n -> numero de nao terminal
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
      (gen:choice (gen:one-of Σ) (genEntrada)) 
      (gen:choice (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1) ) n L) (lambda (s) (gen:const  `(• ,t ,s)) ) ) ) )
                  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) n L) (lambda (s) (gen:const  `(/ ,t ,s))) ) ) )
                  (gen:bind (genPeg Σ (- p 1) n L)
                            (lambda (t) (gen:const `(! ,t)) ))
                  (gen:bind (genPeg Σ (- p 1) n L)
                            (lambda (t) (gen:const `(* ,t)) ))
                  )
      )  
  )

; e -> peg correspondente pra pegar os NT e achar a gramática
(define (genGrammar Σ p n L e rep grammar)
  (if (and  (not (null? e)) (member (car e) Σ) (not (member (car e) rep)) )
      (genGrammar Σ p n L (cdr e) (list rep (car e)) (cons grammar (cons (car e) (sample (genPeg Σ (car (sample (gen:one-of '(0 1 2)) 1)) n L) 1))))
      (if (null? (cdr e))
          "null"
          (genGrammar Σ p n L (cdr e) rep grammar))
      )
      
  )

(define (genEntrada)
  (gen:choice (gen:one-of '(0 1 2 3 4 5 6 7 8 9)) (gen:const 'ε))
  )


(define (genState Σ p n L cont)
  (define peg (sample (genPeg Σ p n L) cont))
  (define grammar '())
  (genGrammar Σ p n L peg '() grammar)
  (define entrada (sample (gen:one-of '(0 1 2 3 4 5 6 7 8 9)) cont))

  (list grammar  '⊢ '() peg '↓ entrada '() '⊥ '(0))
  )
;n -> numero de nao terminal
;L -> lista
;P -> profundidade lista
;Σ -> lista de elementos de um alfabeto

;(sample (gen:one-of '(a b c)) 10)

(genState '(a b c) 1 0 '() 1)
(genState '(a b c) 1 0 '() 2)