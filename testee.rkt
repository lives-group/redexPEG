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

(sample (gen:one-of '(a b c)) 10) 