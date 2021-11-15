#lang racket
(require redex)
(require "./peg.rkt")
(provide (all-defined-out))

; Syntax for parsing expression evaluation
(define-extended-language evalPeg Grammar
  [E (e s)]
  [R e ⊥]
  [D S ⊥]
  [S 0 1])