#lang racket
(require redex)
(require rackcheck)
(provide (all-defined-out))

; Syntax of parsing expressions
(define-language Peg
   (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Temrinal 
    (x variable-not-otherwise-mentioned))

; Syntax for a PEG grammar
(define-extended-language Grammar Peg
  [G (x e G) ∅] ; A grammar is a set of nonterminal definition
  )



; Look-up for a nontermila on a grammar
  
(define-metafunction Grammar
  [(lookupG (x e G) x) e]
  [(lookupG (x_1 e G) x_2) (lookupG G x_2)]
  [(lookupG ∅ x) ,(error 'lookupG "not found: ~e" (term x))]
  )


