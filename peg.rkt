#lang racket
(require redex)
(provide (all-defined-out))


; Syntax of parsing expressions
(define-language Peg
   (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Terminal 
    (x variable-not-otherwise-mentioned))

; Syntax for a PEG grammar
(define-extended-language Grammar Peg
  [G (x e G) ∅] ; A grammar is a set of nonterminal definition
)

