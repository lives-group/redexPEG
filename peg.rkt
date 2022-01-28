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
; Syntax for parsing expression evaluation
(define-extended-language simpleEvalPeg Grammar
  [E (e s)]         ;An evaluation is comprised of a PEG and a input 
  [s (natural ...)  ; An input can be: * A squence of terminal symbols
     ⊥              ;                  * Booton, meaning an parser error 
     ε])            ;                  * Empty string (there is nothing to be consumed !)



