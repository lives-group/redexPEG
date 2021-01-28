#lang racket
(require redex)

(define-language Peg
   (e natural   ; Terminal
     (alt e e)  ; Choice
     (seq e e)  ; Sequence
     (star e)   ; Repetition
     (not e)    ; Not complement
     ϵ          ; Empty
    x)          ; Non-Temrinal 
    (g ((x e) ...) )  ; Non terminal definition
    (x variable-not-otherwise-mentioned))

