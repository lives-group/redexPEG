#lang racket
(require redex)

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
  [G ((x e) ...)] ; A grammar is a set of nonterminal definition
)

; Syntax for parsing expression evaluation
(define-extended-language evalPeg Grammar
  [E (e s)]
  [s (natural ...)
     ⊥])


(define-judgment-form evalPeg
  #:mode (eval I I O)
  #:contract (eval G E s)
  
  ;Terminal
  [-------------------------------- 
   (eval G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (diff? natural_1 natural_2))
   --------------------------------
   (eval G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (eval G (natural_1 ()) ⊥)]

  ;Empty
  [--------------------------------
   (eval G (ε s) s)]

  ;Choice
  [(eval G (e_1 s) s_1)
   (side-condition (botton? s_1))
   --------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  [(eval G (e_2 s) s_1)
  (side-condition (botton? s_1))  
   -------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

  [------------------------------
   (eval G ((/ e_1 e_2) ()) ⊥)]

  ;Sequence
  [(eval G (e_1 s) s_1)
   (eval G (e_2 s_1) s_2)
   -------------------------------
   (eval G ((• e_1 e_2) s) s_2)]

  [(eval G (e_1 s) ⊥)
   ------------------------------
   (eval G ((• e_1 e_2) s) ⊥)]

  ;Not
  [(eval G (e s) s_1)
   (side-condition (botton? s_1))
   -------------------------------
   (eval G ((! e) s) ⊥)]

  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((! e) s) s)]  
  
)

(define-metafunction evalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 


(define-metafunction evalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])




;tests for terminal
(display "Terminal\n")
(judgment-holds (eval () (1 (1 1 1)) s) s)
(judgment-holds (eval () (1 (2 1 1)) s) s)
(judgment-holds (eval () (1 ()) s) s)

;tests for choice
(display "\nChoice\n")
(judgment-holds (eval () ((/ 1 2) (1 1 1)) s) s)
(judgment-holds (eval () ((/ 1 2) (2 1 1)) s) s)
(judgment-holds (eval () ((/ 1 2) ()) s) s)

(display "\nSequence\n")
(judgment-holds (eval () ((• 1 2) (1 2 3)) s) s)
(judgment-holds (eval () ((• 1 2) (2 2 3)) s) s)
(judgment-holds (eval () ((• 1 2) (1 1 3)) s) s)

(display "\nNot\n")
(judgment-holds (eval () ((! 1) (1 2 3)) s) s)
(judgment-holds (eval () ((! 1) (2 2 3)) s) s)
(judgment-holds (eval () ((! 1) ()) s) s)

(display "\nEmpty\n")
(judgment-holds (eval () (ε (2 2)) s) s)
(judgment-holds (eval () (ε (1 2 3 4 5 6 7)) s) s)

;Não terminal
(judgment-holds (eval ((A ε) (B 1)) ((/ B A) (2 2 3 4 5 6 7)) s) s)

;ε* -> vai entrar em loop
;excluir exp loop = exp bem formadas
;rastreia exp mal formadas
;julgamento well formed 


