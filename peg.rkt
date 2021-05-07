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
     x)          ; Non-Terminal 
    (x variable-not-otherwise-mentioned))

; Syntax for a PEG grammar
(define-extended-language Grammar Peg
  [G (x e G) ∅] ; A grammar is a set of nonterminal definition
)

; Syntax for parsing expression evaluation
(define-extended-language evalPeg Grammar
  [E (e s)]
  [s (natural ...)
     ⊥]
  [R e ⊥])

(define-judgment-form evalPeg
  #:mode (lookup I I O)
  #:contract (lookup G x R)
  
  [--------------------------------
   (lookup (x_1 e G) x_1 e)]

  [--------------------------------
   (lookup ∅ x ⊥)]

  [(lookup G x_2 R)
   (side-condition (diffs? x_1 x_2))
   --------------------------------
   (lookup (x_1 e_1 G) x_2 R)]
  
)

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

  ;Repetition
  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((* e) s) s)]

  [(eval G (e s) s_1)
   (side-condition (botton? s_1))
   (eval G ((* e) s_1) s_2)
   -------------------------------
   (eval G ((* e) s) s_2)]

  ;Non-Terminal
  [(lookup G x e)     
   (eval G (e s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  
  [(lookup G x ⊥)
   --------------------------------
   (eval G (x s) ⊥)]

  
)


(define-metafunction evalPeg
  [(equal? x x) #t]
  [(equal? x e) #f])

(define-metafunction evalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 

(define-metafunction evalPeg
  [(diffs? x_1 x_1) #f]
  [(diffs? x_1 x_2) #t])

(define-metafunction evalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])

(define-metafunction evalPeg
  [(not-botton? ⊥)        #t]
  [(not-botton? s_1)      #f])


;tests for terminal
(display "Terminal\n")
(judgment-holds (eval ∅ (1 (1 1 1)) s) s)
(judgment-holds (eval ∅ (1 (2 1 1)) s) s)
(judgment-holds (eval ∅ (1 ()) s) s)

;tests for choice
(display "\nChoice\n")
(judgment-holds (eval ∅ ((/ 1 2) (1 1 1)) s) s)
(judgment-holds (eval ∅ ((/ 1 2) (2 1 1)) s) s)
(judgment-holds (eval ∅ ((/ 1 2) ()) s) s)

(display "\nSequence\n")
(judgment-holds (eval ∅ ((• 1 2) (1 2 3)) s) s)
(judgment-holds (eval ∅ ((• 1 2) (2 2 3)) s) s)
(judgment-holds (eval ∅ ((• 1 2) (1 1 3)) s) s)

(display "\nNot\n")
(judgment-holds (eval ∅ ((! 1) (1 2 3)) s) s)
(judgment-holds (eval ∅ ((! 1) (2 2 3)) s) s)
(judgment-holds (eval ∅ ((! 1) ()) s) s)

(display "\nEmpty\n")
(judgment-holds (eval ∅ (ε (2 2)) s) s)
(judgment-holds (eval ∅ (ε (1 2 3 4 5 6 7)) s) s)

(display "\nRepetition\n")
(judgment-holds (eval ∅ ((* 2) (4 5 6 7)) s) s)
(judgment-holds (eval ∅ ((* 2) ()) s) s)
(judgment-holds (eval ∅ ((* 2) (2 2 2 2 3 4)) s) s) ;era pra consumir todos os 2, na teoria
;(judgment-holds (eval ∅ ((* ε) (2 2 2 3)) s) s) ;não tire esse ; a menos que saiba o que esta fazendo

;Não terminal
(display "\nNon-Terminal\n")
(judgment-holds (eval (A 2 ∅) (A (2 3 4 5 6 7)) s) s)
(judgment-holds (eval (B 1 (A 2 ∅)) (A (2 3 4 5 6 7)) s) s) ;cebolas na gramatica
(judgment-holds (eval (B 1 (A B ∅)) (A (1 2 3 4 5 6 7)) s) s)
(judgment-holds (eval (B 1 (A B ∅)) (C (1 2 3 4 5 6 7)) s) s)
(judgment-holds (lookup (B 1 (A 2 ∅)) C R) R)
(judgment-holds (lookup ∅ C R) R)

;ε* -> vai entrar em loop
;excluir exp loop = exp bem formadas
;rastreia exp mal formadas
