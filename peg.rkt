#lang racket
(require redex)
(require rackcheck)

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
     ⊥
     ε])


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
   (eval G ((! e) s) ε)]  
  
)

(define-metafunction evalPeg
  [(diff? natural_1 natural_1) #f]
  [(diff? natural_1 natural_2) #t]) 

(define-metafunction evalPeg
  [(botton? ⊥)        #f]
  [(botton? s_1)      #t])

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
                        )
           )  
)

(define E0 '(\epsilon))

(define (E1 Σ V)
        (append (map (lambda (e) (list e #f empty)) Σ)
                (map (lambda (e) (list e (sample (gen:one-of (list #t #f)) 1) (list e) )) V)
        )
)

#;[define (mkPegExpr ♣ p)
        (if (= p 0)
            (gen:one-of ♣)
            (gen:choice (gen:bind (mkPegExpr ♣ (l-1))
                                  (lambda (x) (gen:bind (mkPegExpr ♣ (l-1)) (lambda (y) (gen:const (mkSeq x y) )) ) ))
                        ()
                        ())
        )
]


(define (mkSeq e1 e2)
        (  `(• ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) (append (caddr e1) (caddr e2)) )
)
  


