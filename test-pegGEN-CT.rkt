#lang racket
(require redex)
(require  racket/set)
(require "./peg.rkt")
(require "./WFverf.rkt")
(require rackcheck)
(require "judgments.rkt")

(define myGen (make-pseudo-random-generator))

(define (h n)
  (- n 1)
  )


(define (genPegExpr Γ Δ Σ b p)
  (cond
    [(equal? p 0)  (gen:one-of (append (mkListVar Γ Δ b)
                                       (if b
                                           (list (list 'ε #t '()) ) 
                                           (map (lambda (x) (list x #f '())) Σ) )
                                       )) ]
    [(and (> p 0) b)    (gen:choice (gen:bind (genPegExpr Γ Δ Σ b (h p))
                                              (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ b (h p)) (lambda (s) (gen:const  (mkSeq t s) ) ) ) ) )
                                    (gen:bind (genPegExpr Γ Δ Σ #t (h p))
                                              (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ (car (sample gen:boolean 1 myGen)) (h p)) (lambda (s) (gen:const  (mkAlt t s) )) ) ) )
                                    (gen:bind (genPegExpr Γ Δ Σ #f (h p))
                                              (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ #t (h p)) (lambda (s) (gen:const  (mkAlt t s) )) ) ) )
                                    (gen:bind (genPegExpr Γ Δ Σ #f (h p))
                                              (lambda (t) (gen:const (mkNot t) ) ))
                                    (gen:bind (genPegExpr Γ Δ Σ #f (h p))
                                              (lambda (t) (gen:const (mkKle t) ) ))
                                    )]
    [(and (> p 0) (not b))  (gen:choice (gen:bind (genPegExpr Γ Δ Σ #t (h p))
                                                  (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ #f (h p)) (lambda (s) (gen:const  (mkSeq t s) ) ) ) ) )
                                        (gen:bind (genPegExpr Γ Δ Σ #f (h p))
                                                  (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ (car (sample gen:boolean 1 myGen)) (h p)) (lambda (s) (gen:const  (mkSeq t s) ) ) ) ) )
                                        (gen:bind (genPegExpr Γ Δ Σ #f (h p))
                                                  (lambda (t)  (gen:bind (genPegExpr Γ Δ Σ #f (h p)) (lambda (s) (gen:const  (mkAlt t s) )) ) ) )
                                        )]
    )  
  )


(define (Γ-val Γ v)
  (if (null? Γ)
      null
      (if (eq? (car (car Γ)) v)
          (car Γ)
          (Γ-val (cdr Γ) v) )
      )
  ) 

(define (mkListVar Γ Δ b)
  (map (lambda (y) (list (car y) (cadr y) (append (caddr y) (list (car y)) ) ))
       (filter (lambda (x) (and (eq? (cadr x) b) (not (member (car x) Δ))) ) Γ)
       )
  )

(define (mkSeq e1 e2)
  (list `(• ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) ( if (cadr e1)
                                                                (set-union (caddr e1) (caddr e2))
                                                                (caddr e1)
                                                                ) )
  )

(define (mkAlt e1 e2)
  (list `(/ ,(car e1) ,(car e2)) (or (cadr e1) (cadr e2)) (set-union (caddr e1) (caddr e2) ) )
  )

(define (mkKle e1)
  (list `(* ,(car e1) ) #t (caddr e1) )
  )

(define (mkNot e1 )
  (list `(! ,(car e1) ) #t ( caddr e1 ) )
  )

(define (genGrammar G Γ Δ Σ n pmax)
  (if (>= n (length Γ))
      (list G Γ)
      (let* ([x (list-ref Γ n)]
             [Δ_x (hash-ref Δ (car x)) ]
             [t (car (sample (genPegExpr Γ Δ_x Σ (cadr x) pmax) 1) ) ]
             [Δ1 (foldr (lambda (z Δ2) (hash-update Δ2 z (lambda (l) (set-union l (list (car x)) )  ) ) ) Δ (caddr t) )]
             [Γ1  (Γ-up Γ (car x) (cadr t) (caddr t)) ])

        ;(display "Body ")
        ;(display t)
        ;(display " Generated for " )
        ;(display x)
        ;(display " With Γ = ")
        ;(display Γ)
        ;(display " and Δ = ")
        ;(display Δ)
        ;(display " and Δ_x = ")
        ;(display Δ_x)
        ;(display "\n")
                  
        (genGrammar (list (car x) (car t) G) Γ1 Δ1 Σ (+ n 1) pmax)
        )
      )
  )

(define (Γ-item-up x y)
  (list (car x) (cadr x) (set-union (caddr x) y ))

  )

(define (Γ-up xs y b ty)
  (cond [(null? xs) null]
        [(eq? (car (car xs)) y) (cond [(eq? (cadr (car xs)) b)  (cons (list y b (set-union ty (caddr (car xs)))) (Γ-up (rest xs) y b ty))]
                                      [#t  (print (car xs))
                                           (print " attempt to update with ")
                                           (println b)]
                                      )] 
        [(member y (caddr (car xs)) )  (cons (Γ-item-up (car xs) ty) (Γ-up (rest xs) y b ty))]
        [#t (cons (car xs) (Γ-up (rest xs) y b ty)) ]
        )
  )

(define (Δ-up ks x Δ )
  (foldr (lambda (z Δ) (hash-update Δ z (lambda (l) (set-union l (list x) ) )  null ) )  Δ ks )
  )

(define (initΔ Γ)
  (foldr (lambda (t Δ)  (Δ-up (caddr t) (car t) Δ) ) (make-immutable-hash (map (lambda (t) [list (car t) (car t) ] ) Γ ) ) Γ) 
  )

(define (randPEG vars Σi p)
  (let* [(ts  (if (> (length vars) 0) (sample gen:boolean (length vars) myGen) ('()) ) )
         (bol  (car (sample gen:boolean 1 myGen)))
         (Γi (zipWith (lambda (v b) (list v b null)  ) vars ts))
         (Δi (initΔ Γi))
         (GΓ (genGrammar '∅ Γi Δi Σi 0 p) )
         (e0  (car (sample (genPegExpr (cadr GΓ) null Σi bol p) 1)) )]
    (list (car GΓ) (car e0) (cadr GΓ) ))
  )

(define (zip xs ys)
  (cond
    [(null? xs) null]
    [(null? ys) null]
    [#t (cons (list (car xs) (car ys) ) (zip (cdr xs) (cdr ys) ) )]
    )
  )

(define (zipWith func xs ys)
  (cond
    [(null? xs) null]
    [(null? ys) null]
    [#t (cons (func (car xs) (car ys) ) (zipWith func (cdr xs) (cdr ys) ) )]
    )
  )

(define Γ0 '( (A #f (B C)) (B #t (C)) (C #t ()) ))
(define Γ1 '( (A #f ()) ) )
(define Γ2 '( (A #f ()) (B #f ()) ) )
(define Γ3 '( (A #f (B C)) (B #t ()) (C #t ()) (D #t (C)) ))


;(sample (genPegExpr null '() '(0 1)  #f 3) 10)

(define (up2 n) (if (<= n 0) (list 0) (cons 0 (up2 (- n 1)) ) ))

(define (runTest v Σ p n)
  (for ([x n])
             
    (let ([pg (randPEG v Σ p) ])
      (println pg)
      (print "Grammar: ")
      (println (car pg))
      (if (is-WF (car pg) (cadr pg) '() )
          (display " Well formed \n")
          (display " NOT WF \n")
          )
      (display "\n")
      )
    )
  )

;pegar um elemento do headset gerado e procura no outroo
;ou ordenar os dois

(define (getHeadSet randPeg)
  (map (lambda (e)
         (list (car e) (rest e)))
       randPeg)
  )

(define (auxHeadSet hs-judg hs-off)
  (map (lambda (e)
         (if (member e (car hs-off))
             #t
             #f))
          (car hs-judg))
  )

(define (verfHeadSet randPeg)
  (define list-hs (getHeadSet (reverse (list-ref randPeg 2))))
  (define list-grammar (remove-last (separateGrammar (list-ref randPeg 0))))
  
  ;(println list-grammar)
  (map (lambda (peg grammar)
         (let ([judg (judgment-holds (⊢ ,list-hs ,(car (cdr grammar)) τ) τ)])
           ;(print "Judgm: ") (println (cdr (car judg)))
           ;(print "Elton: ") (println (cdr (car (cdr peg))))
           (if (not (member #f (auxHeadSet (cdr (car judg)) (cdr (car (cdr peg))))))
               peg
               (begin (display "Deu ruim\n\n") (list* (car peg) judg))
               ))
         )
       list-hs
       list-grammar
       )
  
  )

(define (separateGrammar grammar)
  (if (equal? grammar '∅)
      (list '∅)
      (cons (list (list-ref grammar 0) (list-ref grammar 1)) (separateGrammar (list-ref grammar 2))))) 
      

(define (remove-last lst)
  (if (null? (cdr lst))
      '()
      (cons (car lst) (remove-last (cdr lst)))))



;GERA A GRAMMAR
(define (genSymbols n)
  (define cont (build-list n values))
  (map (lambda (i)
         (string->symbol (format "X~a" i)))
       cont)
  )

;TESTEEEEE

(define (mkList n)
  (if (<= n 0)
      null
      (cons (- n 1) (mkList (- n 1)) )))


(define (geraTestes)
  (let* ([nV (sample (gen:integer-in 0 10) 1)]
         [vars (genSymbols (car nV)) ]
         [nT (sample (gen:integer-in 0 26) 1)]
         [Σ (mkList (car nT)) ]
         [p (sample (gen:integer-in 0 7) 1)])
    (for ([x 100])
      (verfHeadSet (randPEG vars Σ (car p)))))
  )
;(define peg (randPEG (genSymbols 3) (sample (gen:one-of '(0 1 2 3))) 2))
;peg
;(verfHeadSet peg)
;usar o redex-check
;gerador de dados aleatórios que gere o alfabeto e a gramática

; Loopinf is-WF.
;
; '((B (• (* 0) (/ A ε)) (A (• (• ε 1) (• B ε)) ∅)) (• (/ 1 A) (! 1)) ((A #f ()) (B #t (A))))
; '(0)'(1 ⊥)'(1). Interactions disabled; out of memory
;
; A → ε1Bε      
; B → 0*(A / ε)
;
;(1 / A) !1
;
;(is-WF '(B (• (* 0) (/ A ε)) (A (• (• ε 1) (• B ε)) ∅)) '(• (/ 1 A) (! 1)) '() )
;
;'((D (! (• (• 0 1) (/ 0 0)))
;  (C (* (• (• 0 1) (• ε 0)))
;  (B (• (/ (• C 0) (* 0)) (• (• C ε) (/ 1 0)))
;  (A (/ (/ (• B 0) (/ 1 D)) (• (/ B 0) (• C D))) ∅))))
;
; A → B0
;   / (1/ D)
;   / (B/0)CD
; B → (C0 / *0) C ε (1 / 0)
; C → (01ε0)*
; D → !(01(0 / 0))
;(* (• (/ B B) (/ B 0)))
;
;
;((A #t (C D B)) (B #f (C)) (C #t ()) (D #t ())))
;
;

