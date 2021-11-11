#lang racket
(require redex)
(require  racket/set)
(require "./peg.rkt")
;(require "./WFverf.rkt")
(require rackcheck)

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

(define (genGrammar Γ Δ Σ n pmax)
       (if (>= n (length Γ))
           '∅
           (let* ([x (list-ref Γ n)]
                  [Δ_x (hash-ref Δ (car x)) ]
                  [t (car (sample (genPegExpr Γ Δ_x Σ (cadr x) pmax) 1) ) ]
                  [Δ1 (foldr (lambda (z Δ2) (hash-update Δ2 z (lambda (l) (set-union l (list (car x)) )  ) ) ) Δ (caddr t) )])

                  (display "Body ")
                  (display t)
                  (display " Generated for " )
                  (display x)
                  (display " With Γ = ")
                  (display Γ)
                  (display " and Δ = ")
                  (display Δ)
                  (display " and Δ_x = ")
                  (display Δ_x)
                  (display "\n")
                  (list (car x) (car t) (genGrammar Γ Δ1 Σ (+ n 1) pmax))
           )
        )
 )

(define (Δ-up ks x Δ )
    (foldr (lambda (z Δ) (hash-update Δ z (lambda (l) (set-union l (list x) ) )  null ) )  Δ ks )
 )
(define Γ0 '( (A #f (B C)) (B #t (C)) (C #t ()) ))
(define Γ1 '( (A #f ()) ) )
(define Γ2 '( (A #f ()) (B #f ()) ) )
(define (initΔ Γ)
       (foldr (lambda (t Δ)  (Δ-up (caddr t) (car t) Δ) ) (make-immutable-hash (map (lambda (t) [list (car t) (car t) ] ) Γ ) ) Γ) 
  )

(sample (genPegExpr Γ0 '(C) '(0 1)  #f 3) 10)


