#lang racket
(require redex)
(require  racket/set)
(require "./peg.rkt")
(define +Gen (make-pseudo-random-generator))
(require rackcheck)

;n -> List of non-terminal names
;L -> List
;P -> List depth
;Σ -> List of elements of an alphabet
(define (Gpeg n L P Σ)
  
  (if (equal? P 0) 
      (random 10 +Gen)
      (display "lol")
      )

  )

(define myGen (make-pseudo-random-generator))


;nullable: anulavel ou nao (consome ou nao) proibe de gerar algo nulavel? 

(define (genPeg Σ p L nullable)
  (if (equal? p 0)
      (if nullable
          (gen:choice (gen:one-of Σ) (gen:const 'ε))
          (gen:one-of Σ))
      (gen:choice (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) L nullable)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1) ) L nullable) (lambda (s) (gen:const  `(• ,t ,s)) ) ) ) );;colocar condiçao aqui?
                  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) L nullable)
                            (lambda (t)  (gen:bind (genPeg Σ (- p (+ (random p myGen) 1)) L nullable) (lambda (s) (gen:const  `(/ ,t ,s))) ) ) )
                  (gen:bind (genPeg Σ (- p 1) L nullable)
                            (lambda (t) (gen:const `(! ,t)) ))
                  (gen:bind (genPeg Σ (- p 1) L #f)
                            (lambda (t) (gen:const `(* ,t)) ))
                  (gen:one-of L)
                  )
      )  
  )

;retornar uma lista
;E0: lista de termos: (expressão, nullable, headset)
;p: profundidade
#;(define (genInitAllPeg Σ V)
  (append (list (list 'ε #t null))
          (map (lambda (t) (list t #f null)) Σ)
          (map (lambda (v) (list v (car (sample (gen:one-of '(#f #t)) 1)) (list v))) V))
  )

#;(define (genPegWF E0 p)
  (if (equal? p 0)
      (gen:one-of E0)
      (gen:choice (gen:bind (genPegWF E0 (- p 1))
                            (lambda (e1) (gen:bind (genPegWF E0 (- p 1))
                                                   (lambda (e2) (gen:const (mkSeq e1 e2)))))
                            )
                  (gen:bind (genPegWF E0 (- p 1))
                            (lambda (e1) (gen:bind (genPegWF E0 (- p 1))
                                                   (lambda (e2) (gen:const (mkAlt e1 e2)))))
                            )
                  (gen:bind (gen:filter (genPegWF E0 (- p 1))
                                        (lambda (t) (not (cadr t))))
                            (lambda (e) (gen:const (mkRep e)))
                                                   )
                            )
      )
  )

#;(define (genPegExpr Σ V p)
  (define e0 (genInitAllPeg Σ V))
  (display e0)
  (display "\n")
  (sample (genPegWF e0 p) 10)
  )

#;(define (mkSeq e1 e2)
  (list `(• ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) (if (cadr e1)
                                                               (append (caddr e1) (caddr e2))
                                                               (caddr e1)))
  )
;(mkSeq '(3 #t (3)) '((• 2 ε) #f (4)))

#;(define (mkAlt e1 e2)
  (list `(/ ,(car e1) ,(car e2)) (or (cadr e1) (cadr e2)) (append (caddr e1) (caddr e2))
        )
  )

#;(define (mkRep e)
  (list `(* ,(car e)) #t (caddr e))
        
  )

#;(define myGen (make-pseudo-random-generator))

#;(define (genPeg Σ p n L)
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

; Constrói uma expressão de altura zero
(define (bakeZeroExpr Ce Σ nll)
        (if nll
               ('ε)
               (gen:one-of Ce ) )
)

; Definir um gerador de PEG independetente de tipo 
(define (bakeAnyTypePeg V Σ p)
               (gen:one-of (append V (append Σ (list 'ε ))) )
)

(define (rpartList l)
        (call-with-values (lambda () (partition (lambda (x) (car (sample gen:boolean 1)) ) l) )
                          (lambda (z w) (list z w) ))
  )

(define (bakeSeqNull Γ Σ H p)
        
        (let ([H1H2  (rpartList H) ])
             (gen:bind (bakePeg Γ Σ (first H1H2) #t (- p 1))
                       (lambda (e1)  (gen:bind (bakePeg Γ Σ (second H1H2) #t (- p 1))
                                               (lambda (e2) (gen:const `(• ,e1 ,e2)) ))))
         )  
  )

(define (bakeSeqNulle1 Γ Σ H p)
        
        (let ([H1H2  (rpartList H) ])
             (gen:bind (bakePeg Γ Σ (first H1H2) #t (- p 1))
                       (lambda (e1)  (gen:bind (bakePeg Γ Σ (second H1H2) #f (- p 1))
                                               (lambda (e2) (gen:const `(• ,e1 ,e2)) ))))
         )  
  )

(define (bakeSeqNonNulle1 Γ Σ H p)
        
        (gen:bind (bakePeg Γ Σ H #f (- p 1))
                  (lambda (e1)  (gen:bind (bakeAnyTypePeg (map first Γ) Σ 1)
                                          (lambda (e2) (gen:const `(• ,e1 ,e2)) ))))
           
  )

(define (bakeKle Γ Σ H p)
        
        (gen:bind (bakePeg Γ Σ H #f (- p 1))
                  (lambda (e1) (gen:const `(* ,e1 )) ))        
  )

(define (bakeNot Γ Σ H p)

        (gen:bind (bakePeg Γ Σ H #f (- p 1))
                  (lambda (e1)  (gen:const `(! ,e1 )) ) )       
  ) 


(define (bakableVar Γ H nll)
        (filter (lambda (x) (and (eq? (cadr x) nll) (equal? (caddr x) H)) ) Γ)
)

#;(define (bakeVar Γ H nll)
        (if (= (len H) 1)
            (car H)
            ()
         )
  )

; Γ = '( (Var,Bool, HeadSet) )
(define (bakePeg Γ Σ H nll p)
    (cond
          [(= p 0)              (gen:one-of Σ)]
          [(and (null? H) nll)  (gen:choice (bakeSeqNull Γ Σ H p)
                                            (bakeKle Γ Σ H p)
                                            (bakeNot Γ Σ H p)
                                            (gen:const 'ε) )]
          
          [(and (null? H) (not nll))  (gen:choice (bakeSeqNulle1 Γ Σ H p)
                                                  (bakeSeqNonNulle1 Γ Σ H p)
                                                  (gen:one-of Σ) 
                                      )]
          [(and (not (null? H)) nll)  (gen:choice (bakeSeqNull Γ Σ H p)
                                                  (bakeKle Γ Σ H p)
                                                  (bakeNot Γ Σ H p) )]
          [(and (not (null? H)) (not nll))  (gen:choice (bakeSeqNulle1 Γ Σ H p)
                                                        (bakeSeqNonNulle1 Γ Σ H p)
                                                         )]
    )
  )

(define (genBodyFor e0 p v)
        (gen:filter (mkPegExpr e0 p) (lambda (z) (and (and (cadr z) (cadr v)) (not (subset? (list (car v)) (caddr z))) ) ))
  )

(define (satisfy v xs)
        (list (car v) (filter (lambda (z) (and (and (cadr z) (cadr v)) (not (member (car v) (caddr z))) ) ) xs))
 )

(define (E0 Σ V)
        (append (list (list 'ε #t empty) )
                (map (lambda (e) (list e #f empty)) Σ)
                (map (lambda (e) (list e (car (sample (gen:one-of (list #t #f)) 1)) (list e) )) V)
        )
)

(define (mkRandHeadSet v s)
        (list v (filter (lambda (x) (< (car (sample (gen:integer-in 1 100) 1)) 50) ) s))
)

(define (En e0 n)
        (if (= n 0)
            e0
            ( append (En e0 (- n 1))
                     (for/list [(ee  (En e0 (- n 1)) )]
                               (append (for/list [(ed  (En e0 (- n 1)) )]
                                                 (list (mkAlt ee ed) (mkSeq ee ed)) 
                                        )
                                        (list (mkNot ee) (mkKle ee))
                                )
                     )
                     
             )
        )
  )

(define (gen:non-ε g)
         (gen:filter g (lambda (t) (not (eq? (car t) 'ε) )) ) )

[define (mkPegExpr ♣ p)
        (if (= p 0)
            (gen:one-of ♣)
            (gen:choice (gen:bind ( mkPegExpr ♣ (- p 1))
                                  (lambda (x) (gen:bind ( mkPegExpr ♣ (- p 1) )
                                                        (lambda (y) (gen:const (mkSeq x y) )) ) ))
                        (gen:bind (mkPegExpr ♣ (- p 1))
                                  (lambda (x) (gen:bind (mkPegExpr ♣ (- p 1))
                                                        (lambda (y) (gen:const (mkAlt x y) )) ) ))
                        (gen:bind (gen:filter (mkPegExpr ♣ (- p 1)) (lambda (x) (not (cadr x)) ))
                                  (lambda (y) (gen:const (mkKle y) )  ))
                        (gen:bind (mkPegExpr ♣ (- p 1))
                                  (lambda (y) (gen:const (mkNot y) )  ))
                        (mkPegExpr ♣ (- p 1)) 
            )
        )
]



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

;(bakePeg '(0 1) '(A B C) 2 5)

