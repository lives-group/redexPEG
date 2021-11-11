#lang racket
(require redex)
(require "./peg.rkt")
;(require "./WFverf.rkt")
(define +Gen (make-pseudo-random-generator))
(require rackcheck)

#;(define-metafunction Peg
    [(Gpeg natural) peg]
  
    )
;trocar o nome desse arq aqui que testee ta mt feio

;n -> lista de nomes de nao terminais
;L -> lista
;P -> profundidade lista
;Σ -> lista de elementos de um alfabeto
(define (Gpeg n L P Σ)
  
  (if (equal? P 0) 
      (random 10 +Gen)
      (display "lol")
      )

  )

(define myGen (make-pseudo-random-generator))


;nullable: anulavel ou nao (consome ou nao) proibe de gerar algo nulavel? 
;L: lista de nao terminais
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
(define (genInitAllPeg Σ V)
  (append (list (list 'ε #t null))
          (map (lambda (t) (list t #f null)) Σ)
          (map (lambda (v) (list v (car (sample (gen:one-of '(#f #t)) 1)) (list v))) V))
  )

(define (genPegWF E0 p)
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

(define (genPegExpr Σ V p)
  (define e0 (genInitAllPeg Σ V))
  (display e0)
  (display "\n")
  (sample (genPegWF e0 p) 10)
  )

(define (mkSeq e1 e2)
  (list `(• ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) (if (cadr e1)
                                                               (append (caddr e1) (caddr e2))
                                                               (caddr e1)))
  )
;(mkSeq '(3 #t (3)) '((• 2 ε) #f (4)))

(define (mkAlt e1 e2)
  (list `(/ ,(car e1) ,(car e2)) (or (cadr e1) (cadr e2)) (append (caddr e1) (caddr e2))
        )
  )

(define (mkRep e)
  (list `(* ,(car e)) #t (caddr e))
        
  )
         
#;(define (genPeg Σ p L nullable)
    (if (equal? p 0)
        (if nullable
            (list (gen:choice (gen:one-of Σ) (gen:const 'ε)) nullable '∅)
            (list (gen:one-of Σ) #f '∅))
        (list (gen:choice (gen:bind (car (genPeg Σ (- p (+ (random p myGen) 1)) L nullable))
                                    (lambda (t)  (gen:bind (car (genPeg Σ (- p (+ (random p myGen) 1) ) L nullable)) (lambda (s) (gen:const  `(• ,t ,s)) ) ) ) ) ;;colocar condiçao aqui?
                          (gen:bind (car (genPeg Σ (- p (+ (random p myGen) 1)) L nullable))
                                    (lambda (t)  (gen:bind (car (genPeg Σ (- p (+ (random p myGen) 1)) L nullable)) (lambda (s) (gen:const  `(/ ,t ,s))) ) ) )
                          (gen:bind (car (genPeg Σ (- p 1) L nullable))
                                    (lambda (t) (gen:const `(! ,t)) ))
                          (gen:bind (car (genPeg Σ (- p 1) L #f))
                                    (lambda (t) (gen:const `(* ,t)) ))
                          (gen:one-of L) 
                          )  nullable '∅)
        )  
    )


;gerar o par do parsing com o tipo ??
;lista de pares (nt, (nullable, prefixo de variaveis))

;definir quantos nao terminais
;pra cada n terminal damos o genPeg
; e -> peg correspondente pra pegar os NT e achar a gramática
;receber a lista de gramática - L
;usar o map pra gerar uma peg pra cada nt
;é pra gerar bem formada já
;usa o is-WF ??

;gerar uma expressão pro nt: verifica se a exp é bem formada (se caso a exp tiver um nt tbm, verifica se o não terminal ja existe.....)


#;(define (genGramar Σ p n L e rep grammar)
  
    (if (and  (not (empty? e)) (member (car (list e)) n) )
        (genGrammar Σ p n L (rest (list e)) (list rep (car (list e))) (cons grammar (cons (car (list e))
                                                                                          (sample (genPeg Σ (car (sample (gen:one-of '(0 1 2)) 1)) n L) 1))))
        (if (empty? e)
            "null";;retorna null pq cdr do e fica '()
            (genGrammar Σ p n L (rest e) rep grammar))      )
      
    )

#;(define (genGramar Σ p n L e rep grammar)
  
    (map (lambda (i)
           (list* i (sample (genPeg Σ p n L) 1))) ;;ta gerando gramatica errada, "fechando os termos"
         n)
      
    )

(define (genGrammar Σ p n L e rep grammar)
  (if (equal? (length n) 1)
      (list (car n) (car (sample (genPeg Σ p n L) 1)) '∅)
      (list (car n) (car (sample (genPeg Σ p n L) 1)) (genGrammar Σ p (cdr n) L e rep grammar)))
      
  )


;n -> numero de NT
(define (genSymbols n)
  (define cont (build-list n values))
  (map (lambda (i)
         (string->symbol (format "X~a" i)))
       cont)
  )

(define (genEntrada)
  (gen:choice (gen:one-of '(0 1 2 3 4 5 6 7 8 9)) (gen:const 'ε))
  )


#;(define (genState Σ p n L cont)
  (define peg (sample (genPeg Σ p n L) cont))
  (define empty-grammar '(∅))
  (define grammar (genGrammar Σ p n L (car peg) '() '()))
  (define entrada (sample (gen:one-of '(0 1 2 3)) cont))

  (if (test-WF (list grammar '⊢ '() (car peg) '↓ entrada '() '⊥ '(0)))
      (list grammar '⊢ '() (car peg) '↓ entrada '() '⊥ '(0))
      (genState Σ p n L cont))
  )


;n -> numero de nao terminal
;L -> lista
;p -> profundidade lista
;Σ -> lista de elementos de um alfabeto
;cont -> deve ser 1

;(sample (gen:one-of '(a b c)) 10)
#;(display "\nGera Peg\n")
#;(sample (genPeg '(0 1 2) 1 (genSymbols 3) '()) 1)
#;(cdr (sample (genPeg '(A B C) 1 (genSymbols 3) '()) 1))

#;(display "\nGera Gramática\n")
#;(genGrammar '(0 1 2) 1 (genSymbols 3) '() (sample (genPeg '(0 1 2) 1 (genSymbols 3) '()) 1) '() '())

#;(display "\nGera Estado\n")
#;(genState '(0 1 2) 1 (genSymbols 3) '() 1)
#;(test-WF (genState '(0 1 2) 1 (genSymbols 3) '() 1))
#;(genState '(0 1 2) 1 (genSymbols 3) '() 1)
#;(genState '(0 1 2) 2 (genSymbols 3) '() 1)
#;(genState '(0 1 2) 3 (genSymbols 3) '() 1)
#;(genState '(0 1 2) 3 (genSymbols 3) '() 1)


