#lang racket
(require redex)
(require "./peg.rkt")
(define +Gen (make-pseudo-random-generator))
(require rackcheck)

#;(define-metafunction Peg
    [(Gpeg natural) peg]
  
    )


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



;assando a peg pra ficar prontinha!
;Σ -> Terminal alphabet (ex: 0 1 2)
;V -> Non-Terminals list (ex: A B)
;p -> Peg depth
;n -> Number of pegs we want it to generate with SAMPLE 
(define (bakePeg Σ V p n)
  (define X0 (E0 Σ V))
  (display X0)
  (display "\n")
  (sample (mkPegExpr X0 p) n)
  )

;E0: list of terms: (expression, nullable, headset)
;ex:((ε #t ()) (0 #f ()) (1 #f ()) (2 #f ()) (A #t (A)) (B #t (B)))
(define (E0 Σ V)
  (append (list (list 'ε #t empty) )
          (map (lambda (e) (list e #f empty)) Σ)
          (map (lambda (e) (list e (car (sample (gen:one-of (list #t #f)) 1)) (list e) )) V)
          )
  )

(define (gen:non-ε g)
  (gen:filter g (lambda (t) (not (eq? (car t) 'ε) )) ) )

(define (kruskal V return-list rest cont)
  (define raiz (list-ref V (random (length V))))
  (if (equal? cont 0)
      (set! rest (remove raiz rest))
      rest)
  
  (display "Raiz: ")
  (display raiz)
  (display " - ")
  (define copy-rest rest)
  (set! copy-rest (remove raiz copy-rest))
  (display "Rest: ")
  (display copy-rest)
  (display "\n")
  (define tam (length copy-rest))
  (if (equal? (length copy-rest) 0)
      return-list
  
      (kruskal V
               (list return-list (list raiz (list-ref copy-rest (- tam 1))))
               (remove (list-ref copy-rest (- tam 1)) rest)
               (add1 cont)))
  
  
  )

;(kruskal '(A B C D) '() '(A B C D) 0)

;Generates Peg
;♣: E0 -> Initial list generated with the function E0
(define (mkPegExpr ♣ p)
  (if (= p 0)
      (gen:one-of ♣)
      (gen:choice (gen:bind (mkPegExpr ♣ (- p 1))
                            (lambda (x) (gen:bind ( mkPegExpr ♣ (- p 1) )
                                                  (lambda (y) (gen:const (mkSeq x y) )) ) ))
                  (gen:bind (mkPegExpr ♣ (- p 1))
                            (lambda (x) (gen:bind (mkPegExpr ♣ (- p 1))
                                                  (lambda (y) (gen:const (mkAlt x y) )) ) ))
                  (gen:bind (gen:filter (mkPegExpr ♣ (- p 1)) (lambda (x) (not (cadr x)) ))
                            (lambda (y) (gen:const (mkKle y) ) ))
                  (gen:bind (mkPegExpr ♣ (- p 1))
                            (lambda (y) (gen:const (mkNot y) ) ))
                  (mkPegExpr ♣ (- p 1))
                  )
      )
  )



;Generates peg with •
(define (mkSeq e1 e2)
  (if(eq? (car e1) 'ε)
     e2
     (if (eq? (car e2) 'ε)
         e1
         (list `(• ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) ( if (cadr e1)
                                                                       (set-union (caddr e1) (caddr e2))
                                                                       (caddr e1)
                                                                       ) )
         )
     )
  )

;Generates peg with /
(define (mkAlt e1 e2)
  (list `(/ ,(car e1) ,(car e2)) (and (cadr e1) (cadr e2)) (set-union (caddr e1) (caddr e2) ) )
  )

;Generates peg with *
(define (mkKle e1)
  (list `(* ,(car e1) ) #t (caddr e1) )
  )

;Generates peg with !
(define (mkNot e1 )
  (list `(! ,(car e1) ) #t ( caddr e1 ) )
  )
(bakePeg '(0 1 2) '(A B) 2 1)



;NAO FUNCIONA MAS É UMA TENTATIVA

(define (filterGrammar g)
  (gen:filter g (lambda (t) (equal? #f (cadr t)))))

(define (filterE0 ♣)
  (filter (lambda (e)
            (not (cadr e))
            
            )
          ♣
          )
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
;(display "funçao do elton\n")
;(En (E0 '(0 1) '(A B)) 1)
;(retorna)
(define (mkGrammar ♣ p)
  (if (= p 0)
      (gen:one-of (filterE0 ♣))
      (gen:choice (gen:bind ( mkGrammar ♣ (- p 1))
                            (lambda (x) (gen:bind ( mkGrammar ♣ (- p 1) )
                                                  (lambda (y) (gen:const (mkSeq x y) )) ) ))
                  (gen:bind (mkGrammar ♣ (- p 1))
                            (lambda (x) (gen:bind (mkGrammar ♣ (- p 1))
                                                  (lambda (y) (gen:const (mkAlt x y) )) ) ))
                  (gen:bind (gen:filter (mkGrammar ♣ (- p 1)) (lambda (x) (not (cadr x)) ))
                            (lambda (y) (gen:const (mkKle y) ) ))
                  (gen:bind (mkGrammar ♣ (- p 1))
                            (lambda (y) (gen:const (mkNot y) ) ))
                  (mkGrammar ♣ (- p 1))
                  )
      )
  )



#|

;gerar o par do parsing com o tipo:
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
|#

;GERA PEG NO JEITO ANTIGO
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

;GERA GRAMÁTICA (ERRADO)
(define (genGrammar Σ p n L e rep grammar)
  (if (equal? (length n) 1)
      (list (car n) (car (sample (genPeg Σ p n L) 1)) '∅)
      (list (car n) (car (sample (genPeg Σ p n L) 1)) (genGrammar Σ p (cdr n) L e rep grammar)))
      
  )

;GERA SÍMBOLOS (X0, X1, X2...)
;n -> numero de NT
(define (genSymbols n)
  (define cont (build-list n values))
  (map (lambda (i)
         (string->symbol (format "X~a" i)))
       cont)
  )


;GERA O STATE COMPLETO (GRAMÁTICA PEG-ENTRADA ELEMENTO-CONSUMIDO...)
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
(display "\nGera Peg\n")
(sample (genPeg '(0 1 2) 3 (genSymbols 3) '()) 1)
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

#|

(define (get-result l)

  (if (eq? (list-ref (car l) 7) 'suc)
      (list (list-ref (car l) 5))
      (list '⊥))

  )

(display "\nFunçao setar Peg \n")
(define (setPeg L) ;fica na forma de (grammar exp input)
  
  (define grammar (list-ref L 0))
  (define peg (list-ref L 1))
  (define entry (list-ref L 2))
  
  (define redct-expr (list grammar '⊢ '() peg '↓ entry '() '⊥ '(0)))
  (display redct-expr)
  (display "\n")
  (define judg-expr (list 'eval grammar (list peg entry) 's))
  (display judg-expr)
  (display "\n")

  (test-equal 
   (judgment-holds (eval ,grammar (,peg ,entry) s) s)
   (get-result (apply-reduction-relation* red redct-expr)))

  (test-results)

  )

(display "\n \n")
(setPeg '((A (/ 1 2) ∅) (/ A 2) (1 2 3)))


;testar mais a implementação do elton
;verificar o resultado, o tipo
;refazer os testes pra ver se ta tudo certo
;randPeg
;funcao pra verificar se oq saiu do a #f () condiz com a gramatica

|#




