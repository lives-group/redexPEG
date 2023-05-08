#lang racket

(require redex)

(provide all-defined-out)

(define-language Peg
  (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Temrinal 
  (x variable-not-otherwise-mentioned))

(define-extended-language Typed-Peg Peg
  [τ α
     (b S)
     (× τ τ)
     (+ τ τ)
     (★ τ)
     (! τ)]
  [t x
     b
     S
     τ]
  [C true
     false
     (t ≡ t)
     (∧ C C C ...)
     (∃ α C)
     (def x : τ in C)]
  [CEval hole
     (∧ CEval C C ...)
     ;(∧ C CEval C ...)
     (∃ α CEval)
     (def x : τ in CEval)]
  [α x 
     (v natural)]
  [constraint τ t C]
  [S (x ...) ∅]
  [b #t
     #f]
  [x variable-not-otherwise-mentioned]
  [ty (τ (b S))]
  [ψ ((x τ)...)]
  [φ ((α τ)...)]
  [ctx (ψ φ)]
  [exp (e τ) ]
  [reduc (ctx constraint)]
  [hs (x hs)
      ∅])


(define-extended-language Grammar Typed-Peg
  [G ((x e) ...) ∅]
  )


(define-extended-language Inference Typed-Peg
  [state-exp (ψ φ exp)]
  [state (ψ φ constraint)]
  )

(define n 0)
(define (inc)
  (let ([x n])
    (begin (set! n (+ 1 n)) x)))

; tc -> trivial-constraints
(define-metafunction Inference
  tc : e τ -> C
  [(tc ε τ) (α_1 ≡ (#t ∅)) (where α_1 ,(term (v ,(inc))))]

  [(tc natural τ) (τ ≡ (#f ∅))]

  [(tc x τ) (x ≡ τ)]

  [(tc (/ e_1 e_2) τ) (∧ (∃ α_1 (tc e_1 α_1))
                         (∃ α_2 (tc e_2 α_2))
                         (τ ≡ (+ α_1 α_2)))
                      (where α_1 ,(term (v ,(inc))))
                      (where α_2 ,(term (v ,(inc))))]

  [(tc (• e_1 e_2) τ) (∧ (∃ α_1 (tc e_1 α_1))
                         (∃ α_2 (tc e_2 α_2))
                         (τ ≡ (× α_1 α_2)))
                      (where α_1 ,(term (v ,(inc))))
                      (where α_2 ,(term (v ,(inc))))]

  [(tc (! e_1) τ) (∧ (∃ α_1 (tc e_1 α_1))
                     (τ ≡ (! α_1)))
                  (where α_1 ,(term (v ,(inc))))]

  [(tc (* e_1) τ) (∧ (∃ α_1 (tc e_1 α_1))
                     (τ ≡ (★ α_1)))
                  (where α_1 ,(term (v ,(inc))))])


#|(term (tc ε (#t ∅)))
(term (tc 1 (#f ∅)))
(term (tc A (#f ∅)))
(term (tc (/ 2 2) τ))
(term (tc (• 1 2) (#f ∅)))
(term (tc (! 1) (#f ∅)))
(term (tc (* 1) (#t ∅)))
;(term (tc (() () ((* ε) (#t ∅))))) ; dá erro, mas é pra dar!
(term (tc (• (/ 1 3) 2) (#f ∅)))
(term (tc (* (/ 1 2)) (#f ∅)))
(term (tc (! (* (/ 1 2))) (#f ∅)))

|#

(define-metafunction Grammar
  gc : G τ -> C
  [(gc ∅ τ) true]
  [(gc () τ) true]
  [(gc ((x e) (x_1 e_1) ...) τ)
   (∃ α_1 (def x : α_1 in (∧ (tc e α_1) (gc ((x_1 e_1) ...) τ))))]
  )

(term (gc ∅ (#t ∅)))
(term (gc () (#t ∅)))
(term (gc ((A 1)) (#t ∅)))

;fazer a semantica de reescrita d

;meta função pra variável livre (n aparece ligada a quantificador)
;cap 5 - part1

(define-metafunction Typed-Peg
  [(append () ()) ()]
  [(append (α ...) ()) (α ...)]
  [(append () (α ...)) (α ...)]
  [(append (α_1 ...) (α_2 ...)) (α_1 ... α_2 ...)]
  )

(define-metafunction Typed-Peg
  attach-α : C (α ...) -> (α ...)
  [(attach-α true (α ...)) (α ...)]
  [(attach-α false (α ...)) (α ...)]
  [(attach-α (t_1 ≡ t_2) (α ...)) (α ...)]
  [(attach-α (∧ C) (α ...)) (attach-α C (α ...))]
  [(attach-α (∧ C_1 C_2 ...) (α ...) ) (append (attach-α C_1 (α ...)) (attach-α (∧ C_2 ...) (α ...)))]
  [(attach-α (∃ α C) (α_1 ...)) (attach-α C (α α_1 ...))]
  [(attach-α (def x : τ in C) (α ...)) (attach-α C (α ...))]
  )


(define-metafunction Typed-Peg
  ∉ : α (α ...) -> boolean
  [(∉ _ ()) #t]
  [(∉ α (α α_1 ...)) #f]
  [(∉ α (α_1 α_2 ...)) (∉ α (α_2 ...))])

;mudar τ pra v

(define-metafunction Typed-Peg
  lcons : (α τ) φ -> φ
  [(lcons (α τ) ()) ((α τ))]
  [(lcons (α_1 τ) ((α_2 τ_2) ... (α_1 τ_1) (α_3 τ_3) ...))
   ((α_2 τ_2) ... (α_1 τ) (α_3 τ_3) ...)]
  [(lcons (α τ) ((α_1 τ_1) ...)) ((α τ) (α_1 τ_1) ...)]
  )

(define-metafunction Typed-Peg
  ψcons : (x τ) ψ -> ψ
  [(ψcons (x τ) ()) ((x τ))]
  [(ψcons (x τ) ((x_2 τ_2)... (x τ_1) (x_3 τ_3) ...))
   (((x_2 τ_2)... (x_1 τ) (x_3 τ_3) ...))]
  [(ψcons (x τ) ((x_1 τ_1) ...)) ((x τ) (x_1 τ_1) ...)]
  )

;criar uma função lcons que insere um par (variável, tipo) no psi
;

(define-metafunction Typed-Peg
  apply-sub : φ (α τ) -> φ
  [(apply-sub () (α τ) ) ()]
  [(apply-sub ((α_1 α_2) (α_3 τ_3) ...) (α_2 τ) )
   (lcons (α_1 τ) (apply-sub ((α_3 τ_3) ...) (α_2 τ) ))]
  [(apply-sub ((α_1 τ_1) (α_3 τ_3) ...) (α_2 τ) )
   (lcons (α_1 τ_1) (apply-sub ((α_3 τ_3) ...) (α_2 τ) ))]
  )

(define-metafunction Typed-Peg
  subs : φ τ -> τ
  [(subs ((α_2 τ_2) ... (α_1 τ_1) (α_3 τ_3) ...) α_1) τ_1]
  [(subs φ τ) τ]
  )

(define-metafunction Typed-Peg
  compose : φ (α τ) -> φ
  [(compose () (α τ) ) ((α τ))]
  [(compose
    ((α τ) ... (α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))
   (lcons (α_3 τ_3) (apply-sub ((α τ) ... (α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))) ]
  )

(define-metafunction Typed-Peg
  ∪ : φ (τ (b S)) -> φ
  [(∪ () (τ (b S)))   ((τ (b S)))]
  [(∪ ((τ_1 (b_1 S_1)) (τ_2 (_ _)) ...)  (τ (b S)))
   (ccons (∈ τ ((τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...))
          (τ (b S))
          (∪ ((τ_2 (b_2 S_2)) ...) (τ (b S))))])

(define-metafunction Typed-Peg
  ∈ : τ φ -> boolean
  [(∈ _ ()) #f]
  [(∈ τ ((τ (b_1 S_1)) (τ_2 (b_2 S_2)) ...)) #t]
  [(∈ τ ((τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...)) (∈ τ ((τ_2 (b_2 S_2)) ...))])

(define-metafunction Typed-Peg
  ccons : boolean (α τ) φ -> φ
  [(ccons #t (α τ) ((α_1 τ_1)... (α_2 τ_2) (α_3 τ_3) ...))
   ((α_1 τ_1)... (α_2 τ) (α_2 τ_3) ...)]
  [(ccons #f (α τ)
          ((α_1 τ_1) (α_2 τ_2) ...))
   ((α τ) (α_1 τ_1) (α_2 τ_2) ...)])

(define-metafunction Typed-Peg
  samevar : τ τ -> boolean
  [(samevar τ τ) #t]
  [(samevar τ _) #f])

; PROCURANDO NO ENV ψ E RETORNANDO O TIPO
(define-metafunction Typed-Peg
  [(ψLook ((x_1 τ_1) (x_2 τ_2)...) x_1) τ_1]
  [(ψLook ((x_1 τ_1) (x_2 τ_2)...) x_3) (ψLook ((x_2 τ_2) ...) x_3)] 
  )

; PROCURANDO NO ENV φ E RETORNANDO O HEAD
(define-metafunction Typed-Peg
  [(φLook ((b_1 S_1) (b_2 S_2) ...) (b_1 S_1)) S_1]
  [(φLook ((b_1 S_1) (b_2 S_2) ...) (b_3 S_3)) (φLook ((τ_2 (b_2 S_2))...) τ_3)] 
  )

; VERIFICA SE O X PERTENCE AO HEAD DAQUELE TIPO
(define-metafunction Typed-Peg
  [(∈hs _ ()) #f]
  [(∈hs x (x x_1 ...)) #t]
  [(∈hs x (x_1 x_2 ...)) (∈hs x (x_2 ...))])

(define constraint-solve
  (reduction-relation 
   Typed-Peg
   #:domain (ψ φ C)

   ; regras Elton
   (--> (ψ φ (in-hole CEval (∃ α_1 true)))
        (ψ φ (in-hole CEval true))
        )

   (--> (ψ φ (in-hole CEval (∃ α_1 false)))
        (ψ φ (in-hole CEval false))
        )

   ;1
   (--> (ψ φ ((def x : τ in C)))
        ((ψcons ψ (subs φ α_1)) φ C)
        )
   
   ;2
   (--> (ψ φ (in-hole CEval (∧ (∃ α_1 C_1) C_2)))
        (ψ φ (in-hole CEval (∃ α_1 (∧ C_1 C_2))))
        (side-condition (term (∉ α_1 (attach-α C_2 ()))))
        )
   ;3
   (--> (ψ φ (in-hole CEval ((b_1 S_1) ≡ (★ (#t S_2)))))
        (ψ φ (in-hole CEval false))
        )
   ;4
   (--> (ψ φ (in-hole CEval (x ≡ (b S))))
        (ψ φ (in-hole CEval false))
        (side-condition (term (∈hs (x (φLook φ (ψLook ψ x))))))
        )
   ;5
   (--> (ψ φ (in-hole CEval (∧ C false C_1 ...)))
        (ψ φ (in-hole CEval false))
        )
   ;6
   (--> (ψ φ (in-hole CEval (∧ false C C_1 ...)))
        (ψ φ (in-hole CEval false))
        )
   ;7
   (--> (ψ φ (in-hole CEval (∧ C true C_1 ...)))
        (ψ φ (in-hole CEval C))
        )
   ;8
   (--> (ψ φ (in-hole CEval (∧ true C C_1 ...)))
        (ψ φ (in-hole CEval C))
        )
   ;9
   (--> (ψ φ (in-hole CEval (α ≡ (b S))))
        (ψ (compose φ (α (b S))) (in-hole CEval true))
        )
   ;10
   (--> (ψ φ (in-hole CEval ((b S) ≡ α)))
        (ψ (compose φ (α (b S))) (in-hole CEval true))
        )
   ;11
   (--> (ψ φ (in-hole CEval ((b_1 S_1) ≡ (b_2 S_2))))
        (ψ φ (in-hole CEval (and (=b? b_1 b_2) (=S? S_1 S_2))))
        )
   )
  )

(define-metafunction Typed-Peg
  and : boolean boolean -> C
  [(and #t #t) true]
  [(and _ _) false]
  )

(define-metafunction Typed-Peg
  =b? : boolean boolean -> boolean
  [(=b? #t #t) #t]
  [(=b? _ _) #f]
  )

(define-metafunction Typed-Peg
  =S? : S S -> boolean
  [(=S? () ()) #t]
  [(=S? () (x x_1 ...)) #f]
  [(=S? (x x_1 ...) ()) #f]
  [(=S? (x_1 x ...) (x_2 ... x_1 x ...))
   (=S? (x ...) (x_2 ... x ...))]
  )

;metafunction que vai gerar os constraints com a metafunction e vai executar o reduction sobre o contrainst gerado
;resultado final: constraint true pra falar que a gramática é válida

;; Testes

;fazer metafunction com gramática
;fazer testes com propriedade gerando gramática e comparando o tipo
;com gerador de tipo (Rodrigo)