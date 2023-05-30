#lang racket

(require redex)
(require typed-peg)
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
     (! τ)
     error]
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
  [S (x ...)]
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
      ])

(define-extended-language Grammar Typed-Peg
  [G ((x e) ...) ]
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
  [(tc ε τ) (τ ≡ (#t ()))]

  [(tc natural τ) (τ ≡ (#f ()))]

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



;gc - grammar constraint
(define-metafunction Grammar
  gc : ((x e) ...) -> C
  [(gc ()) true]
  [(gc ((x e) (x_1 e_1) ...))
   (∧ (∃ α_1 (def x : α_1 in (tc e α_1))) (gc ((x_1 e_1) ...) ))])

(define-metafunction Grammar
  grmConstraint : G -> C
  [(grmConstraint (((x e) ... ) e_1)) (∧ (gc ((x e) ...) ) (∃ α_1 (tc e_1 α_1) ))]
  )


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
        (ψ φ (in-hole CEval (mand (=b? b_1 b_2) (=S? S_1 S_2))))
        )
   ;A outra
   (--> (ψ φ (in-hole CEval (τ_1 ≡ τ_2)))
          (ψ φ (in-hole CEval (equiv φ τ_1 τ_2)))
          )
   )
  )

; Aux. attach-α
(define-metafunction Typed-Peg
  [(append () ()) ()]
  [(append (α ...) ()) (α ...)]
  [(append () (α ...)) (α ...)]
  [(append (α_1 ...) (α_2 ...)) (α_1 ... α_2 ...)]
  )

;VERIFICA OS ALFAS LIGADOS E FORMA UMA LISTA COM ELES
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
  [(subs φ (★ τ)) (★ (subs φ τ))]
  [(subs φ (! τ)) (! (subs φ τ))]
  [(subs φ (+ τ_1 τ_2)) (+ (subs φ τ_1) (subs φ τ_2))]
  [(subs φ (× τ_1 τ_2)) (× (subs φ τ_1) (subs φ τ_2))]
  [(subs φ τ) τ]
  )

(define-metafunction Typed-Peg
  compose : φ (α τ) -> φ
  [(compose () (α τ) ) ((α τ))]
  [(compose
    ((α τ) ... (α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))
   (lcons (α_3 τ_3) (apply-sub ((α τ) ... (α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))) ]
  )


; PROCURANDO NO ENV ψ E RETORNANDO O TIPO
(define-metafunction Typed-Peg
  #;[(ψLook () )]
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


; AND PARA REDUCTION
(define-metafunction Typed-Peg
  mand : boolean boolean -> C
  [(mand #t #t) true]
  [(mand _ _) false]
  )

(define-metafunction Typed-Peg
  =b? : boolean boolean -> boolean
  [(=b? #t #t) #t]
  [(=b? _ _) #f]
  )

(define-metafunction Typed-Peg
  =S? : S S -> boolean
  [(=S? () ()) #t]
  ;[(=S? ∅ ∅) #t]
  [(=S? () (x x_1 ...)) #f]
  [(=S? (x x_1 ...) ()) #f]
  [(=S? (x_1 x ...) (x_2 ... x_1 x ...))
   (=S? (x ...) (x_2 ... x ...))]
  )

(define-metafunction Typed-Peg
  klee : τ -> τ
  [(klee (#f S) ) (#t S)]
  [(klee α) α]
  [(klee _) error])

(define-metafunction Typed-Peg
  not : τ -> τ
  [(not (_ S) ) (#t S)]
  [(not α) α]
  [(not _) error])

(define-metafunction Typed-Peg
  ⊕ : τ τ -> τ
  [(⊕ (b S) (b_1 S_1)) (,(or (term b) (term b_1)) (union S S_1))]
  [(⊕ τ_1 τ_2) (+ τ_1 τ_2)])

(define-metafunction Typed-Peg
  ⊗ : τ τ -> τ
  [(⊗ (b S) (b_1 S_1)) (,(and (term b) (term b_1)) (union S (⇒ b S_1)))]
  [(⊗ τ_1 τ_2) (× τ_1 τ_2)])

(define-metafunction Typed-Peg
  ⇒ : b S -> S
  [(⇒ #t S) S]
  [(⇒ _ _) ()])

(define-metafunction Typed-Peg
  union : S S -> S
  [(union () ()) ()]
  ;[(union ∅ ∅) ∅]
  ;[(union ∅ S) S]
  ;[(union S ∅) S]
  [(union () S) S]
  [(union S ()) S]
  [(union (x_1 ...) (x_2 ...)) ,(set-union (term (x_1 ...)) (term (x_2 ...)))]
  #;[(union (x x_1 ...) (x_2 ...)) (x (union (x_1 ...) (x_2 ...)))]
  )

(define-metafunction Typed-Peg
  τeval : τ -> τ
  [(τeval (★ τ)) (klee (τeval τ))]
  [(τeval (+ τ_1 τ_2)) (⊕ (τeval τ_1) (τeval τ_2))]
  [(τeval (× τ_1 τ_2)) (⊗ (τeval τ_1) (τeval τ_2))]
  [(τeval (! τ)) (not (τeval τ))]
  [(τeval τ) τ])


(define-metafunction Typed-Peg
  auxEquiv : boolean -> C
  [(auxEquiv #t) true]
  [(auxEquiv #f) false]
  )

(define-metafunction Typed-Peg
  equiv : φ τ τ -> C
  [(equiv  φ τ_1 τ_2) (auxEquiv ,(equal? (term (τeval (subs φ τ_1)))
                               (term (τeval (subs φ τ_2)))))]
  )

; fazer eq e eval(pegar um tau e se casar com algum construtores)

;metafunction que vai gerar os constraints com a metafunction e vai executar o reduction sobre o contrainst gerado
;resultado final: constraint true pra falar que a gramática é válida

;; Testes

;fazer metafunction com gramática
;fazer testes com propriedade gerando gramática e comparando o tipo
;com gerador de tipo (Rodrigo)


(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ())))))
(apply-reduction-relation* constraint-solve (term (() () (tc 1 (#f ())))))
;(apply-reduction-relation* constraint-solve (term (() () (tc A (#f ())))))
(apply-reduction-relation* constraint-solve (term (() () (tc (/ 2 2) τ))))
(apply-reduction-relation* constraint-solve (term (() () (tc (* 2) τ))))


;O QUE FAZER COM A GRAMÁTICA
;A METAFUNÇÃO EQUIV É PRA USAR NA LINHA 173 MESMO?

