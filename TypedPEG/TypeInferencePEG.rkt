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

(define-extended-language Inference Typed-Peg
  [state-exp (ψ φ exp)]
  [state (ψ φ constraint)]
  )

(define n 0)
(define (inc)
  (let ([x n])
    (begin (set! n (+ 1 n)) x)))

#;(define-metafunction Inference
    ⊕ : τ τ -> τ
    [(⊕ ( boolean hs) ( boolean_1 hs_1))
     ( (∨ boolean  boolean_1) (∪ hs hs_1) ) ])

#;(define-metafunction Inference
    ⊗ : τ τ -> τ
    [(⊗ ( #f hs) ( boolean_1 hs_1)) ( (AND #t  boolean_1) hs ) ]
    [(⊗ ( #t hs) ( boolean_1 hs_1)) ( (AND #f  boolean_1) (∪ hs  hs_1)) ])

#;(define-metafunction Inference
    ∨ : boolean boolean -> boolean
    [(∨ #f #f) #f]
    [(∨ _ _) #t])

#;(define-metafunction Inference
    AND : boolean boolean -> boolean
    [(AND #t #t) #t]
    [(AND _ _) #f])

#;(define-metafunction Inference
    ¬ : boolean -> boolean
    [(¬ #t) #t]
    [(¬ #f) #t])

#;(define-metafunction Inference
    ast : boolean -> boolean
    [(ast #t) (error)]
    [(ast #f) #t])

#;(define-metafunction Inference
    ∪ : hs hs -> hs
    [(∪ ∅ hs)   hs]
    [(∪ (x hs)  hs_1) (ccons (∈ x hs_1) x (∪ hs hs_1))])


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
;fazer a semantica de reescrita d

;meta função pra variável livre (n aparece ligada a quantificador)
;cap 5 - part1 
(define-metafunction Typed-Peg
  ∉ : α C -> boolean
  [(∉ _ ()) #t]
  [(∉ x (x x_1 ...)) #f]
  [(∉ x (x_1 x_2 ...)) (∉ x (x_2 ...))])

;mudar τ pra v

(define-metafunction Typed-Peg
  lcons : (α τ) φ -> φ
  [(lcons (α τ) ()) ((α τ))]
  [(lcons (α_1 τ) ((α_2 τ_2)... (α_1 τ_1) (α_3 τ_3)...)) (((α_2 τ_2)... (α_1 τ) (α_3 τ_3)...))]
  [(lcons (α τ) ((α_1 τ_1) ...)) ((α τ) (α_1 τ_1) ...)]
  )

(define-metafunction Typed-Peg
  apply-sub : φ (α τ) -> φ
  [(apply-sub () (α τ) ) ()]
  [(apply-sub ((α_1 α_2) (α_3 τ_3) ...) (α_2 τ) )
   (lcons (α_1 τ) (apply-sub ((α_3 τ_3) ...) (α τ) ))]
  [(apply-sub ((α_1 τ_1) (α_3 τ_3) ...) (α_2 τ) )
   (lcons (α_1 τ_1) (apply-sub ((α_3 τ_3) ...) (α τ) ))]
  
  )

(define-metafunction Typed-Peg
  compose : φ (α τ) -> φ
  [(compose
    ((α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))
   (lcons (α_3 τ_3) (apply-sub ((α_1 τ_1) (α_2 τ_2) ...) (α_3 τ_3))) ]
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
  ccons : boolean ty φ -> φ
  [(ccons #t (τ (b S)) ((τ_1 (b_1 S_1))... (τ (b_3 S_3)) (τ_2 (b_2 S_2)) ...))
   ((τ_1 (b_1 S_1))... (τ (b S)) (τ_2 (b_2 S_2)) ...)]
  [(ccons #f (τ (b S))
          ((τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...))
   ((τ (b S)) (τ_1 (b_1 S_1)) (τ_2 (b_2 S_2)) ...)])

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

   ;1 - falta mexer no ψ
   (--> (ψ φ ((def x : τ in C)))
        (ψ φ C)
        )
   ;2 - dois parenteses mesmo? barra alfa é um conj de alfas
   (--> (ψ φ (∧ (∃ α_1 C_1) C_2))
        (ψ φ (∃ α_1 (∧ C_1 C_2)))
        (side-condition (term (∉ α_1 C_2)))
        )
   ;3
   (--> (ψ φ ((b_1 S_1) ≡ (★ (#t S_2))))
        (ψ φ false)
        )
   ;4
   (--> (ψ φ (x ≡ (b S)))
        (ψ φ false)
        (side-condition (term (∈hs (x (φLook φ (ψLook ψ x))))))
        )
   ;5
   (--> (ψ φ (∧ C false))
        (ψ φ false)
        )
   ;6
   (--> (ψ φ (∧ false C))
        (ψ φ false)
        )
   ;7
   (--> (ψ φ (∧ C true))
        (ψ φ C)
        )
   ;8
   (--> (ψ φ (∧ true C))
        (ψ φ C)
        )
   ;9 - só jesus na causa dessa metafunction de união
   (--> (ψ φ (α ≡ (τ (b S))))
        (ψ (∪ φ (α (b S))) true)
        )
   ;10 - mesma coisa do 9
   (--> (ψ φ ((τ (b S)) ≡ α))
        (ψ (∪ φ (α (b S))) true)
        )
   ;11 - tem o <> entre os tipos, devemos aplicar a redução de novo?
   (--> (ψ φ ((b_1 S_1) ≡ (b_2 S_2)))
        (ψ φ (∧ (b_1 ≡ b_2) (S_1 ≡ S_2)))
        )
   )
  )

;metafunction que vai gerar os constraints com a metafunction e vai executar o reduction sobre o contrainst gerado
;resultado final: constraint true pra falar que a gramática é válida


