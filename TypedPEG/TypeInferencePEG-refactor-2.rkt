#lang racket

(require redex)
(require typed-peg)
(provide (all-defined-out))

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
     (clone τ x)]
  [t x τ]
  [C b
     (t ≡ t)
     (∧ C C)
     (def x : τ in C)]
  [CEval hole
         (∧ CEval C)
         (∧ C CEval)]
  [α (v natural)]
  [S (x ...)]
  [b #t #f]
  [x variable-not-otherwise-mentioned]
  [ψ ((x τ)...)]
  [φ ((α τ)...)]
  )

(define-extended-language Grammar Typed-Peg
  [G ((x e) ...) ]
  )

(define counter 1)
(define (reset) (set! counter 1))
(define (fresh-var) (list 'v (inc) ))

(define start_var '(v 0))

(define (inc)
  (let ([x counter])
    (begin (set! counter (+ 1 counter)) x)))

(define-metafunction Typed-Peg
  get-nullable : τ -> b
  ([get-nullable (b S)] b)
  ([get-nullable _] (get-nullable (τeval τ)))
  )

(define-metafunction Typed-Peg
  get-headset : τ -> b
  ([get-headset (b S)] S)
  ([get-headset _] (get-headset (τeval τ)))
  )

(define-metafunction Typed-Peg
  tcMonad : e τ natural -> (C natural)
  [(tcMonad ε τ natural) ((τ ≡ (#t ())) natural)]
  [(tcMonad natural_1 τ natural) ((τ ≡ (#f ())) natural)]
  [(tcMonad x τ natural) (
                          (∧ (x ≡ (v natural)) (τ ≡ (clone (v natural) x)))
                          ,(+ (term natural) 1))]
  [(tcMonad x τ natural) ((τ ≡ ((get-nullable τ) (x (get-headset τ)))) natural)
                         (side-condition (term (valid-hs x (τeval τ)))) ]
  
  [(tcMonad (/ e_1 e_2) τ natural) ((∧
                                     (∧
                                      C_1
                                      C_2)
                                     (τ ≡ (+ (v natural) (v natural_1))))
                                    natural_2)
                                   (where (C_1 natural_1) (tcMonad e_1 (v natural) ,(+ (term natural) 1)))
                                   (where (C_2 natural_2) (tcMonad e_2 (v natural_1) ,(+ (term natural_1) 1)))
                                   ]

  [(tcMonad (• e_1 e_2) τ natural) ((∧
                                     (∧
                                      C_1
                                      C_2)
                                     (τ ≡ (× (v natural) (v natural_1))))
                                    natural_2)
                                   (where (C_1 natural_1) (tcMonad e_1 (v natural) ,(+ (term natural) 1)))
                                   (where (C_2 natural_2) (tcMonad e_2 (v natural_1) ,(+ (term natural_1) 1)))
                                   ]

  [(tcMonad (! e_1) τ natural) ((∧
                                 C
                                 (τ ≡ (! (v natural))))
                                natural_1)
                               (where (C natural_1) (tcMonad e_1 (v natural) ,(+ (term natural) 1)))
                               ]

  [(tcMonad (* e_1) τ natural) ((∧
                                 C
                                 (τ ≡ (★ (v natural))))
                                natural_1)
                               (where (C natural_1) (tcMonad e_1 (v natural) ,(+ (term natural) 1)))
                               ]
  )
  

; tc -> trivial-constraints
(define-metafunction Typed-Peg
  tc : e τ -> C
  [(tc ε τ) (τ ≡ (#t ()))]

  [(tc natural τ) (τ ≡ (#f ()))]

  #;[(tc x (b S) φ) (x ≡ (b S))] ;quanto temos um tau unico (instanciado e completo (b S))
  ;quando ele é uma variavel  (alfa), ai geramos duas restrições:
  ;uma que vai garantir que ele n ocorra no proprio headset
  ;que coloca ele no headset dele

  #;[(tc x α φ) (x ≡ (τeval (subs α)))]

  [(tc x τ) (∧ (x ≡ α_1) (τ ≡ (clone α_1 x))) (where α_1 ,(fresh-var))]

  [(tc x τ) (τ ≡ ((get-nullable τ) (x (get-headset τ))))
            (side-condition (term (valid-hs x (τeval τ)))) ]
  
  [(tc (/ e_1 e_2) τ) (∧ (∧  (tc e_1 α_1)
                             (tc e_2 α_2))
                         (τ ≡ (+ α_1 α_2)))
                      (where α_1 ,(fresh-var))
                      (where α_2 ,(fresh-var))]

  [(tc (• e_1 e_2) τ) (∧ (∧ (tc e_1 α_1)
                            (tc e_2 α_2))
                         (τ ≡ (× α_1 α_2)))
                      (where α_1 ,(fresh-var))
                      (where α_2 ,(fresh-var))]

  [(tc (! e_1) τ) (∧ (tc e_1 α_1)
                     (τ ≡ (! α_1)))
                  (where α_1 ,(fresh-var))]

  [(tc (* e_1) τ) (∧ (tc e_1 α_1)
                     (τ ≡ (★ α_1)))
                  (where α_1 ,(fresh-var))])



;gc - grammar constraint
(define-metafunction Grammar
  gc : ((x e) ...) -> C
  [(gc ()) #t]
  [(gc ((x e) (x_1 e_1) ...))
   (∧ (def x : α_1 in (tc e α_1)) (gc ((x_1 e_1) ...) )) (where α_1 fresh-var)])

;gc - grammar constraint
(define-metafunction Grammar
  gc1Monad : ψ G C natural -> ((ψ C) natural)
  [(gc1Monad ψ () C natural ) ((ψ C) natural)]
  [(gc1Monad ψ ((x e) (x_1 e_1) ...) C natural)
   (gc1Monad (ψcons (x (v natural)) ψ)
             ((x_1 e_1) ...)
             (c-and C C_1)
             natural_1)
   (where (C_1 natural_1) (tcMonad e (v natural) ,(+ (term natural) 1)))
   ])

(define (verify-natural l natural)
  (if (natural? (car l))
      (car l)
      natural))

(define (verify-C list-C list-natural)
  (display list-C)
  (if (natural? (car list-natural))
      (car list-C)
      list-C))

;gc - grammar constraint
(define-metafunction Grammar
  gc1 : ψ G C -> (ψ C)
  [(gc1 ψ () C) (ψ C)]
  [(gc1 ψ ((x e) (x_1 e_1) ...) C) 
   (gc1 (ψcons (x α) ψ)
        ((x_1 e_1) ...)
        (c-and C (tc e α )))
   (where α ,(fresh-var))])


(define-metafunction Grammar
  grm->constraint : G e -> (ψ φ C)
  [(grm->constraint G e)
   (ψ
    ()
    (c-and C  (tc e α) ))
   (where α ,start_var) 
   (where (ψ C) (gc1 () G #t)) ])

(define start_var_2 0) 
(define-metafunction Grammar
  grm->constraint-monad : G e -> (ψ φ C)
  [(grm->constraint-monad G e)
   (ψ
    ()
    (c-and C_2 C_1))
   (where (C_1 natural_1) (tcMonad e (v 0) 1))
   (where ((ψ C_2) natural_2) (gc1Monad () G #t natural_1)) ])

(define (inferType G e)
  (apply-reduction-relation* constraint-solve (genConstraint G e)
                             #:cache-all? #t
                             #:stop-when stop?
                             ))



(define (genConstraint G e)
  (term (grm->constraint-monad ,G ,e) ))

(define (stop? ctx)
  (match ctx
    [(list _ _ #t) #t]
    [_  #f]))

(define constraint-solve
  (reduction-relation 
   Typed-Peg
   #:domain (ψ φ C)

   ;1
   (--> (ψ φ C)
        ((subsψ ψ φ_1) φ_1 (subsf φ_1 C_1))
        (where (natural φ_1 C_1) (Csimplify φ 0 C) )
        (side-condition (> (term natural) 0) )
        "r-1")
   ;3
   (--> (ψ φ (in-hole CEval ( t ≡ (★ (#t S)))))
        (ψ φ #f)
        "r-3")
   ;4
   (--> (ψ φ (in-hole CEval (x ≡ (b S))))
        (ψ φ #f)
        (where (b_1 S_1) (ψLook ψ x))
        (side-condition  (term (∈hs x S_1) ) ) 
        "r-4")
   ;4,5
   #;(--> (ψ φ (in-hole CEval (x ≡ α)))
          (ψ φ (in-hole CEval (x ≡ (subs φ α)) ))
          (side-condition (term (in-ϕ φ α) ))
          "regra-4eMeio")
   ;4,75
   (--> (ψ φ (in-hole CEval (x ≡ α)))
        (ψ φ (in-hole CEval (α ≡ (subs φ (ψLook ψ x))) ))
        (side-condition (and (not (term (in-ϕ φ α) ))
                             (term (in-ψ ψ x) ) ))
        "regra-4eTresQuartos")
   ;5
   (--> (ψ φ (in-hole CEval (∧ C #f)))
        (ψ φ #f)
        "r-5")
   ;6
   (--> (ψ φ (in-hole CEval (∧ #f C)))
        (ψ φ #f)
        "r-6")
   ;7
   (--> (ψ φ (in-hole CEval (∧ C #t)))
        (ψ φ (in-hole CEval C))
        "r-7")
   ;8
   (--> (ψ φ (in-hole CEval (∧ #t C)))
        (ψ φ (in-hole CEval C))
        "r-8")
   ;9
   #;(--> (ψ φ (in-hole CEval (α ≡ (b S))))
          (ψ (compose φ (α (b S))) (in-hole CEval #t))
          "r-9")
   ;10
   #;(--> (ψ φ (in-hole CEval ((b S) ≡ α)))
          (ψ (compose φ (α (b S))) (in-hole CEval #t))
          "r-10")
   ;11
   (--> (ψ φ (in-hole CEval ((b_1 S_1) ≡ (b_2 S_2))))
        (ψ φ (in-hole CEval ,(and (term (=b? b_1 b_2)) (term (=S? S_1 S_2)) )))
        "r-11")
   ;A outra
   #;(--> (ψ φ (in-hole CEval (α ≡ τ)))
          (ψ φ (in-hole CEval (α ≡ (τeval (subs φ τ))) ))
          #;(side-condition (not (term (∉ α_1 (attach-α (τ_1 ≡ τ_2) ())))))
          (side-condition (and (term (τeval? τ ))
                               (not (term (ground τ)))
                               (term (vars-subset φ (vars τ))) ))
          "r-outra")
   )
  )

(define-metafunction Typed-Peg
  in-ϕ : φ α -> boolean 
  [(in-ϕ ( (α_1 τ_1) ... (α τ) (α_2 τ_2) ...) α) #t]
  [(in-ϕ _ _) #f]
  )

(define-metafunction Typed-Peg
  in-ψ : ψ x -> boolean 
  [(in-ψ ( (x_1 τ_1) ... (x τ) (x_2 τ_2) ...) x) #t]
  [(in-ψ _ _) #f]
  )

(define-metafunction Typed-Peg
  ground : τ -> boolean 
  [(ground (b S) ) #t]
  [(ground _) #f]
  )

(define-metafunction Typed-Peg
  τeval? : τ -> boolean 
  [(τeval? (b S)) #t]
  [(τeval? (★ τ)) (τeval? τ)]
  [(τeval? (+ τ_1 τ_2)) ,(and (term (τeval? τ_1)) (term (τeval? τ_2)))]
  [(τeval? (× (#f S) τ_2)) #t]
  [(τeval? (× τ_1 τ_2)) ,(and (term (τeval? τ_1)) (term (τeval? τ_2)))]
  [(τeval? (! τ)) (τeval? τ)]
  [(τeval? _) #f])

(define-metafunction Typed-Peg
  Csimplify : φ natural C  -> (natural φ C) 
  [(Csimplify φ natural (α ≡ (b S)) ) (,(+ (term natural) 1) (compose φ ((α (b S))) ) #t)
                                      (side-condition (not (term (in-ϕ φ α))))]
  [(Csimplify φ natural (α ≡ (b S)) ) (natural φ ((subs φ α) ≡ (b S)))
                                      (side-condition (term (in-ϕ φ α )))]
  [(Csimplify φ natural (t ≡ τ) )  (natural φ (t ≡ (τeval (subs φ τ))) )
                                   (side-condition (not (term (ground τ))) )]
  [(Csimplify φ natural (∧ C_1 C_2)) (natural_2 φ_2 (c-and C_3 C_4))
                                     (where (natural_1 φ_1 C_3) (Csimplify φ natural C_1))
                                     (where (natural_2 φ_2 C_4) (Csimplify φ_1 natural_1 C_2))]
  [(Csimplify φ natural C) (natural φ C)]
  )

#;(define-metafunction Typed-Peg
    Csimplify : φ φ C  -> (φ C) 
    [(Csimplify φ φ_nw (α ≡ (b S)) ) ((φcons (α (b S)) φ_nw) #t)
                                     (side-condition (not (term (in-ϕ φ α))))]
    [(Csimplify φ φ_nw (α ≡ (b S)) ) (φ_nw (subs φ α) ≡ (b S)) (side-condition (term (in-ϕ φ α )))]
    [(Csimplify φ φ_nw (t ≡ τ) )  (φ_nw (t ≡ (τeval (subs φ τ)))) (side-condition (not (term (ground τ))) )]
    [(Csimplify φ φ_nw (∧ C_1 C_2)) ((compose φ_1 φ_2) (c-and C_3 C_4))
                                    (where (φ_1 C_3) (Csimplify φ φ_nw C_1))
                                    (where (φ_2 C_4) (Csimplify φ φ_nw C_2))]
    [(Csimplify φ φ_nw C) (φ_nw C)]
    )

(define-metafunction Typed-Peg
  c-and : C C -> C 
  [(c-and  #t C) C]
  [(c-and  C #t) C]
  [(c-and C_1 C_2) (∧ C_1 C_2)]
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

#;(define-metafunction Typed-Peg
    ψcons : (x τ) ψ -> ψ
    [(ψcons (x τ) ( (x_2 τ_2) ...))  ((x τ) (x_2 τ_2) ...)]
    )

(define-metafunction Typed-Peg
  ψcons : (x τ) ψ -> ψ
  [(ψcons (x τ) ()) ((x τ))]
  [(ψcons (x τ) ((x τ_1) (x_2 τ_2) ...))  (((x_1 τ) (x_2 τ_2) ...))]
  [(ψcons (x τ) ((x_1 τ_1) (x_2 τ_2)...)) ((x τ) (x_1 τ_1) (x_2 τ_2)...)
                                          (side-condition (symbol<? (term x) (term x_1)))]
  [(ψcons (x τ) ((x_1 τ_1) (x_2 τ_2)...)) ((x_1 τ_1) (x_3 τ_3) ...)
                                          (where ((x_3 τ_3) ...) (ψcons (x τ) ((x_2 τ_2)... ) ))]
  )

(define-metafunction Typed-Peg
  α<? : α α -> boolean
  [(α<? (v natural_1) (v natural_2)) ,(< (term natural_1) (term natural_2))]
  )

(define-metafunction Typed-Peg
  φcons : (α τ) φ -> φ
  [(φcons (α τ) ()) ((α τ))]
  #;[(φcons (α τ) ((α τ_1) (α_2 τ_2)...)) ((α τ_1) (α_2 τ_2)...)]
  [(φcons (α τ) ((α_1 τ_1) (α_2 τ_2)...)) ((α τ) (α_1 τ_1) (α_2 τ_2)...)
                                          (side-condition (term (α<?  α α_1)))]
  [(φcons (α τ) ((α_1 τ_1) (α_2 τ_2)...)) ((α_1 τ_1) (α_3 τ_3) ...)
                                          (where ((α_3 τ_3) ...) (φcons (α τ) ((α_2 τ_2)... ) ))]
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
  [(subs φ (clone τ_1 x)) (clone (subs φ τ_1) x)]
  [(subs φ τ) τ]
  )

(define-metafunction Typed-Peg
  subsf : φ C -> C
  [(subsf φ (τ ≡ τ_1)) ((subs φ τ) ≡ (subs φ τ_1) )]
  [(subsf φ (x ≡ τ_1)) (x ≡ (subs φ τ_1) )]
  [(subsf φ (τ_1 ≡ x)) ((subs φ τ_1) ≡ x)]
  [(subsf φ (∧ C_1 C_2)) (∧ (subsf φ C_1) (subsf φ C_2))]
  [(subsf φ b) b]
  )

(define-metafunction Typed-Peg
  subsψ : ψ φ -> ψ
  [(subsψ () φ)    ()]
  [(subsψ ((x τ) (x_1 τ_1) ...)  φ) (ψcons (x (subs φ τ)) (subsψ ((x_1 τ_1) ...) φ) )]
  )

(define-metafunction Typed-Peg
  vars : τ -> (α ...)
  [(vars α_1) (α_1)]
  [(vars (★ τ)) (vars τ)]
  [(vars (! τ)) (vars τ)]
  [(vars (+ τ_1 τ_2)) (vars-union (α_1 ...) (α_2 ...))
                      (where (α_1 ...) (vars τ_1))
                      (where (α_2 ...) (vars τ_2))]
  [(vars (× τ_1 τ_2)) (vars-union (α_1 ...) (α_2 ...))
                      (where (α_1 ...) (vars τ_1))
                      (where (α_2 ...) (vars τ_2))]
  [(vars (b S)) ()]
  )

(define-metafunction Typed-Peg
  vars-subset :  φ (α ...) -> boolean
  [(vars-subset ((α_2 τ_2) ...) ())  #t]
  [(vars-subset () (α α_1 ... ))     #f] 
  [(vars-subset ((α_2 τ_2) ... (α_1 τ_1) (α_3 τ_3) ...)     (α_1  α_4 ...))
   (vars-subset ((α_2 τ_2) ... (α_3 τ_3) ...) (α_4 ...))]
  [(vars-subset ((α_2 τ_2) ...) (α_1 α_4 ...)) #f]
  )

(define-metafunction Typed-Peg
  vars-union : (α ...) (α ...) -> (α ...)
  [(vars-union (α_1 ...) ())  (α_1 ...)]
  [(vars-union () (α_1 ...) )  (α_1 ...)]
  [(vars-union (α_1 α_2 ...) (α_3 ... α_1  α_4 ...)) (vars-union (α_1 α_2 ...) (α_3 ... α_4 ...))]
  [(vars-union (α_1 α_2 ...) (α_3 α_4 ...)) (vars-union (α_1 α_2 ... α_3) (α_4 ...))]
  )

(define-metafunction Typed-Peg
  compose : φ φ -> φ
  [(compose () φ) φ]
  [(compose ((α_2 τ_2) (α_3 τ_3) ...) φ)
   (φcons (α_2 (subs φ τ_2)) (compose ((α_3 τ_3) ...) φ)) ]
  )


; PROCURANDO NO ENV ψ E RETORNANDO O TIPO
(define-metafunction Typed-Peg
  ψLook : ψ x -> τ
  [(ψLook ((x_1 τ_1) (x_2 τ_2)...) x_1) τ_1]
  [(ψLook ((x_1 τ_1) (x_2 τ_2)...) x_3) (ψLook ((x_2 τ_2) ...) x_3)] 
  )

; PROCURANDO NO ENV φ E RETORNANDO O HEAD
(define-metafunction Typed-Peg
  φLook : ϕ τ -> S
  [(φLook ((b_1 S_1) (b_2 S_2) ...) (b_1 S_1)) S_1]
  [(φLook ((b_1 S_1) (b_2 S_2) ...) (b_3 S_3)) (φLook ((τ_2 (b_2 S_2))...) τ_3)] 
  )

(define-metafunction Typed-Peg
  valid-hs : x τ -> boolean
  [(valid-hs x (b S) ) (∉ x S) ]
  )

; VERIFICA SE O X PERTENCE AO HEAD DAQUELE TIPO
(define-metafunction Typed-Peg
  [(∈hs _ ()) #f]
  [(∈hs x (x x_1 ...)) #t]
  [(∈hs x (x_1 x_2 ...)) (∈hs x (x_2 ...))])


(define-metafunction Typed-Peg
  =b? : boolean boolean -> boolean
  [(=b? #t #t) #t]
  [(=b? _ _)   #f]
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
  [(klee α) (★ α)])

(define-metafunction Typed-Peg
  not! : τ -> τ
  [(not! (_ S) ) (#t S)]
  [(not! α) (! α)])

(define-metafunction Typed-Peg
  ⊕ : τ τ -> τ
  [(⊕ (b S) (b_1 S_1)) (,(or (term b) (term b_1)) (union S S_1))]
  [(⊕ τ_1 τ_2) (+ τ_1 τ_2)])

(define-metafunction Typed-Peg
  ⊗ : τ τ -> τ
  [(⊗ (#f S) τ) (#f S)]
  [(⊗ (#t S) (b_1 S_1)) (b_1 (union S S_1)) ]
  [(⊗ τ_1 τ_2) (× τ_1 τ_2)])


(define-metafunction Typed-Peg
  union : S S -> S
  [(union (x_1 ...) (x_2 ...)) ,(set-union (term (x_1 ...)) (term (x_2 ...)))]
  )

(define-metafunction Typed-Peg
  τeval : τ -> τ
  [(τeval (★ τ)) (klee (τeval τ))]
  [(τeval (+ τ_1 τ_2)) (⊕ (τeval τ_1) (τeval τ_2))]
  [(τeval (× τ_1 τ_2)) (⊗ (τeval τ_1) (τeval τ_2))]
  [(τeval (! τ)) (not! (τeval τ))]
  [(τeval (clone (b (x ... x_1 x_2 ...)) x_1)) (b (x ... x_1 x_2 ...))]
  [(τeval (clone (b (x ...)) x_1)) (b (x_1 x ...))]
  [(τeval (clone τ x)) (clone (τeval τ) x)]
  [(τeval τ) τ])


#;(define-metafunction Typed-Peg
    auxEquiv : boolean -> C
    [(auxEquiv #t) true]
    [(auxEquiv #f) false]
    )

#;(define-metafunction Typed-Peg
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


;(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ())))))
;(apply-reduction-relation* constraint-solve (term (() () (tc 1 (#f ())))))
;(apply-reduction-relation* constraint-solve (term (() () (tc A (#f ())))))
;(apply-reduction-relation* constraint-solve (term (() () (tc (/ 2 2) τ))))
;(apply-reduction-relation* constraint-solve (term (() () (tc (* 2) τ))))


;O QUE FAZER COM A GRAMÁTICA
;A METAFUNÇÃO EQUIV É PRA USAR NA LINHA 173 MESMO?
