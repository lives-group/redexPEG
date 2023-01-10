#lang racket

; This module contains the implementation of a big step semmantics for PEG in Redex. 


(require redex)
(require "./peg.rkt")

(provide (all-defined-out))

; Syntax for a big-step PEG evaluation
(define-extended-language BigStep Grammar
  [E (e s)]         ;  An evaluation is comprised of a PEG and a input 
  [s (natural ...)  ;  An input can be: * A squence of terminal symbols
     ⊥              ;                   * Bottom, meaning an parser error 
     ε]             ;                   * Empty string (there is nothing to be consumed !)
  [r (x e)]     ;
  [GR (r ...)
      ∅]        ;
  [re Z O F]    ;
  [rsuc Z O]    ;  
  [h (x ...)]
  )

; Judgment for a big-step  peg evaluation 
(define-judgment-form BigStep
  #:mode (eval I I O)
  #:contract (eval G E s)
  
  ;Terminal
  [-------------------------------- 
   (eval G (natural_1 (natural_1 natural ...)) (natural ...))]
  
  [(side-condition (dismatch? natural_1 natural_2))
   --------------------------------
   (eval G (natural_1 (natural_2 natural ...)) ⊥)]
  
  [--------------------------------
   (eval G (natural_1 ()) ⊥)]
  
  ; choice 
  [(eval G (e_1 s) (natural ...))
   --------------------------------
   (eval G ((/ e_1 e_2) s) (natural ...))]

  [(eval G (e_1 s) ⊥)
   (eval G (e_2 s) s_1)
   -------------------------------
   (eval G ((/ e_1 e_2) s) s_1)]

 
  ;Sequence
  [(eval G (e_1 s) (natural ...))
   (eval G (e_2 (natural ...)) s_2)
   -------------------------------
   (eval G ((• e_1 e_2) s) s_2)]

  [(eval G (e_1 s) ⊥)
   -------------------------------
   (eval G ((• e_1 e_2) s) ⊥)]

  ;Not
  [(eval G (e s) (natural ...) )
   -------------------------------
   (eval G ((! e) s) ⊥)]  

  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((! e) s) s)]

  ;Repetition
  [(eval G (e s) ⊥)
   -------------------------------
   (eval G ((* e) s) s)]

  [(eval G (e s) (natural ...))
   (eval G ((* e) (natural ...)) s_2)
   -------------------------------
   (eval G ((* e) s) s_2)]

  ;Empty
  [-------------------------------
   (eval G (ε s) s)]

  ;Non-Terminal
  [(eval G ((lookupG G x) s) s_1)
   --------------------------------
   (eval G (x s) s_1)]
  )

; Checks if natural_1 and natural_2 are different
(define-metafunction BigStep
  [(dismatch? natural_1 natural_1) #f]
  [(dismatch? natural_1 natural_2) #t]) 


;; Render a pdf of a formalization
; (render-judgment-form eval "../judgment-latex/judgment-form-eval.pdf")

#;(define-relation BigStep
    ; Relation-contract
    WF ⊆ e
  
    [(WF ε)] 
    [(WF number)]
    [(WF (/ e_1 e_2)) (WF e_1) (WF e_2)]
    [(WF (! e)) (WF e)]
    [(WF (* e)) (WF e)] ; pensar nessa aqui
    [(WF (• e_1 e)) (WF e_1)]
    ;nao terminal
    )

(define-language PegRelation
  (e natural    ; Terminal
     (/ e e)     ; Choice
     (• e e)     ; Sequence
     (* e)       ; Repetition
     (! e)       ; Not complement
     ε           ; Empty
     x)          ; Non-Temrinal 
  (x variable-not-otherwise-mentioned)
  [r (x e)]     ;
  [GR (r ...)
      ∅]
  [Γ ((x t) ...)];
  [re Z O F]    ;
  [rsuc Z O]
  [hs (x ...)]
  [t (boolean hs)])

(define-relation PegRelation
  → ⊆ (GR e) × re
  [(→ (_ ε) Z)]
  [(→ (_ natural) F)]
  [(→ (_ natural) O)]
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) F)]
  [(→ (GR (/ e_1 e_2)) O) (→ (GR e_1) O)]
  [(→ (GR (/ e_1 e_2)) Z) (→ (GR e_1) Z)]
  [(→ (GR (* e)) Z) (→ (GR e) Z)]
  [(→ (GR (* e)) F) (→ (GR e) O)]
  [(→ (GR (! e)) F) (→ (GR e) Z)]
  [(→ (GR (! e)) F) (→ (GR e) O)]
  [(→ (GR (! e)) O) (→ (GR e) F)]
  [(→ ((r_1... (x e) r_2...) x) Z) (→ (( r_1... (x e) r_2...) e) Z)]
  [(→ ((r_1... (x e) r_2...) x) O) (→ (( r_1... (x e) r_2...) e) O)]
  [(→ ((r_1... (x e) r_2...) x) F) (→ (( r_1... (x e) r_2...) e) F)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) Z)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) Z) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) Z) (→ (GR e_1) Z) (→ (GR e_2) Z)]
  
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) O) (→ (GR e_2) F)]
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) Z) (→ (GR e_2) F)]
  
  
  [(→ (GR (/ e_1 e_2)) Z) (→ (GR e_1) F) (→ (GR e_2) Z)]
  [(→ (GR (/ e_1 e_2)) O) (→ (GR e_1) F) (→ (GR e_2) O)]
  [(→ (GR (/ e_1 e_2)) F) (→ (GR e_1) F) (→ (GR e_2) F)]
  )

(define-relation PegRelation
  null ⊆ (GR e)
  [(null (_ ε))]
  [(null (GR (/ e_1 e_2))) (null (GR e_1))]
  [(null (GR (/ e_1 e_2))) (null (GR e_2))]
  [(null (GR (* e)))]
  [(null ((r_1... (x e) r_2...) x)) (null (( r_1... (x e) r_2...) e))]
  [(null (GR (• e_1 e_2))) (null (GR e_1)) (null (GR e_2))]
  )

(define-metafunction PegRelation
  [(∪ () ()) ()]
  [(∪ (x_1...) ()) (x_1...)]
  [(∪ () (x_2...)) (x_2...)]
  [(∪ (x_1...) (x_2...)) ,(append `(x_1...) `(x_2...))])

(define-metafunction PegRelation
  lookUp : x hs -> boolean 
  [(lookUp x_1 (x... x_1 x_2...)) #f]
  [(lookUp x hs) (member x hs)])

;DISJUNÇÃO
(define-metafunction PegRelation
  ⊕ : t t -> t
  [(⊕ (boolean_1 hs_1) (boolean_2 hs_2))
   (,(or (term boolean_1) (term boolean_2))
    (∪ hs_1 hs_2))])

;CONJUNÇÃO
(define-metafunction PegRelation
  ⊗ : t t -> t
  [(⊗ (boolean_1 hs_1) (boolean_2 hs_2))
   (,(and (term boolean_1) (term boolean_2))
    (∪ hs_1 (⇒ boolean_1 hs_2)))])

(define-metafunction PegRelation
  ⇒ : boolean hs -> hs
  [(⇒ #t hs) hs]
  [(⇒ #f hs) ()])

(define-metafunction PegRelation
  head-set : GR e -> hs
  [(head-set _ ε) ()]
  [(head-set _ natural) ()]
  [(head-set ((x e)... (x_1 e_1) (x_2 e_2)...) x_1)  ,(cons (term x_1)
                                                            (term (head-set ((x e)... (x_1 e_1) (x_2 e_2)...)
                                                                            e_1)))]

  [(head-set GR (• e_1 e_2)) ,(append (term (head-set GR e_1))
                                      (term (head-set GR e_2)))
                             ; if :
                             (side-condition (term (→ (GR e_1) Z)))]
  
  [(head-set GR (• e_1 e_2)) (head-set GR e_1)]
  [(head-set GR (/ e_1 e_2)) ,(append (term (head-set GR e_1)) 
                                      (term (head-set GR e_2)))]
  [(head-set GR (* e)) (head-set GR e)]
  [(head-set GR (! e)) (head-set GR e)])



(define-judgment-form PegRelation
  #:mode (type I I I O)
  #:contract (type Γ GR e t)
  
  [-------------------------------- 
   (type Γ GR ε (#t (head-set GR ε)))]

  [-------------------------------- 
   (type Γ GR natural (#f (head-set GR natural)))]

  [(→ (GR e_1) O)
   (type Γ GR e_1 (boolean_1 _))
   (type Γ GR e_2 (boolean_2 _))
   -------------------------------- 
   (type Γ GR (• e_1 e_2) (⊗ (boolean_1 (head-set GR e_1)) (boolean_2 (head-set GR e_2))))]

  [(→ (GR e_1) F)
   -------------------------------- 
   (type Γ GR (• e_1 e_2) (#f (head-set GR e_1)))]

  [(→ (GR e_1) Z)
   (type Γ GR e_1 (boolean_1 _))
   -------------------------------- 
   (type Γ GR (• e_1 e_2) (#f (head-set GR e_1)))]

  [(type Γ GR e_1 (boolean_1 _))
   (type Γ GR e_2 (boolean_2 _))
   -------------------------------- 
   (type Γ GR (/ e_1 e_2) (⊕ (boolean_1 (head-set GR e_1)) (boolean_2 (head-set GR e_2))))]

  [
   -------------------------------- 
   (type Γ GR (! e) (#t (head-set GR e)))]

  [(type Γ GR e (#f _))
   -------------------------------- 
   (type Γ GR (* e) (#t (head-set GR e)))]

  [;fazer o lookup
   ;verificar se o x ta no hs (n pode t'a)
   ;(lookUp x (head-set GR x))
   -------------------------------- 
   (type Γ GR x (#t (head-set GR x)))]
  )

(judgment-holds (type () () 1 t) t) 
(judgment-holds (type () () ε t) t)
(judgment-holds (type () () (• 1 3) t) t)
(judgment-holds (type () () (• ε 3) t) t)
(judgment-holds (type () () (! 1) t) t)
(judgment-holds (type () () (* 1) t) t)
(judgment-holds (type () () (/ ε 3) t) t)
(judgment-holds (type () ((A 2)) (/ A 3) t) t)
(judgment-holds (type () ((A 2)) A t) t)
;(judgment-holds (type () ((A (/ A 2))) A t) t)
#;(judgment-holds (type ((A (#t ())) 
                         (B (#t ()))
                         (S (#f (A B)))) 
                        ((S (• A (• B 2)))
                         (A (/ (• 0 A) ε)) 
                         (B (/ (• 1 B) ε))) S t)t)

#;(term (→ (((S (• A (• B 2)))
             (A (/ (• 0 A) ε)) 
             (B (/ (• 1 B) ε))) A) Z))
(term (null (((S (• A (• B 2)))
             (A (/ (• 0 A) ε)) 
             (B (/ (• 1 B) ε))) (• 0 A))))
(term (null (((S (• A (• B 2)))
             (A (/ (• 0 A) ε)) 
             (B (/ (• 1 B) ε))) (/ (• 0 A) ε))))

;(judgment-holds (type () ((B 2)) A t) t)

; Fazer o type system figura 3  


#| ; Tests

(judgment-holds (→ (∅ ε) O))
(judgment-holds (→ (∅ 1) O))
(judgment-holds (→ (∅ (• 1 3)) Z))
(judgment-holds (→ (∅ (/ 1 3)) Z))
(judgment-holds (→ (∅ (• 1 ε)) Z))
(judgment-holds (→ (∅ (* 1)) Z))
(judgment-holds (→ (∅ (! 1)) F))

|#

; headset -> metafunction (retorna um conjunto de variáveis)
; headset associado a um tipo: conjunto de variáveis que está imetediatamente a esquerda)
; judgment do sistema de tipos (3: https://dl.acm.org/doi/pdf/10.1145/3355378.3355388)