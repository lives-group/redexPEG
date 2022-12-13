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
  [h (x ...)])

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
      ∅]        ;
  [re Z O F]    ;
  [rsuc Z O])

(define-relation PegRelation
  → ⊆ (GR e) × re
  [(→ (_ ε) Z)]
  [(→ (_ natural) O)]
  [(→ (_ natural) F)]
  [(→ ((r... (x e) r...) x) re) (→ (( r... (x e) r...) e) re) ]
  [(→ (GR (• e_1 e_2)) Z) (→ (GR e_1) Z) (→ (GR e_2) Z)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) Z)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) O) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) O) (→ (GR e_1) Z) (→ (GR e_2) O)]
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) F)]
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) O) (→ (GR e_2) F)]
  [(→ (GR (• e_1 e_2)) F) (→ (GR e_1) Z) (→ (GR e_2) F)]
  [(→ (GR (/ e_1 e_2)) O) (→ (GR e_1) O)]
  [(→ (GR (/ e_1 e_2)) Z) (→ (GR e_1) Z)]
  [(→ (GR (/ e_1 e_2)) re) (→ (GR e_1) F) (→ (GR e_2) re)]
  [(→ (GR (* e)) Z) (→ (GR e) Z)]
  [(→ (GR (* e)) F) (→ (GR e) O)]
  [(→ (GR (! e)) F) (→ (GR e) Z)]
  [(→ (GR (! e)) F) (→ (GR e) O)]
  [(→ (GR (! e)) O) (→ (GR e) F)])

#;(define-metafunction PegRelation
    [(∪ x_1 x_2) ,(append (term x_1) (term x_2))])

#;(define-metafunction PegRelation
    [(R )])


(define-metafunction PegRelation
  head-set : GR e -> (x ...)
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



#;(define-judgment-form PegRealtion
    #:mode ()
    #:contract ()
    )

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