#lang racket

;This Module contains an implmemtation of a type system for PEG 

(require redex)
(require "../lang/peg.rkt")

(provide (all-defined-out))

; Syntax for TypedPeg
;; Γ -> list of variables of type τ
;; G -> Peg Grammar 
;; τ -> (b, H)
;; b -> T or F
;; H -> set of vars (called Headset)
(define-extended-language TypedPeg Peg 
  [Γ ((x τ ) ...)]
  [τ (b H)]
  [b #t #f]
  [H (x ...)]
  )

; Helpers for TypedPeg
; ∨ (logical or - self explanatory)
(define-metafunction TypedPeg
  [(∨ #t #f) #t]
  [(∨ #f #t) #t]
  [(∨ #t #t) #t]
  [(∨ #f #f) #f]
  )

;Helpers functions for TypedPeg

; Union operation. 
; Format: ∪ h1 h2
;   where  h1 : headset
;          h2 : headset
;  result : a set union of h1 and h2
;
(define-metafunction TypedPeg
  [(∪ H_1 H_2 ) ,(set-union (term H_1) (term H_2))]
  )

; Lookup metafunction for context Γ
; Format: ΓLook Γ x
;   where Γ : is the context to be searched
;         x : is a varibale name.
;   reuslt : The type associated with the variable 
(define-metafunction TypedPeg
  [(ΓLook ((x_1 τ_1) (x_2 τ_2) ...) x_1) τ_1]
  [(ΓLook ((x_1 τ_1) (x_2 τ_2) ...) x_3) (ΓLook ((x_2 τ_2) ...) x_3)] 
  )


;
(define-metafunction TypedPeg
  [(ins (b H) x) (b ,(set-union (list (term x)) (term H)))]
  )

; Judgment to find the type of a peg
; Return (b H) -> (nullable or not (list of vars))
(define-judgment-form TypedPeg
  #:mode (⊢ I I O)  
  #:contract (⊢ Γ e τ)

  [----------------------------"empty"
   (⊢ Γ ε (#t ()))]

  [----------------------------"terminal"
   (⊢ Γ number (#f ()))]

  [----------------------------"var"
   (⊢ Γ x (ins (ΓLook Γ x) x))]

  [(⊢ Γ e (b H))
   ----------------------------"rep"
   (⊢ Γ (* e) (#t H))]

  [(⊢ Γ e (b H))
   ----------------------------"not"
   (⊢ Γ (! e) (#t H))]

  [(⊢ Γ  e_1 (#t H_1))
   (⊢ Γ  e_2 (b H_2))
   ----------------------------"seq_1"
   (⊢ Γ (• e_1 e_2) (b (∪ H_1 H_2)))]

  [(⊢ Γ  e_1 (#f H_1))
   (⊢ Γ e_2 (b H_2))
   ----------------------------"seq_2"
   (⊢ Γ (• e_1 e_2) (#f H_1))]

  [(⊢ Γ  e_1 (b_1 H_1))
   (⊢ Γ e_2 (b_2 H_2))
   ----------------------------"alt"
   (⊢ Γ (/ e_1 e_2) ((∨ b_1 b_2) (∪ H_1 H_2)))]
  )
