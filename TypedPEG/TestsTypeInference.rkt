#lang racket

(require typed-peg/core
         typed-peg/typing/infer
         typed-peg/typing/type
         typed-peg/typing/constraint
         typed-peg/tree
         peg-gen
         rackcheck
         rackunit
         redex)

(require "./TypeInferencePEG.rkt")







(sample (gen:peg 2 2 3) 1)


(define (get-G l)
  (car (car l)))
(define (get-expression l)
  (second (car l)))
(define (get-type l)
  (third (car l)))





(define (teste l)
  (println "Expressão: ")
  (println (car l))
  (apply-reduction-relation* constraint-solve (term (() ,(get-G l) (tc ,(get-expression l) ,(get-type l))))))


(teste (sample (gen:peg 2 2 3) 1))

;(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ())))))









#|
(define (peg2struct peg)
    (let ([ug (car peg)]
          [exp (cadr peg)])
    (peg-grammar (convg ug) (conve exp)) )
  )

(define (convg g)
     (if (eq? '∅ g)
         null
         (cons (cons (symbol->string (car g)) (conve (cadr g))) (convg (caddr g))))
  )

(define (conve peg)
   (match peg
         [(list '• e d)  (pcat (conve e) (conve d))]
         [(list '/ e d)  (pchoice  (conve e) (conve d) )]
         [(list '* e) (pstar  (conve e)) ]
         [(list '! e) (pneg (conve e)) ]
         ['ε (peps ) ]
         [(? natural? n)  (pchr (integer->char (+ 48 n)) )]
         [_ (pvar (symbol->string peg)) ]
         )
  )

(define straw '((J (• (* 1) (/ ε 0)) (X (• (/ 1 1) (/ 0 J)) (K (/ (• 0 ε) (/ X J)) ∅)))
                (/ (• 1 J) (/ 1 1))
                ((K #t (X J)) (X #f ()) (J #t ()))) )

(define (testgen p)
    (not (eq? (cdr (infer (peg2struct p))) 'unsat))
  )

(define (solution2context s)
   (let ([varMap (car s)]
         [tempMap (cdr s)])
         (map (lambda (x)  (cons (string->symbol (car x)) (la (cdr x) tempMap)) ) varMap )
     ) 
  )

(define (tyvar2String tyv)
      (string-append "t" (number->string (term-tyvar-tyvar tyv)) )
  )

(define (la k z)
      (let ([ty (cdr (assoc (tyvar2String k) z))] )
           (list (type-null? ty) (map string->symbol (type-head-set ty))))
 )


(define (consT e xs)
     (if xs (cons e xs) #f))

(define (myrm e xs)
  (cond
    [(null? xs) #f]
    [(eqv? (car xs) e) (cdr xs)]
    [else (consT (car xs) (myrm e (cdr xs)))]))

(define (listeq xs ys)
      (cond
         [(not ys) #f]
         [(and (null? xs) (null? ys))              #t]
         [(and (not (null? xs)) (not (null? ys)))  (listeq (cdr xs) (myrm (car xs) ys)) ]
         [else #f])
  )

(define (matchTypes ty tyy)
   (and ty
        tyy
        (eqv? (car ty) (car tyy))
        (eqv? (cadr ty) (cadr tyy))
        (listeq (last ty) (last tyy)) ))

(define (allTypesMatch g g1 )
   (andmap (lambda (t) (matchTypes t (assoc (car t) g) )) g1)
  )

(define-property type-checks([peg  (gen:peg 3 5 2)])
    (check-equal?  (testgen peg) #t)
  )

(define-property type-contexts-match([peg  (gen:peg 3 5 2)])
    (check-equal?  (allTypesMatch (solution2context (infer (peg2struct peg))) (last peg)) #t)
  )

(check-property type-checks)
(check-property type-contexts-match)emicida 


(term (tc ε (#t ∅)))
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


(term (gc ∅ (#t ∅)))
(term (gc () (#t ∅)))
(term (gc ((A 1)) (#t ∅)))




(apply-reduction-relation* constraint-solve (term (() () (tc ε (#t ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc 1 (#f ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc A (#f ∅)))))
(apply-reduction-relation* constraint-solve (term (() () (tc (/ 2 2) τ))))
(apply-reduction-relation* constraint-solve (term (() () (tc (* 2) τ))))



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
|#


