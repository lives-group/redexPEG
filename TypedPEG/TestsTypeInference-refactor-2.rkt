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

(require "./TypeInferencePEG-refactor-2.rkt")
(require "./TestsTypedPeg.rkt")

(define (get-G l)
  (import-gen-grm (car l)))

(define (get-expression l)
  (cadr l))

(define (get-type l)
  (caddr l))

(define (get-type-of-typed-peg peg)
  (solution2context (infer (peg2struct peg)))
  )

(define (import-gen-grm l)
  (match l
    ['∅  null]
    [(list v e g) (cond
                    [(symbol? v) (cons (cons v (list e)) (import-gen-grm g))]
                    [else (error "Error while converting from random generated peg") ])]
    )
  )


(define (teste l)
  (inferType (get-G l) (get-expression l))
  )


(define (constraint-from-peggen peggen)
  (genConstraint (get-G peggen) (get-expression peggen))
  )

(define (traces-gen peggen)
  (traces constraint-solve (constraint-from-peggen peggen))
  )


(define (findTrue l)
  (cond [(eq? l '()) #f]
        [else (or (last (car l)) (findTrue (cdr l)))]
        )
  )

(define (compare2lists list1 list2)
  (match list1 
    ['() #t]
    [(cons (list nt b hs) xs) (let ([result-assoc (assoc nt list2)])
                                (cond [(and result-assoc
                                            (equal? (caadr result-assoc) b)
                                            (equal? (list->set (cadr (cadr result-assoc))) (list->set hs)))
                                       (compare2lists xs list2)]
                                      [else #f]))]
    )
  )

;LISTA DO RODRIGO TEM QUE SER PRIMEIRO
(define (compare-types list1 list2)
  (and (equal? (length list1) (length list2)) (compare2lists list1 list2))
  )

(define (test255 list1 list2)
  (map (lambda (x) 
         (map (lambda (y) 
                (and (equal? (car x) (car y))
                     (and (equal? (car (cadr y)) (car (rest x)))
                          (equal? (list->set (cadr (cadr y))) (list->set (cadr (rest x)))))))
              list1))
       list2))

(define (findTrueinList l)
  (andmap (lambda (x) (findTruePure x))
          l))


(define (findTruePure term)
  (cond [(empty? term) #f]
        [(car term) #t]
        [else (findTruePure (cdr term))]))

(define-property type-checks([peg  (gen:peg 3 5 2)])
  ;(println peg)
  (compare-types  
   
   (get-type-of-typed-peg peg)
   (car (car (teste peg)))
   )
  )


;verifica se o tamanho das listas são iguais, se não forem, já retorna falso
;se for, ele compara as listas 
(define (check-types type_1 type_2)
  (cond [(not (equal? (length type_1) (length type_2))) #f]
        [(equal? (length type_1) 1) (equal? (rest (car type_1))
                                            (cadr (car type_2)))]
        [else (equal? (list->set type_1) (list->set type_2))]
        )
  )

(define (new-test peg)
  (define type-of-rodrigo (get-type-of-typed-peg peg))
  (define our-type (car (car (teste peg))))
  (println our-type)
  (println type-of-rodrigo)
  (compare-types
   type-of-rodrigo
   our-type
   ))

(define-property simple-check ([peg  (gen:peg 3 2 2)])
  ;(println peg)
  (findTrue (teste peg))
  
  )

(check-property (make-config #:tests 5
                             #:deadline (+ (current-inexact-milliseconds) (* 60 3000)))
                type-checks)
#;(check-property (make-config #:tests 1
                               #:deadline (+ (current-inexact-milliseconds) (* 60 3000))
                               ) simple-check
                                 )

;(teste (last (sample (gen:peg 2 2 3) 1)))

;((C ε (B C (A 1 ∅))) A ((A #f ()) (B #t (C)) (C #t ())))
#;(apply-reduction-relation*
   constraint-solve
   (term (((A (v 3)) (B (v 2)) (C (v 1)))
          ()
          (∧
           (∧
            (∧
             ((v 1) ≡ (#t ()))
             (∧
              (C ≡ (v 3))
              ((v 2) ≡ (clone (v 3) C))))
            ((v 3) ≡ (#f ())))
           (∧
            (A ≡ (v 1))
            ((v 0) ≡ (clone (v 1) A)))))))


#;(apply-reduction-relation* constraint-solve (term (((C (v 1)) (E (v 2)) (S (v 5)))
                                                     ()
                                                     (∧
                                                      (∧
                                                       (∧
                                                        (∧
                                                         (∧
                                                          ((v 3) ≡ (#t ()))
                                                          ((v 4) ≡ (#t ())))
                                                         ((v 1) ≡ (× (v 3) (v 4))))
                                                        (∧
                                                         (∧
                                                          ((v 3) ≡ (#f ()))
                                                          ((v 4) ≡ (#f ())))
                                                         ((v 2) ≡ (+ (v 3) (v 4)))))
                                                       (∧
                                                        (∧
                                                         (∧
                                                          (E ≡ (v 8))
                                                          ((v 6) ≡ (clone (v 8) E)))
                                                         ((v 7) ≡ (#t ())))
                                                        ((v 5) ≡ (× (v 6) (v 7)))))
                                                      (∧
                                                       (∧
                                                        (∧
                                                         (C ≡ (v 11))
                                                         ((v 9) ≡ (clone (v 11) C)))
                                                        (∧
                                                         (E ≡ (v 12))
                                                         ((v 10)
                                                          ≡
                                                          (clone (v 12) E))))
                                                       ((v 0) ≡ (× (v 9) (v 10))))))))


;peg = ((Q (• A J) (A (• ε 0) (J (• ε ε) ∅)))
;       (/ A 0)
;       ((J #t ()) (A #f ()) (Q #f (A))))

;peg = ((N (* (/ 0 2)) (A (/ (/ 2 0) (• N 2)) ∅)) (/ (• 1 ε) (• 2 ε)) ((A #f (N)) (N #t ())))
;peg = ((N (* (/ 0 2)) ∅) (• 1 ε) ( (N #t ())))


(define a '((J (#t ())) (K (#t (X J))) (X (#f ()))))
(define b '((J #t ()) (X #f ()) (K #t (J Y))))


;(findTrueinList (test255 a b))