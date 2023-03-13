#lang racket

(require redex)
(require "../Redex-PEG/peg/lang/bigStepSemantics.rkt")
(require "./TypePEG-reduction.rkt")

;; Tests do compare the results of the reduction and judgment type check.

;(apply-reduction-relation* typing (term (((A (#f (A)))) ((A 1)) A)))
;(judgment-holds (type ((A (#f (A)))) ((A 1)) A t) t)


(define (compareReductionJudgment Γ G exp)
   (equal? (last (judgment-holds (type ,Γ ,G ,exp t) t)) 
                (last (last (apply-reduction-relation* typing (term (,Γ ,G ,exp)))))))



;; Tests
(compareReductionJudgment '() '() 1)
(compareReductionJudgment '() '() '(• 1 2))
(compareReductionJudgment '() '() '(/ 1 2))
(compareReductionJudgment '() '() '(! 1))
(compareReductionJudgment '() '() '(* 1))
(compareReductionJudgment '() '() '(• 1 (• 2 3)))
(compareReductionJudgment '() '() '(• 1 (/ 2 (/ 3 4))))
(compareReductionJudgment '((A (#f (A)))) '((A 1)) 'A) ;; Esse da errado