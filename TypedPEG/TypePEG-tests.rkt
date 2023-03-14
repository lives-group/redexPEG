#lang racket

(require redex)
(require rackcheck)
(require "../Redex-PEG/peg/lang/bigStepSemantics.rkt")
(require "./TypePEG-reduction.rkt")

;; Tests do compare the results of the reduction and judgment type check.

(define (compareReductionJudgment Γ G exp)
  (equal? (last (last (apply-reduction-relation* typing (term (,Γ ,G ,exp)))))
          (last (judgment-holds (type ,Γ ,G ,exp t) t))))


;; Tests
(compareReductionJudgment '() '() 1)
(compareReductionJudgment '() '() '(• 1 2))
(compareReductionJudgment '() '() '(/ 1 2))
(compareReductionJudgment '() '() '(! 1))
(compareReductionJudgment '() '() '(* 1))
(compareReductionJudgment '() '() '(• 1 (• 2 3)))
(compareReductionJudgment '() '() '(• 1 (/ 2 (/ 3 4))))
(compareReductionJudgment '() '() '(! (• 1 (/ 2 (/ 3 4)))))
(compareReductionJudgment '((A (#f ()))) '((A 1)) 'A)
(compareReductionJudgment '((A (#t ())) 
                            (B (#t ()))
                            (S (#f (A B))))
                          '((S (• A (• B 2)))
                            (A (/ (• 0 A) ε)) 
                            (B (/ (• 1 B) ε)))
                          'S)