#lang racket
(require redex)
(require rackcheck)
(require "judgments.rkt")
(require "test-pegGEN-CT.rkt")

;; Tests to check if the generated PEG is Well typed

(define (geraTestes)
  (let* ([nV (sample (gen:integer-in 0 10) 1)]
         [vars (genSymbols (car nV)) ]
         [nT (sample (gen:integer-in 0 26) 1)]
         [Σ (mkList (car nT)) ]
         [p (sample (gen:integer-in 0 7) 1)])
    (for ([x 100])
      (verfHeadSet (randPEG vars Σ (car p)))
      (print "a")
      )
    )
  )


;; 
(define (getLastTerm e)
  (cddr e)
  )