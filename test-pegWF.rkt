#lang racket
(require redex)
(require rackcheck)
(require "judgments.rkt")
(require "WFverf.rkt")
(require "test-pegGEN-CT.rkt")

;; Testing if the generated PEG is Well-Formed

(define (testPEG e)
  (is-WF (getGrammar e) (getExpression e) '())
  )

;; Helper function to get Grammar and the Expression from randPEG

(define (getGrammar e)
  (car e)
  )

(define (getExpression e)
  (car (cdr e))
  )


;; Test generaton 

(define (testLoop n)
  (if (> n 0) 
      ( (println (testPEG (randPEG (genSymbols 3) (sample (gen:one-of '(0 1 2 3))) 2)))
        (testLoop (- n 1)))
      (display "Fim")
      )
  )