#lang racket
(require redex)
(require rackcheck)
(require "judgments.rkt")
(require "WFverf.rkt")
(require "test-pegGEN-CT.rkt")

;; Testing if the generated PEG is Well-Formed

(define (testPEG e)
  (if (is-WF (getGrammar e) (getExpression e) '())
      (println #t)
      (println e)) ;; If isn't Well-Formed then we print the expression
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
      ((testPEG (randPEG (genSymbols 3) (sample (gen:one-of '(0 1 2 3))) 2))
        (testLoop (- n 1)))
      (display "Fim")
      )
  )

;(testLoop 10)
;(testLoop 100) -> da erro de memoria