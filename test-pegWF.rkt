#lang racket
(require redex)
(require rackcheck)
(require "WFverf.rkt")
(require "test-pegGEN-CT.rkt")

;; Testing if the generated PEG is Well-Formed

(define (testPEG e)
  (if (is-WF (getGrammar e) (getExpression e) '())
      (println #t)
      (begin
        (println e)
        (exit 0))) ;; If isn't Well-Formed then we print the expression and stop
  )

;; Helper function to get Grammar and the Expression from randPEG

(define (getGrammar e)
  (car e)
  )

(define (getExpression e)
  (car (cdr e))
  )


;; Test generation 

(define (testLoop n)
  (if (> n 0) 
      (begin
        (testPEG (randPEG (genSymbols 3) (sample (gen:one-of '(0 1 2 3))) 2))
        (testLoop (- n 1)))
      (display "Fim")
      )
  )

;(testLoop 10)
;(testLoop 100)