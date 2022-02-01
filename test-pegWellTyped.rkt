#lang racket
(require redex)
(require rackcheck)
(require "judgments.rkt")
(require "test-pegGEN-CT.rkt")

;; Tests to check if the generated PEG is Well typed





;; 
(define (getLastTerm e)
  (cddr e)
  )