#lang racket

(require redex)
(require "../lang/peg.rkt")
(require "../lang/bigStepSemantics.rkt")

;Tests


;Tests for Terminal

(display "Terminal\n")
(test-equal (judgment-holds (eval ∅ (1 (1 1 1)) s) s) (list (term (1 1))))
(test-equal (judgment-holds (eval ∅ (1 (2 1 1)) s) s) (list (term ⊥)))
(test-equal (judgment-holds (eval ∅ (1 ()) s) s)      (list (term ⊥)))
(test-results)

;Tests for Choice
(display "\nChoice\n")

(test-equal (judgment-holds (eval ∅ ((/ 1 2) (1 1 1)) s) s)      (list (term (1 1))))
(test-equal (judgment-holds (eval ∅ ((/ 1 2) (2 1 1)) s) s)      (list (term (1 1))))
(test-equal (judgment-holds (eval ∅ ((/ 1 2) ()) s) s)           (list (term ⊥)))
(test-equal (judgment-holds (eval ∅ ((/ 1 2) (3 4)) s) s)        (list (term ⊥)))
(test-results)

;Tests for Sequence
(display "\nSequence\n")

(test-equal (judgment-holds (eval ∅ ((• 1 2) (1 2 3)) s) s) (list (term (3))))
(test-equal (judgment-holds (eval ∅ ((• 1 2) (2 2 3)) s) s) (list (term ⊥)))
(test-equal (judgment-holds (eval ∅ ((• 1 2) (1 1 3)) s) s) (list (term ⊥)))
(test-results)

;Tests for Not
(display "\nNot\n")

(test-equal (judgment-holds (eval ∅ ((! 1) (1 2 3)) s) s) (list (term ⊥)))
(test-equal (judgment-holds (eval ∅ ((! 1) (2 2 3)) s) s) (list (term (2 2 3))))
(test-equal (judgment-holds (eval ∅ ((! 1) ()) s) s)  (list empty))
(test-results)

;Tests for Empty
(display "\nEmpty\n")

(test-equal (judgment-holds (eval ∅ (ε (2 2)) s) s) (list (term (2 2))))
(test-equal (judgment-holds (eval ∅ (ε (1 2 3 4 5 6 7)) s) s) (list (term (1 2 3 4 5 6 7))))
(test-results)

;Tests for Repetition
(display "\nRepetition\n")

(test-equal (judgment-holds (eval ∅ ((* 2) (4 5 6 7)) s) s)  (list (term (4 5 6 7))))
(test-equal (judgment-holds (eval ∅ ((* 2) ()) s) s)  (list (term ())))
(test-equal (judgment-holds (eval ∅ ((* 2) (2 2 2 2 3 4)) s) s) (list (term (3 4))))
(test-results)

;Tests for Non-Terminal
(display "\nNon-Terminal\n")

(test-equal (judgment-holds (eval (A 2 ∅) (A (2 3 4 5 6 7)) s) s) (list (term (3 4 5 6 7))))
(test-equal (judgment-holds (eval (B 1 (A 2 ∅)) (A (2 3 4 5 6 7)) s) s) (list (term (3 4 5 6 7))))
(test-equal (judgment-holds (eval (B 1 (A B ∅)) (A (1 2 3 4 5 6 7)) s) s) (list (term (2 3 4 5 6 7))))
;(test-equal (judgment-holds (eval (B 1 (A B ∅)) (C (1 2 3 4 5 6 7)) s) s) (list (term ⊥)))
(test-results)
