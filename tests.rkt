#lang racket
(require redex)
(require "./peg.rkt")
(require "./judgments.rkt")

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
(test-results)

;Tests for Sequence
(display "\nSequence\n")

(test-equal (judgment-holds (eval ∅ ((• 1 2) (1 2 3)) s) s) (list (term (3))))
(test-equal (judgment-holds (eval ∅ ((• 1 2) (2 2 3)) s) s) (list (term ⊥)))
(test-equal (judgment-holds (eval ∅ ((• 1 2) (1 1 3)) s) s) (list (term ⊥)))
(test-results)

;Tests for Not
(display "\nNot\n")

(test-equal (judgment-holds (eval ∅ ((! 1) (1 2 3)) s) s) (list (term (1 2 3))))
(test-equal (judgment-holds (eval ∅ ((! 1) (2 2 3)) s) s) (list (term ε)))
(test-equal (judgment-holds (eval ∅ ((! 1) ()) s) s)  (list (term ε)))
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
(test-equal (judgment-holds (eval (B 1 (A B ∅)) (C (1 2 3 4 5 6 7)) s) s) (list (term ⊥)))
(test-equal (judgment-holds (lookup (B 1 (A 2 ∅)) C R) R) (list (term ⊥)))
(test-equal (judgment-holds (lookup ∅ C R) R) (list (term ⊥)))
(test-results)

;Tests for ⇀ 
(display "⇀\n")
(test-equal (judgment-holds (⇀ ∅ ε D) D) (list (term 0)))
(test-equal (judgment-holds (⇀ ∅ 1 D) D) (term (1 ⊥)))
(test-equal (judgment-holds (⇀ ∅ (! ε) D) D) (list (term ⊥)))
(test-equal (judgment-holds (⇀ ∅ (* ε) D) D) (list (term 0)))
(test-equal (judgment-holds (⇀ ∅ (/ 1 ε) D) D) (term (0 1)))
(test-equal (judgment-holds (⇀ ∅ (• 1 (* ε)) D) D) (term (1 ⊥)))
(test-results)

;Tests for Well-Formed
(display "\nWell-Formed\n")
;(judgment-holds (eval ∅ ((* ε) (2 2 2 3)) s) s)
;(judgment-holds (eval ∅ ((* (• ε ε)) (4 5 6 7)) boolean) boolean)

(test-equal (judgment-holds (WF ∅ (* ε) boolean) boolean) (list (term #f)))
(test-equal (judgment-holds (WF ∅ (/ 1 ε) boolean) boolean) (list (term #t)))
(test-equal (judgment-holds (WF ∅ (* (/ 1 ε)) boolean) boolean) (list (term #f)))
(test-equal (judgment-holds (WF ∅ (• 1 (* ε)) boolean) boolean) (list (term #t)))
(test-equal (judgment-holds (WF ∅ (* 1) boolean) boolean) (list (term #t)))
(test-equal (judgment-holds (WF ∅ 1 boolean) boolean) (list (term #t)))
;(judgment-holds (WF (A (• A 1) ∅) A boolean) boolean) loop
(test-equal (judgment-holds (WF (A (• 1 A) ∅) A boolean) boolean) (list (term #t)))
;(judgment-holds (WF (A (• ε A) ∅) A boolean) boolean) loop
(test-results)


;DUVIDAS:
;fazer a regra da !⇀ para tirar o problema do (* (/ 1 ε)) 
;fazer uma funçao que verifica se o resultado do judgment da ⇀ eh um 0
;⇥
;↛