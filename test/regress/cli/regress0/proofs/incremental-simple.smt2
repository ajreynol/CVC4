; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () Int)
(push)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(pop)
(push)
(assert (> x 2))
(assert (< x 0))
(check-sat)
(pop)
(push)
(assert (> x 3))
(assert (< x 0))
(check-sat)
(pop)
