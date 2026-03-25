; COMMAND-LINE: --incremental
; EXPECT: unsat
; EXPECT: unsat
(set-logic ALL)
(push)
(declare-fun x () Int)
(assert (> x 1))
(assert (< x 0))
(check-sat)
(pop)
(push)
(declare-fun x () String)
(assert (< (str.len x) 0))
(check-sat)
(pop)
