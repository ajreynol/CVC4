; EXPECT: unsat
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(assert (= a ((as const (Array Int Int)) 0)))
(assert (not (= (select a 7) 0)))
(check-sat)
