; EXPECT: unsat
(set-logic AUFLIA)
(declare-fun a () (Array Int Int))
(assert (= a (store ((as const (Array Int Int)) 0) 1 2)))
(assert (not (= (select a 0) 0)))
(check-sat)
