; COMMAND-LINE: --enum-inst
; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Real) Bool)
(assert (forall ((x Int) (y Real)) (=> (= y (+ (to_real x) 1.5)) (P y))))
(assert (not (P 1.5)))
(check-sat)
