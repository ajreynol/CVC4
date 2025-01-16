; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (forall ((x Int) (y Int)) (or (< x y) (< x b) (= x 2) (< y 0))))
(check-sat)
