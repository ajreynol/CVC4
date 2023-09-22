; COMMAND-LINE: --pool-inst-trust
; EXPECT: sat
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-pool P Int (0))
(assert (forall ((x Int)) (! (> (f x) (+ x 1)) :pool (P))))
(check-sat)
