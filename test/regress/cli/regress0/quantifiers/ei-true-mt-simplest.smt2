; COMMAND-LINE: --eager-inst --no-e-matching
; EXPECT: unsat
(set-logic ALL)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int)) (! (=> (and (P x y) (P y z)) (P x z)) :pattern ((P x y) (P y z)))))
(assert (P 0 1))
(assert (P 1 2))
(assert (not (P 0 2)))
(check-sat)
