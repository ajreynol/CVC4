; EXPECT: unsat
(set-logic ALL)
(assert (exists ((v Real)) (and (<= 0 v) (exists ((v Real)) (forall ((y Real)) (> 0 v))))))
(check-sat)
