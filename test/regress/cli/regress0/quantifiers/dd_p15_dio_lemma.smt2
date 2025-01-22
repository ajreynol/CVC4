(declare-fun ~ () Int)
(assert (forall ((v Int)) (or (= ~ (div v 2)) (= 0 (mod (div v 2) 2)))))
(check-sat)
