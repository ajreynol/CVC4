; EXPECT: unsat
(set-logic ALL)

(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun P (U) Bool)
(declare-const a U)

(assert
 (forall ((x U))
   (! (P (f (g x)))
      :pattern ((f (g x))))))

(assert (not (P (f (g a)))))
(check-sat)
