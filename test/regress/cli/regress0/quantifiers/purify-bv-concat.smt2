; EXPECT: unsat
(set-logic ALL)
(declare-fun P ((_ BitVec 4)) Bool)
(assert (forall ((x (_ BitVec 3))) (P (concat #b0 x))))
(declare-fun b () (_ BitVec 4))
(assert (not (P b)))
(assert (= ((_ extract 3 3) b) #b0))
(check-sat)
