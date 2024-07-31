; EXPECT: unsat
(set-logic HO_ALL)
(set-option :finite-model-find true)
(declare-const R (Set (Tuple Int)))
(declare-const M (Set (Tuple Int Bool Int Bool Int)))
(assert (distinct (as set.empty (Set (Tuple Int))) R))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_17 (Tuple Int))) (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_18 (Tuple Int Bool Int Bool Int))) false) M))) R)))
(check-sat)
