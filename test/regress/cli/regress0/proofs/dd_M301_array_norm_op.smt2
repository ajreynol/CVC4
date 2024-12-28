; EXPECT: unsat
(set-logic AUFDTLIRA)
(declare-sort n 0)
(declare-fun n (n) Int)
(define-fun t ((x n)) Int (n x))
(declare-const r n)
(assert (exists ((x (Array Int n)) (x1 (Array Int n))) (not (=> (= x (store x1 1 r)) (= x (store (store (store (store (store (store x 2 r) 0 r) 5 r) 3 r) 4 r) 9 r)) (= x (store x 0 r))))))
(check-sat)
