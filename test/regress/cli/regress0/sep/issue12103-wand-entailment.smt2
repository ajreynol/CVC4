; EXPECT: unknown
(set-logic QF_ALL)
(declare-heap (Int Int))
(set-info :status unsat)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(declare-const a Int)

(assert (sep (pto x a) (wand (pto x w) (sep (pto y z) true))))
(assert
  (not
    (and
      (sep (pto x a) true)
      (or
        (and (= x y) (= z w))
        (and (not (= x y)) (sep (pto y z) true))))))

(check-sat)
