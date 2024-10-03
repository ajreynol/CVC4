; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (not (str.in_re x ((_ re.loop 1 6) (re.union (str.to_re "AB") (str.to_re "A"))))))
(assert (or (= x (str.++ "AB" y)) (= x (str.++ "A" y))))
(assert (str.in_re y ((_ re.loop 1 4) (re.union (str.to_re "AB") (str.to_re "A")))))
(check-sat)
