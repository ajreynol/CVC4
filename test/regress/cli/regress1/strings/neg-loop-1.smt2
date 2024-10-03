; EXPECT: sat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (not (str.in_re x ((_ re.loop 0 6) (re.union (str.to_re "AB") (str.to_re "A"))))))
(assert (< (str.len x) 6))
(assert (not (str.contains x "B")))
(check-sat)
