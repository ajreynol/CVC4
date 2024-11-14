; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(assert (str.contains (str.substr x 0 (str.indexof x "y" 0)) "y"))
(check-sat)
