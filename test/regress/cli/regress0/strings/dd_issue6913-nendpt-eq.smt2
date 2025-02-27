; EXPECT: unsat
(set-logic ALL)
(declare-fun a () String)
(assert (= (str.++ "0" (str.from_code 0) (str.replace "" a "A")) (str.++ a "A" (str.at (str.++ a a a) 1))))
(check-sat)
