(set-info :smt-lib-version 2.6)
(set-logic ALL)

(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () Int)
(assert (and
(not (= (str.replace "A" (str.from_int z) x) (str.++ "A" (str.replace "" (str.from_int z) x))))
(not (= (str.replace x (str.at x z) "") (str.++ (str.replace (str.++ (str.substr x 0 z) (str.substr x z 1)) (str.substr x z 1) "") (str.substr x (+ 1 z) (str.len x)))))
)
)
(check-sat)
