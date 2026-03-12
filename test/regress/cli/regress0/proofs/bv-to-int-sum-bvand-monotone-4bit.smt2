; COMMAND-LINE: --produce-proofs --proof-check=eager --solve-bv-as-int=sum
; EXPECT: unsat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (not (bvuge x (bvand x y))))
(check-sat)
