; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=sum
; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=bv
; COMMAND-LINE: --cegqi-all --full-saturate-quant --solve-bv-as-int=iand
; EXPECT: unsat
(set-logic UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(assert (forall ((x (_ BitVec 4))) (bvugt (f x) (_ bv15 4))))
(check-sat)
(exit)
