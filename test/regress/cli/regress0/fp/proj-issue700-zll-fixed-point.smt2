; EXPECT: sat
(set-logic ALL)
(declare-const f (_ BitVec 15))
(set-option :fp-exp true)
(set-option :produce-learned-literals true)
(assert (fp.isNaN ((_ to_fp 5 11) ((_ zero_extend 1) f))))
(check-sat)
