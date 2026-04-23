; COMMAND-LINE: --dump-proofs --proof-granularity=theory-rewrite
; SCRUBBER: grep -o 'unsat\|macro-quant-macro-def\|TRUST SUBS_EQ'
; EXPECT: unsat
; EXPECT: macro-quant-macro-def
(set-logic UFLIA)
(set-option :macros-quant true)

(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (P x)))
(assert (not (P 0)))

(check-sat)
