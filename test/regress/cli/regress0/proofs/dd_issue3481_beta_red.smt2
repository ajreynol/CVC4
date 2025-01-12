; EXPECT: unsat
(set-logic ADTLIRA)
(define-fun i ((y Int)) Bool false)
(define-fun d ((temp___expr_18 Int) (temp___is_init_14 Bool) (temp___skip_constant_15 Bool) (temp___do_toplevel_16 Bool) (temp___do_typ_inv_17 Bool)) Bool (or (i temp___expr_18)))
(assert (exists ((y Int)) (d y false false true true)))
(check-sat)
