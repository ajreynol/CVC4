; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ADTLIRA)
(define-fun i ((y Int)) Bool false)
(define-fun d ((x Int)) Bool (or (i x)))
(assert (exists ((y Int)) (d y)))
(check-sat)
