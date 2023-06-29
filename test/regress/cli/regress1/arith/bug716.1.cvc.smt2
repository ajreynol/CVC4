; EXIT: 1
; COMMAND-LINE: -i
; EXPECT: (error "The exponent of the POW(^) operator can only be a positive integral constant below 67108864. Exception occurred in:
; EXPECT:  (^ 3 x)")
(set-logic ALL)
(declare-fun x () Int)
(assert (= (^ 3 x) 27))
(check-sat-assuming ( (= x 3) ))
