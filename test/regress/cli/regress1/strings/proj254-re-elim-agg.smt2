(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)

(set-option :re-elim agg)
(declare-fun a () String)
(assert (str.in_re a (re.++ (re.+ (str.to_re "AB")) (str.to_re "B"))))
(assert (<= (str.len a) 4))
(check-sat)
