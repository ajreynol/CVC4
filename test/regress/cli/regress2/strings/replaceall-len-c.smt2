(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status sat)

(set-option :strings-fmf true)
(declare-fun x () String)
(assert (= (str.len (str.replace_all "ABBABAAB" x "C")) 5))
(check-sat)
