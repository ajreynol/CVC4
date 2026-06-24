; EXPECT: unsat
; Regression for CPC proof checking of the STR_IN_RE_CONSUME rewrite. The
; intersection (re.* alnum) & (re.allchar ++ "s3") has its re.* child first, which
; does not fully consume, so $str_re_consume_inter must still detect the conflict in
; the second child ("...s3" cannot follow the "arn:aws:s3:" prefix). Also exercises
; flattening of re.inter whose printed re.all terminator is an explicit operand.
(set-logic QF_S)
(declare-const resource String)
(assert (str.in_re resource (re.++ (str.to_re "arn:aws:s3:") (re.* re.allchar))))
(assert (str.in_re resource
  (re.++ (str.to_re "arn:aws:")
         (re.inter (re.* (re.union (re.range "a" "z") (re.range "0" "9") (str.to_re "-")))
                   (re.++ re.allchar (str.to_re "s3")))
         (str.to_re ":region:job"))))
(check-sat)
