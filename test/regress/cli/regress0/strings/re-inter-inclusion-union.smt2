; EXPECT: unsat
; Regression for CPC proof checking of the RE_INTER_INCLUSION rewrite when a
; compound component (here a re.union) appears as a plain concatenation component
; on one side and as an re.inter operand on the other. The two occurrences have
; the same meaning but slightly different flat forms (a singleton re.++ wrapper),
; so the flat-form inclusion check ($str_re_includes_rec) must short-circuit on
; equal components at its singleton-list cases; otherwise it fails to prove that
; R1 is a subset of R2 here.
(set-logic QF_S)
(declare-const x String)
(define-fun UNION () RegLan
  (re.union (str.to_re "af-south-1") (str.to_re "us-east-1") (str.to_re "us-west-2")))
(define-fun R1 () RegLan
  (re.++ (str.to_re "arn:aws:s3:")
         (re.inter UNION (re.++ (str.to_re "af") re.allchar (str.to_re "south-1")))
         (str.to_re ":job")))
(define-fun R2 () RegLan
  (re.++ (str.to_re "arn:aws:s3:") UNION (str.to_re ":job")))
(assert (str.in_re x R1))
(assert (not (str.in_re x R2)))
(check-sat)
