(set-logic HO_BV)

(synth-fun tweak ((pixel (_ BitVec 8))) (_ BitVec 8)
(( NTnonbool (_ BitVec 8)))
((NTnonbool (_ BitVec 8)(pixel (_ bv255 8) (bvxor NTnonbool NTnonbool)))
))

; abusing pixel_oracle.sh both for 'correctness' and 'hints'

; correctness (verification)
(declare-oracle-fun pixel_correct  ((-> (_ BitVec 8) (_ BitVec 8))) Bool pixel_oracle_invert.sh)

(constraint (pixel_correct tweak))

; hints (synthesis)
(oracle-constraint

  ((tweak (-> (_ BitVec 8) (_ BitVec 8))))
  ((correct Bool) (pixelIn (_ BitVec 8)) (pixelOut (_ BitVec 8)))
  (=> (not correct) (= (tweak pixelIn) pixelOut))pixel_oracle_invert.sh )

(check-synth)
