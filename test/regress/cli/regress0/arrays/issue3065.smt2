(set-info :smt-lib-version 2.6)
(set-logic AUFBVFPDTNIRA)
(set-option :incremental true)

(declare-sort ty 0)

(declare-sort tuple0 0)

(declare-fun x () (Array Int (Array Int Int)))

(declare-fun x1 () (Array Int (Array Int Int)))

(assert
;; VC_test_map_multidim1
 ;; File "bench/ce/map/../map.mlw", line 13, characters 12-30
  (not (not (= (select (select x1 0) 0) (select (select x1 1) 1)))))
(check-sat)

;; Ensures
  (assert (= x1 (store x 0 (select x 1))))

(check-sat)
