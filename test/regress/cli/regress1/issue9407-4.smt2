; EXPECT: sat
(set-logic QF_ABV)
(declare-const __ (_ BitVec 9))
(declare-fun mem_35_192 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun mem_35_191 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun t_190 () (_ BitVec 1))
(declare-fun t_189 () (_ BitVec 1))
(declare-fun t_188 () (_ BitVec 1))
(declare-fun t_187 () (_ BitVec 1))
(declare-fun t_186 () (_ BitVec 1))
(declare-fun t_185 () (_ BitVec 1))
(declare-fun t_184 () (_ BitVec 1))
(declare-fun t_183 () (_ BitVec 1))
(declare-fun t_182 () (_ BitVec 1))
(declare-fun t_181 () (_ BitVec 1))
(declare-fun T_1t0_6762_133 () (_ BitVec 1))
(define-fun T_32t5_6767_132 () (_ BitVec 32) (_ bv0 32))
(declare-fun R_ZF_13_127 () (_ BitVec 1))
(declare-fun T_32t3_6775_105 () (_ BitVec 32))
(define-fun T_32t1_6773_104 () (_ BitVec 32) ((_ zero_extend 16) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 2) __))))))))
(declare-fun T_32t2_6779_98 () (_ BitVec 32))
(define-fun R_EBP_0_64 () (_ BitVec 32) ((_ zero_extend 16) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 2) __))))))))
(declare-fun R_ESP_1_61 () (_ BitVec 32))
(declare-fun madebysaiyan_0 () (_ BitVec 32))
(assert (= (_ bv1 1) (bvand (ite (= t_190 (ite (= T_32t2_6779_98 (bvsub R_ESP_1_61 (_ bv4 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_189 (ite (= mem_35_191 (store (store (store (store mem_35_192 (bvadd T_32t2_6779_98 (_ bv3 32)) ((_ extract 7 0) (bvlshr R_EBP_0_64 (_ bv24 32)))) (bvadd T_32t2_6779_98 (_ bv2 32)) ((_ extract 7 0) (bvlshr R_EBP_0_64 (bvashr (_ bv6 32) (bvsub (bvudiv (bvmul (_ bv8 32) (_ bv4294967291 32)) (bvadd T_32t1_6773_104 madebysaiyan_0)) (bvsrem (bvadd (_ bv4294967286 32) (_ bv4294967289 32)) (bvor (_ bv8 32) T_32t3_6775_105))))))) (bvadd T_32t2_6779_98 (_ bv1 32)) ((_ extract 7 0) (bvlshr R_EBP_0_64 (_ bv8 32)))) (bvadd T_32t2_6779_98 (_ bv0 32)) ((_ extract 7 0) R_EBP_0_64))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_188 (ite (= T_32t1_6773_104 (bvadd T_32t2_6779_98 (_ bv8 32))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_187 (ite (= T_32t3_6775_105 (bvor (concat (_ bv0 24) (select mem_35_191 (bvadd T_32t1_6773_104 (_ bv0 32)))) (bvshl (concat (_ bv0 24) (select mem_35_191 (bvadd T_32t1_6773_104 (_ bv1 32)))) (_ bv8 32)) (bvshl (concat (_ bv0 24) (select mem_35_191 (bvadd T_32t1_6773_104 (_ bv2 32)))) (_ bv16 32)) (bvshl (concat (_ bv0 24) (select mem_35_191 (bvadd T_32t1_6773_104 (_ bv3 32)))) (_ bv24 32)))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_186 (ite (= R_ZF_13_127 (ite (= T_32t3_6775_105 (_ bv0 32)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_185 (ite (= T_32t5_6767_132 (concat (_ bv0 31) R_ZF_13_127)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_184 (ite (= T_1t0_6762_133 ((_ extract 0 0) T_32t5_6767_132)) (_ bv1 1) (_ bv0 1))) (_ bv1 1) (_ bv0 1)) (ite (= t_183 (bvor t_181 t_182)) (_ bv1 1) (_ bv0 1)) (ite (= t_182 (bvnot T_1t0_6762_133)) (_ bv1 1) (_ bv0 1)) (ite (= t_181 T_1t0_6762_133) (_ bv1 1) (_ bv0 1)) (bvnot (_ bv0 1)) t_190 t_189 t_188 t_187 t_186 t_185 t_184 t_183 (_ bv1 1))))
(check-sat)
