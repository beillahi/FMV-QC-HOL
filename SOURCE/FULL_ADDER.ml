(* ========================================================================= *)
(*                                                                           *)
(*                           FULL_ADDER.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: October 24, 2017                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "tactics_2.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(* 62 optical qubits *)
(*5 + 3 + 2 * 3 = 14 CZ gates *)
(*--------------------**********************------------------*) 

let tensor1_blin = prove(` !a x1 x2. 1 <=  dimindex (:N) ==>
        (tensor 1 ((lambda i. x1 + x2):bqs^N) =
                tensor 1 ((lambda i. x1 ):bqs^N) +
                tensor 1 ((lambda i. x2):bqs^N)) /\
        tensor 1 ((lambda i. a % x1):bqs^N) =
                a % tensor 1 ((lambda i. x1 ):bqs^N)`,
    SIMP_TAC [tensor;ONE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` 1 <= 1`]
    THEN CFUN_ARITH_TAC);;
    
let F_ADDER = define 
`F_ADDER ((x1:sm), (x2:sm), (x3:sm), (x4:sm), 
(y1:sm), (y2:sm), (y3:sm), (y4:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=>  
(!(b0:sm) (b1:sm) (b2:sm) (b3:sm) (c1:sm) (c2:sm) (c0:sm) (d1:sm) (d2:sm).
CNOT2_GATE (x1,x2,b0,b1,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (x3,x4,b2,b3,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (b1,b2,c1,c2,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE (b0,c1,c0,d1,ten,LH,LV,m_modes_pro) /\
SWAP_GATE (c2,b3,d2, y4,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE (c0,d1,d2,y1,y2,y3,ten,LH,LV,m_modes_pro))` ;;
    
let adder_tactics =     
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
F_ADDER] THEN REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [
`(b0:sm)`; `(b1:sm)`; `(b2:sm)`; `(b3:sm)`; `(c1:sm)`; 
`(c2:sm)`; `(c0:sm)`; `(d1:sm)`; `(d2:sm)`] THEN
    REPEAT GEN_TAC THEN integer_equiv 4 THEN
    ASM_SIMP_TAC ([(main_comp_inputs [1;1;1;1] 4);tensor_nmlem1] @ 
    (one_less 4)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l [1;1;1;1]) THEN
    rewrite_decompose_tac 4 [1;1;1;1] 0 0 THEN
    rew_condition_tac  4 [1;1;1;1]  0 THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l [1;1;1;1])) THEN
    ASM_SIMP_TAC[tensor1_blin] THEN
    SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
    COMPLEX_ADD_LDISTRIB;
    COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
    SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    SIMP_TAC ((GSYM CX_MUL) :: (rewr_dev 4 0)) THEN
    SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) =
    a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
    IMP_REWRITE_TAC[GSYM (main_comp_inputs [1;1;1;1] 4);
    REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH] THEN 
    ONCE_SIMP_TAC (rewrite_l [4]) THEN 
    rewrite_recompose_tac  4 [1;1;1;1] 0 0 THEN
    SIMP_TAC[condition_recompose 4 [1;1;1;1]] THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l [4])) THEN
    quantum_sub_tac [["0"; "CNOT2_GATE"; "2"; "ad1"; "ad2"; "b0"; "b1"; "ten"; "LH"; "LV";
     "pro"];
    ["2"; "CNOT2_GATE"; "2"; "ad3"; "ad4"; "b2"; "b3"; "ten"; "LH"; "LV";
     "pro"]] 4 [] THEN
   quantum_sub_tac [["1"; "CNOT2_GATE"; "2"; "b1"; "b2"; "c1"; "c2"; "ten"; "LH"; "LV";
     "pro"]] 4 [] THEN
   quantum_sub_tac [["0"; "SWAP_GATE"; "2"; "b0"; "c1"; "c0"; "d1"; "ten"; "LH"; "LV"; "pro"];
    ["2"; "SWAP_GATE"; "2"; "c2"; "b3"; "d2"; "ad8"; "ten"; "LH"; "LV"; "pro"]] 4 [] THEN
   quantum_sub_tac [["0"; "FREDKIN1_GATE"; "3"; "c0"; "d1"; "d2"; "ad5"; "ad6"; "ad7"; "ten";
     "LH"; "LV"; "pro"]] 4 [] THEN
    SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
    CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
    CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
    GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
    REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
    REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW;REAL_MUL_SYM;GSYM real_sub;
    GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
    CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
    REAL_MUL_LNEG] THEN SIMP_TAC[thm1;thm2;SQRT_DIV;SQRT_1;
    GSYM REAL_POW_2;REAL_POS;SQRT_POW_2] THEN CONV_TAC NUM_REDUCE_CONV
    THEN TRY (CFUN_ARITH_TAC);;

    
    
    let FULL_ADDER_000 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LH (ad5) else if i = 2 
     then LH (ad6) else if i = 3 then LH (ad7) else LH (ad8))`,adder_tactics);;
     
     
    let FULL_ADDER_001 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then  LH (ad1)
else  if i = 2 then  LH (ad2) else if i = 3 then 
 LV (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LH (ad5) else if i = 2
     then LH (ad6) else if i = 3 then LV (ad7) else LV (ad8)) `,adder_tactics);;
     
     
    let FULL_ADDER_010 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1)  
else  if i = 2 then  LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) %
     tensor 4 (lambda i. if i = 1 then LV (ad5) else if i = 2
     then LH (ad6) else if i = 3 then LH (ad7) else LV (ad8))`,adder_tactics);;
     
    let FULL_ADDER_011 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LV (ad5) else if i = 2
     then LV (ad6) else if i = 3 then LH (ad7) else LH (ad8))`,adder_tactics);;
     
     
    let FULL_ADDER_100 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then  LV (ad1)
else  if i = 2 then LH (ad2) else if i = 3 then 
 LH (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LV (ad5) else if i = 2
     then LH (ad6) else if i = 3 then LV (ad7) else LV (ad8)) `,adder_tactics);;
     
    let FULL_ADDER_101 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1)
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) %
     tensor 4 (lambda i. if i = 1 then LV (ad5) else if i = 2
     then LV (ad6) else if i = 3 then LV (ad7) else LH (ad8))`,adder_tactics);;
     
     
let FULL_ADDER_110 = time prove(
 `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1)
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LH (ad5) else if i = 2
     then LV (ad6) else if i = 3 then LH (ad7) else LH (ad8))`,adder_tactics);;

     
    let FULL_ADDER_111 =  prove(
`!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1)
else  if i = 2 then  LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
    Cx (&1 / &268435456) % 
     tensor 4 (lambda i. if i = 1 then LH (ad5) else if i = 2
     then LV (ad6) else if i = 3 then LV (ad7) else LV (ad8))`,adder_tactics);;


let full_adder_tac l = 
 SUBGOAL_TAC "FULL_ADDER_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_000))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_000] THEN CFUN_ARITH_TAC] THEN 
 SUBGOAL_TAC "FULL_ADDER_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_001))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_010))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_011))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_100))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_101))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_110))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FULL_ADDER_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) FULL_ADDER_111))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FULL_ADDER_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "FULL_ADDER_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "FULL_ADDER_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FULL_ADDER_111" (fun thm-> ALL_TAC);;   