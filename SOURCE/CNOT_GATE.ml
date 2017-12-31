(* ========================================================================= *)
(*                                                                           *)
(*                          CNOT_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "FLIP_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 


let CNOT1_GATE = define   `CNOT1_GATE ((x1:sm), (x2:sm), (y2:sm), (y1:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (c1:sm).
HADAMARD_GATE (x1, a1, ten, LH, LV) /\
CZ_GATE (a1, x2, c1, y1,ten, LH, LV ,m_modes_pro) /\
HADAMARD_GATE (c1, y2, ten, LH, LV))` ;;

let CNOT2_GATE = define   `CNOT2_GATE ((x2:sm), (x1:sm), (y1:sm), (y2:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (c1:sm).
HADAMARD_GATE (x1, a1, ten, LH, LV) /\
CZ_GATE (x2, a1, y1, c1,ten, LH, LV ,m_modes_pro) /\
HADAMARD_GATE (c1, y2, ten, LH, LV))` ;;

        
        
let CNOT_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
CFUN_SMUL_LID;CNOT1_GATE] THEN REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(c1:sm)`] THEN
ASM_SIMP_TAC [ARITH_RULE `2 = (1+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN   
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
STRIP_TAC THEN hadamard_tac "cn1" "a1" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex a2.  ((a2 % f1) y) * ((f2) x)  =  (a2) * (f1 y * f2 x)  
/\ ((f1) y) * ((a2 % f2) x)  =  (a2) * (f1 y * f2 x)`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ 1 <= dimindex (:N))) `] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N)) )) `] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
 STRIP_TAC THEN cz_tac "a1" "cn2" "c1" "cn3" THEN
REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[IMP_IMP] THEN
ASM_SIMP_TAC [ARITH_RULE `2 = ((1+1))/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN   
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 STRIP_TAC THEN hadamard_tac "c1" "cn4" THEN
 REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[IMP_IMP] THEN
SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex a2.  ((a2 % f1) y) * ((f2) x)  =  (a2) * (f1 y * f2 x)  /\
(( f1) y) * ((a2 % f2) x)  =  (a2) * (f1 y * f2 x)  /\ ((f1) y) * ((f2) x)  = (f1 y * f2 x)  `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ 1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N)) )) `] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW ;SQRT_DIV;SQRT_1;
GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_FIELD `inv (sqrt (&2)) = &1 / sqrt (&2)`;
REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;REAL_MUL_LNEG;
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0] 
 ` ((&1 / sqrt (&2)) * sqrt (&2) = &1) `;
REAL_FIELD `&1 / &2 * &1 / &4 + &1 / &2 * &1 / &4 = &1 / &4`];;



let CNOT1_00 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT1_GATE (cn1,cn2,cn4,cn3,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LH (cn1)  else LH (cn2)):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LH (cn4)  else LH (cn3)))`,CNOT_tactic);;


let CNOT1_01 =  prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT1_GATE (cn1,cn2,cn4,cn3,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LV (cn1)  else LH (cn2)):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LV (cn4)  else LH (cn3)))`,CNOT_tactic);;

let CNOT1_10 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT1_GATE (cn1,cn2,cn4,cn3,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LH (cn1)  else LV (cn2)):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LV (cn4)  else LV (cn3)))`,CNOT_tactic);;

let CNOT1_11 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT1_GATE (cn1,cn2,cn4,cn3,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LV (cn1)  else LV (cn2)):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LH (cn4)  else LV (cn3)))`,CNOT_tactic);;


let cnot1_tac cn1 cn2 cn4 cn3 = 
 SUBGOAL_TAC "cnot100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT1_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT1_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT1_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT1_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT1_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT1_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT1_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT1_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "cnot110" (fun thm-> ALL_TAC) THEN
REMOVE_THEN "cnot101" (fun thm-> ALL_TAC) THEN
REMOVE_THEN "cnot100" (fun thm-> ALL_TAC) THEN
REMOVE_THEN "cnot111" (fun thm-> ALL_TAC);;
 
 
let CNOT2_tactic = 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CNOT2_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(c1:sm)`] THEN
ASM_SIMP_TAC [ARITH_RULE `2 = (1+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN   
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
STRIP_TAC THEN hadamard_tac "cn1" "a1" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex a2.  ((f1) y) * ((a2 % f2) x)  = 
     (a2) * (f1 y * f2 x)  `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ 1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N)) )) `] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
 STRIP_TAC THEN cz_tac "cn2" "a1" "cn3" "c1" THEN
REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[IMP_IMP] THEN
ASM_SIMP_TAC [ARITH_RULE `2 = ((1+1))/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN   
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
STRIP_TAC THEN hadamard_tac "c1"  "cn4" THEN
 REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[IMP_IMP] THEN
SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex a2.  ((f1) y) * ((a2 % f2) x)  = 
     (a2) * (f1 y * f2 x)  /\ ((f1) y) * ((f2) x)  = 
     (f1 y * f2 x)  `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ 1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N)) )) `] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW ;SQRT_DIV;SQRT_1;
GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_FIELD `inv (sqrt (&2)) = &1 / sqrt (&2)`;
REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;REAL_MUL_LNEG;
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0]  
` ((&1 / sqrt (&2)) * sqrt (&2) = &1) `; 
REAL_FIELD `&1 / &2 * &1 / &4 + &1 / &2 * &1 / &4 = &1 / &4`];;




let CNOT2_00 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LH cn2  else LH cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then  LH cn3  else LH cn4))`,CNOT2_tactic);;


let CNOT2_01 =  prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LV cn2  else LH cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LV cn3  else LV cn4))`,CNOT2_tactic);;

let CNOT2_10 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LH cn2  else LV cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LH cn3  else LV cn4))`,CNOT2_tactic);;

let CNOT2_11 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LV cn2  else  LV cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LV cn3  else LH cn4))`,CNOT2_tactic);;

 
 let CNOT2_0vac = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LH cn2  else vac cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LH cn3  else vac cn4))`,CNOT2_tactic);;


let CNOT2_vac1 =  prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then vac cn2  else LV cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then vac cn3  else LV cn4))`,CNOT2_tactic);;

let CNOT2_1vac = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then LV cn2  else vac cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then LV cn3  else vac cn4))`,CNOT2_tactic);;

let CNOT2_vac0 = prove(`!(cn1:sm) (cn2:sm) (cn4:sm) (cn3:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CNOT2_GATE (cn2,cn1,cn3,cn4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i.  if i = 1 then vac cn2  else  LH cn1):bqs^N) = Cx (&1 / &4) %
 (tensor 2 (lambda i. if i = 1 then vac cn3  else LH cn4))`,CNOT2_tactic);;
 

 
let cnot2_tac cn2 cn1 cn3 cn4 = 
 SUBGOAL_TAC "cnot21v" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_1vac))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_1vac] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot20v" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_0vac))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_0vac] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot2v1" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_vac1))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_vac1] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot2v0" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_vac0))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_vac0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot200" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot210" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot201" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cnot211" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cn1",cn1) 
 (SPEC_V("cn2",cn2) (SPEC_V ("cn4",cn4) (SPEC_V("cn3",cn3) CNOT2_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CNOT2_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN
REMOVE_THEN "cnot20v" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot21v" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot2v1" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot2v0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot210" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot201" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot200" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cnot211" (fun thm-> ALL_TAC);;