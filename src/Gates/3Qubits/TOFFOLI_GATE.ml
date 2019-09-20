(* ========================================================================= *)
(*                                                                           *)
(*                          TOFFOLI_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "../TS_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*18 optical qubits *)
(*3 CZ gates *)
(*--------------------**********************------------------*) 

let TOFFOLI3_GATE = define 
`TOFFOLI3_GATE ((x1:sm), (x2:sm), (x3:sm), (y1:sm), (y2:sm), (y3:sm),
ten , (LH:sm->(real->complex)), (LV:sm->(real->complex)),
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex))) <=> 
(? (c3:sm) (d3:sm) (c1:sm) (d1:sm).
HADAMARD_GATE (x3, c3, ten,LH, LV) /\ FLIP_GATE (x1,c1,ten,LH, LV) /\
TS_GATE (c1,x2,c3,d1,y2,d3,ten,LH, LV,m_modes_pro) /\
FLIP_GATE (d1,y1,ten,LH, LV) /\ HADAMARD_GATE (d3,y3, ten,LH, LV))`;;


let TOFFOLI1_GATE = define 
`TOFFOLI1_GATE ((x1:sm), (x2:sm), (x3:sm), (y1:sm), (y2:sm), (y3:sm),
ten , (LH:sm->(real->complex)), (LV:sm->(real->complex)),
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex))) <=> 
(? (c1:sm) (d1:sm) (e1:sm) (f1:sm).
HADAMARD_GATE (x1, c1, ten,LH, LV) /\ FLIP_GATE (c1,d1,ten,LH, LV) /\
TS_GATE (d1,x2,x3,e1,y2,y3,ten,LH, LV,m_modes_pro) /\
FLIP_GATE (e1,f1,ten,LH, LV) /\ HADAMARD_GATE (f1,y1, ten,LH, LV))`;;


let TOFFOLI1_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;TOFFOLI1_GATE] THEN
REPEAT GEN_TAC THEN    
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `3 = ((1+1)+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
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
STRIP_TAC THEN hadamard_tac "tf1" "c1" THEN flip_tac "c1" "d1" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex tf2.  ((tf2 % f1) y) * ((f2) x) * ((f3) z) = 
     (tf2) * (f1 y * f2 x) * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 3 <= dimindex (:N) /\ 1 <= dimindex (:N))) `]
THEN ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC[ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2
 then if i = 1 then tf1 else tf2  else tf3 else g i) =
(if i <= 3 /\ 1 <= i 
 then if i = 1 then tf1 else if i = 2 then  tf2  else tf3 else g i)`] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
 STRIP_TAC THEN ts_tac "d1" "tf2" "tf3" "e1" "tf5" "tf6" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;ARITH_RULE `3 = ((1+1)+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
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
STRIP_TAC THEN flip_tac "e1" "f1"  THEN hadamard_tac "f1" "tf4" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex tf2.  ((tf2 % f1) y) * ((f2) x) * ((f3) z) = 
     (tf2) * (f1 y * f2 x) * f3 z /\ ((f1) y) * ((f2) x) * ((f3) z) = 
     (f1 y * f2 x) * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 3 <= dimindex (:N) /\ 1 <= dimindex (:N))) `]
THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC[ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2
 then if i = 1 then tf1 else tf2  else tf3 else g i) =
(if i <= 3 /\ 1 <= i 
 then if i = 1 then tf1 else if i = 2 then  tf2  else tf3 else g i)`] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_ASSOC;CFUN_ADD_SYM;
CFUN_ADD_LID;CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
 CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;CFUN_ADD_SYM;
GSYM CX_ADD;CFUN_ADD_AC;CFUN_SUB_AC;CFUN_SMUL_LZERO;REAL_ADD_AC;
REAL_SUB_REFL;GSYM CX_MUL; GSYM CX_ADD; GSYM CX_SUB;REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;
REAL_ADD_RINV;REAL_ADD_LID;REAL_ADD_RID;
CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun) (k:cfun). 
  b%a + c%a +d = (b+c) % a +d   /\  k + b%a +   c%a + f = k + f +  (b+c) % a `;
REAL_ADD_AC;GSYM CX_MUL; GSYM CX_ADD; GSYM CX_SUB;CFUN_ADD_AC;SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;GSYM CX_ADD;
REAL_MUL_RID;GSYM CFUN_ADD_RDISTRIB;
CFUN_ADD_LID;REAL_FIELD `inv (sqrt (&2)) = &1 / sqrt (&2)  `;REAL_ADD_LINV;REAL_MUL_LZERO;REAL_DIV_RMUL;
REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_RZERO;REAL_SUB_REFL;REAL_NEG_NEG;REAL_MUL_LNEG;
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0]  ` ((&1 / sqrt (&2)) * sqrt (&2) = &1) `;
REAL_FIELD `&1 / &2 * &1 / &64 + &1 / &2 * &1 / &64 = &1 / &64`];;


let TOFFOLI3_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;TOFFOLI3_GATE] THEN
REPEAT GEN_TAC THEN    
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `3 = ((1+1)+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
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
STRIP_TAC THEN hadamard_tac "tf3" "c3" THEN flip_tac "tf1" "c1" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex tf2.  ((f1) y) * ((f2) x) * ((tf2 % f3) z) = 
     (tf2) * (f1 y * f2 x) * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 3 <= dimindex (:N) /\ 1 <= dimindex (:N))) `]
THEN ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC[ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2
 then if i = 1 then tf1 else tf2  else tf3 else g i) =
(if i <= 3 /\ 1 <= i 
 then if i = 1 then tf1 else if i = 2 then  tf2  else tf3 else g i)`] THEN
 ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
 STRIP_TAC THEN ts_tac "c1" "tf2" "c3" "d1" "tf5" "d3" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;ARITH_RULE `3 = ((1+1)+1)/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
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
STRIP_TAC THEN flip_tac  "d1" "tf4" THEN hadamard_tac "d3" "tf6" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex tf2.  ((f1) y) * ((f2) x) * ((tf2 % f3) z) = 
     (tf2) * (f1 y * f2 x) * f3 z /\ ((f1) y) * ((f2) x) * ((f3) z) = 
     (f1 y * f2 x) * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(8 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 3 <= dimindex (:N) /\ 1 <= dimindex (:N))) `]
THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC[ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2
 then if i = 1 then tf1 else tf2  else tf3 else g i) =
(if i <= 3 /\ 1 <= i 
 then if i = 1 then tf1 else if i = 2 then  tf2  else tf3 else g i)`] THEN
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
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0]  ` ((&1 / sqrt (&2)) * sqrt (&2) = &1) `;
REAL_FIELD `&1 / &2 * &1 / &64 + &1 / &2 * &1 / &64 = &1 / &64`];;




let TOFFOLI1_001 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N)
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LH (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LH (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;


let TOFFOLI1_101 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LH (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LH (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;


let TOFFOLI1_111 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm) 
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LV (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LV (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;




let TOFFOLI1_011 = prove( `!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LV (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LV (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;


let TOFFOLI1_000 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N)  
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LH (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LH (tf5) else  LH (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;


let TOFFOLI1_100 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N)
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LH (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LH (tf5) else  LH (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;




let TOFFOLI1_110 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LV (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LV (tf5) else  LH (tf6)))`,integer_equiv 8 THEN TOFFOLI1_tactic);;




let TOFFOLI1_010 = prove( `!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI1_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LV (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LV (tf5) else  LH (tf6)))`, integer_equiv 8 THEN TOFFOLI1_tactic);;



let toffoli1_tac tf1 tf2 tf3 tf4 tf5 tf6 = 
 SUBGOAL_TAC "TOFFOLI1_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_000))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_000] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_001))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_010))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_011))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_100))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_101)))))))))
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_110))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI1_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI1_111))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI1_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "TOFFOLI1_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "TOFFOLI1_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI1_111" (fun thm-> ALL_TAC);;




let TOFFOLI3_001 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N)  
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LH (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LH (tf5) else  LV (tf6)))`,integer_equiv 8 THEN TOFFOLI3_tactic);;


let TOFFOLI3_101 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LH (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LH (tf5) else  LV (tf6)))`,integer_equiv 8 THEN TOFFOLI3_tactic);;


let TOFFOLI3_111 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm) 
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N)  
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LV (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LV (tf5) else  LH (tf6)))`, integer_equiv 8 THEN TOFFOLI3_tactic);;




let TOFFOLI3_011 = prove( `!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LV (tf2) else LV (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LV (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI3_tactic);;


let TOFFOLI3_000 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LH (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LH (tf5) else  LH (tf6)))`,integer_equiv 8 THEN TOFFOLI3_tactic);;


let TOFFOLI3_100 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LH (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LH (tf5) else  LH (tf6)))`,integer_equiv 8 THEN  TOFFOLI3_tactic);;




let TOFFOLI3_110 = prove(`!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (tf1) else if i = 2 then  LV (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LV (tf4) else if i = 2
then LV (tf5) else  LV (tf6)))`, integer_equiv 8 THEN TOFFOLI3_tactic);;




let TOFFOLI3_010 = prove( `!(tf1:sm) (tf2:sm) (tf3:sm) (tf4:sm) (tf5:sm) (tf6:sm)
 (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TOFFOLI3_GATE (tf1,tf2,tf3,tf4,tf5,tf6,ten,LH, LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (tf1) else if i = 2 then  LV (tf2) else LH (tf3)):bqs^N) =
 Cx (&1 / &64) % (tensor 3 (lambda i. if i = 1 then LH (tf4) else if i = 2
then LV (tf5) else  LH (tf6)))`, integer_equiv 8 THEN TOFFOLI3_tactic);;



let toffoli3_tac tf1 tf2 tf3 tf4 tf5 tf6 = 
 SUBGOAL_TAC "TOFFOLI3_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_000))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_000] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_001))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_010))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_011))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_100))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_101)))))))))
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_110))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "TOFFOLI3_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("tf1",tf1)
(SPEC_V ("tf2",tf2) (SPEC_V ("tf3",tf3) (SPEC_V("tf4",tf4) 
(SPEC_V ("tf5",tf5) (SPEC_V("tf6",tf6) TOFFOLI3_111))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TOFFOLI3_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "TOFFOLI3_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "TOFFOLI3_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "TOFFOLI3_111" (fun thm-> ALL_TAC);;