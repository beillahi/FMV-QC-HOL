(* ========================================================================= *)
(*                                                                           *)
(*                          TS_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "SWAP_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*18 optical qubits *)
(*3 CZ gates *)
(*--------------------**********************------------------*) 


let TS_inputs =  
 define `TS_inputs ( (c1:sm^N),(t1:sm), (t2:sm), (t3:sm),
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
(tensor 3 ((lambda i.  if i = 1 then LH (t1) else if  i = 2 then LH (t2) else LH (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LH (t1) else if i = 2 then  vac (t2) else
if i = 3 then  LH (t3) else LH (c1$4)):bqs^N) /\ 
(tensor 3 ((lambda i.  if i = 1 then LH (t1) else if  i = 2 then LH (t2) else LV (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LH (t1) else if i = 2 then  vac (t2) else
if i = 3 then  LV (t3) else LH (c1$4)):bqs^N) /\ 
(tensor 3 ((lambda i.  if i = 1 then LH (t1) else if  i = 2 then LV (t2) else LH (t3) ):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LH (t1) else if i = 2 then  LV (t2) else
if i = 3 then  LH (t3) else vac (c1$4)):bqs^N) /\ 
(tensor 3 ((lambda i.  if i = 1 then LH (t1) else if  i = 2 then LV (t2) else LV (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LH (t1) else if i = 2 then  LV (t2) else
if i = 3 then  LV (t3) else vac (c1$4)):bqs^N) /\   
(tensor 3 ((lambda i.  if i = 1 then LV (t1) else if  i = 2 then LH (t2) else LH (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LV (t1) else if i = 2 then  vac (t2) else
if i = 3 then  LH (t3) else LH (c1$4)):bqs^N) /\   
(tensor 3 ((lambda i.  if i = 1 then LV (t1) else if  i = 2 then LH (t2) else LV (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LV (t1) else if i = 2 then  vac (t2) else
if i = 3 then  LV (t3) else LH (c1$4)):bqs^N) /\   
(tensor 3 ((lambda i.  if i = 1 then LV (t1) else if  i = 2 then LV (t2) else LH (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LV (t1) else if i = 2 then  LV (t2) else
if i = 3 then  LH (t3) else vac (c1$4)):bqs^N) /\   
(tensor 3 ((lambda i.  if i = 1 then LV (t1) else if  i = 2 then LV (t2) else LV (t3)):bqs^N)) =
tensor 4 ((lambda i. if i = 1 then LV (t1) else if i = 2 then  LV (t2) else
if i = 3 then  LV (t3) else vac (c1$4)):bqs^N)`;;


let TS_outputs =  
 define `TS_outputs ((c1:sm^N), (y1:sm), (y2:sm),(y3:sm),
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
(tensor 4 ((lambda i. if i = 1 then LH (y1) else if i = 2
then vac (y2) else if i = 3 then LH (y3) else LH (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LH (y1) else 
if  i = 2 then LH (y2) else LH (y3)):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LH y1 else if i = 2
then LV y2 else if i = 3 then LH y3 else vac (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LH y1 else 
if  i = 2 then LV y2 else LH y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LH y1 else if i = 2
then vac y2 else if i = 3 then LV y3 else LH (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LH y1 else 
if  i = 2 then LH y2 else LV y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LH y1 else if i = 2
then LV y2 else if i = 3 then LV y3 else vac (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LH y1 else 
if  i = 2 then LV y2 else LV y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LV y1 else if i = 2
then vac y2 else if i = 3 then LH y3 else LH (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LV y1 else 
if  i = 2 then LH y2 else LH y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LV y1 else if i = 2
then vac y2 else if i = 3 then LV y3 else LH (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LV y1 else 
if  i = 2 then LH y2 else LV y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LV y1 else if i = 2
then LV y2 else if i = 3 then LH y3 else vac (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LV y1 else 
if  i = 2 then LV y2 else LH y3):bqs^N)) /\
(tensor 4 ((lambda i. if i = 1 then LV y1 else if i = 2
then LV y2 else if i = 3 then LV y3 else vac (c1$4)):bqs^N)) =
(tensor 3 ((lambda i.  if i = 1 then LV y1 else 
if  i = 2 then LV y2 else LV y3):bqs^N))`;;





let IS_TS_MODEL = define `IS_TS_MODEL ((x1:sm), (x2:sm), (x3:sm), (y1:sm),
(y2:sm),(y3:sm),(c1:sm), (c2:sm), (d2:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)),
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(CNOT2_GATE (x1,x2,c1,c2,ten,LH,LV,m_modes_pro) /\   
CZ_GATE (c2, x3, d2, y3,ten,LH, LV ,m_modes_pro) /\
CNOT2_GATE (c1,d2,y1,y2,ten,LH,LV,m_modes_pro) ) `;;



let TS_GATE = define 
   `TS_GATE ((x1:sm), (x2:sm), (x3:sm), (y1:sm),(y2:sm),(y3:sm),ten, 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
    (? (k:sm^N) (c1:sm) (c2:sm) (d2:sm). 
    IS_TS_MODEL (x1,x2,x3,y1,y2,y3,c1,c2,d2,ten,LH,LV,m_modes_pro) /\ 
    TS_outputs (k,y1, y2, y3,LH,LV) /\ TS_inputs (k, x1, x2,x3,LH,LV))`;;



let TS_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;TS_GATE] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[IS_TS_MODEL] THEN
ASM_SIMP_TAC [TS_inputs ] THEN
ASM_SIMP_TAC [GSYM TS_inputs ] THEN
ASM_SIMP_TAC [ARITH_RULE `4 = 2 + 2 /\  1 <= 2  `;tensor_nmlem1;ARITH_RULE 
    `(4 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
    <=> (4 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((4 <= dimindex (:N)) ==>(i <= 2 ==> (i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_1mlem1d)] THEN   
SIMP_TAC [ ARITH_RULE `(1 <= i ==> ((i = 0) = F)) /\
(if i <= 2 /\ 1 <= i then if i = 1 then ts1
else if i = 2 then ts2 else if i = 3 then ts3 else x4 else g i) = 
(if i <= 2 /\ 1 <= i then if i = 1 then ts1 else  ts2  else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
STRIP_TAC THEN cnot2_tac "ts1" "ts2"  "c1" "c2" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f2:A^N->complex ts2.   ((ts2 % f2) x) * ((f3) z) = 
     (ts2) *  f2 x * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE ` 2 + 2 = 4  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `4 <= dimindex (:N) ==>  (2 <= dimindex (:N)) `;ARITH]
THEN ONCE_SIMP_TAC[(tensor_1mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((4 <= dimindex (:N)) ==>(i <= 4 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC [ ARITH_RULE `(if i <= 4 /\ 1 <= i then if i <= 2 then if i = 1 then ts1 else ts2
   else if i - 2 = 1 then ts3 else x4 else g i) = 
   (if i <= 4 /\ 1 <= i then if i = 1 then ts1
   else if i = 2 then ts2 else if i = 3 then ts3 else x4 else g i)`]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]  THEN
ASM_SIMP_TAC [ARITH_RULE `4 = (1 + 2) + 1 /\  1 <= 2 /\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
    `(4 <= dimindex (:N) ==>  2 <= dimindex (:N) /\ 1 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
    <=> (4 <= dimindex (:N) /\  2 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d);(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((4 <= dimindex (:N)) ==>(i <= 2 ==> (i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) )) /\
    ((4 <= dimindex (:N)) ==>(i <= 1 ==> (i + 2 <= dimindex (:N) /\ i + 3 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_1mlem1d);(ISPECL [`1`] tensor_1mlem1d)] THEN 
SIMP_TAC [ ARITH_RULE `(1 <= i ==> ((i = 0) = F)) /\
((( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)) /\
(if i <= 2 /\ 1 <= i then if i = 1 then ts1
else if i = 2 then ts2 else x4 else g i) = 
(if i <= 2 /\ 1 <= i then if i = 1 then ts1 else  ts2  else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `
((( i <= 1) /\ ( 1 <= i )) <=> ( i = 1))`)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[(ARITH_RULE `
((( i <= 1) /\ ( 1 <= i )) <=> ( i = 1))`)] THEN
STRIP_TAC THEN cz_tac "c2" "ts3" "d2" "ts6" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f2:A^N->complex ts2.  ((f1) y) * ((ts2 % f2) x) * ((f3) z) = 
     (ts2) *  (f1 y * f2 x) * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE ` (1 + 2) + 1 = 4  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `4 <= dimindex (:N) ==>  (2 <= dimindex (:N) /\ 1 <= dimindex (:N)) `;ARITH]
THEN ONCE_SIMP_TAC[(tensor_1mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 3) ==> 1 <= i-3) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((4 <= dimindex (:N)) ==>(i <= 4 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N) /\ i - 3 <= dimindex (:N)) )) `] THEN
SIMP_TAC [ ARITH_RULE `(if i <= 4 /\ 1 <= i then if i <= 3 then if i = 1 then ts1
   else if i - 1 = 1 then  ts2  else ts3 else x4 else g i) = 
   (if i <= 4 /\ 1 <= i then if i = 1 then ts1
   else if i = 2 then ts2 else if i = 3 then ts3 else x4 else g i)`]
 THEN  ASM_SIMP_TAC[GSYM tensor_1mlem1d]  THEN
ASM_SIMP_TAC [ARITH_RULE `4 = 2 + 2 /\  1 <= 2  `;tensor_nmlem1;ARITH_RULE 
    `(4 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
    <=> (4 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((4 <= dimindex (:N)) ==>(i <= 2 ==> (i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_1mlem1d)] THEN   
SIMP_TAC [ ARITH_RULE `(1 <= i ==> ((i = 0) = F)) /\
(if i <= 2 /\ 1 <= i then if i = 1 then ts1
else if i = 2 then ts2 else if i = 3 then ts3 else x4 else g i) = 
(if i <= 2 /\ 1 <= i then if i = 1 then ts1 else  ts2  else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
STRIP_TAC THEN cnot2_tac "c1" "d2" "ts4" "ts5"  THEN 
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;
COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f2:A^N->complex ts2.   ((ts2 % f2) x) * ((f3) z) = 
     (ts2) *  f2 x * f3 z `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
 IMP_REWRITE_TAC[ARITH_RULE ` 2 + 2 = 4  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `4 <= dimindex (:N) ==>  (2 <= dimindex (:N)) `;ARITH]
THEN ONCE_SIMP_TAC[(tensor_1mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE `( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((4 <= dimindex (:N)) ==>(i <= 4 ==> (i <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
    /\ i - 1 <= dimindex (:N)) )) `] THEN
SIMP_TAC [ ARITH_RULE `(if i <= 4 /\ 1 <= i then if i <= 2 then if i = 1 then ts1 else ts2
   else if i - 2 = 1 then ts3 else x4 else g i) = 
   (if i <= 4 /\ 1 <= i then if i = 1 then ts1
   else if i = 2 then ts2 else if i = 3 then ts3 else x4 else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
ASM_SIMP_TAC [TS_outputs ] THEN ASM_SIMP_TAC [GSYM TS_outputs ] THEN
SIMP_TAC [ETA_AX;GSYM CX_MUL;REAL_MUL_RNEG; REAL_MUL_LNEG;
GSYM REAL_MUL_ASSOC;CFUN_SMUL_ASSOC;REAL_FIELD ` &1 / &4 * &1 / &4 * &1 / &4 = &1 / &64`];;



let TS_000 = prove(`!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (ts1) else if i = 2 then LH (ts2) else LH (ts3)):bqs^N) = Cx (&1 / &64) %
tensor 3 (lambda i. if i = 1 then LH (ts4) else if i = 2 then LH (ts5) else LH (ts6))`,TS_tactic);;


let TS_101 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (ts1) else if i = 2 then  LV (ts2) else
 LV (ts3)):bqs^N) = Cx (-- (&1 / &64)) %
 (tensor 3 (lambda i. if i = 1 then LH (ts4) else if i = 2
then  LV (ts5) else LV (ts6)))`,TS_tactic);;

let TS_010 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (ts1) else if i = 2 then  LH (ts2) else
LH (ts3) ):bqs^N) = Cx (&1 / &64) %
 (tensor 3 (lambda i. if i = 1 then LV (ts4) else if i = 2
then LH (ts5) else LH (ts6)))`,TS_tactic);;

let TS_011 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (ts1) else if i = 2 then  LV (ts2) else
LH (ts3)):bqs^N) = Cx (&1 / &64) %
 (tensor 3 (lambda i. if i = 1 then LV (ts4) else if i = 2
then LV (ts5) else LH (ts6)))`,TS_tactic);;

let TS_111 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (ts1) else if i = 2 then  LV (ts2) else
 LV (ts3)):bqs^N) = Cx ((&1 / &64)) %
 (tensor 3(lambda i. if i = 1 then LV (ts4) else if i = 2
then LV (ts5) else LV (ts6) ))`,TS_tactic);;

let TS_001 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (ts1) else if i = 2 then  LV (ts2) else
LH (ts3)):bqs^N) = Cx (&1 / &64) %
 (tensor 3 (lambda i. if i = 1 then LH (ts4) else if i = 2
then LV (ts5) else LH (ts6)))`,TS_tactic);;

let TS_100 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LH (ts1) else if i = 2 then  LH (ts2) else
LV (ts3)):bqs^N) = Cx (&1 / &64) %
 (tensor 3 (lambda i. if i = 1 then LH (ts4) else if i = 2
then LH (ts5) else LV (ts6)))`,TS_tactic);;

let TS_110 = prove( `!(ts1:sm) (ts2:sm) (ts3:sm) (ts4:sm) (ts5:sm) (ts6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
TS_GATE (ts1, ts2, ts3, ts4,ts5,ts6,ten, LH, LV, m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (ts1) else if i = 2 then  LH (ts2) else
 LV (ts3)):bqs^N) = Cx (&1 / &64) %
 (tensor 3 (lambda i. if i = 1 then LV (ts4) else if i = 2
then LH (ts5) else LV (ts6)))`,TS_tactic);;



let ts_tac ts1 ts2 ts3 ts4 ts5 ts6 = 
 SUBGOAL_TAC "ts_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_000))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_000] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_001))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_010))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_011))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_100))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_101)))))))))
[IMP_REWRITE_TAC [spec_thm_tac TS_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_110))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "ts_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ts1",ts1)
(SPEC_V ("ts2",ts2) (SPEC_V ("ts3",ts3) (SPEC_V("ts4",ts4) 
(SPEC_V ("ts5",ts5) (SPEC_V("ts6",ts6) TS_111))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac TS_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "ts_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "ts_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "ts_111" (fun thm-> ALL_TAC);;

