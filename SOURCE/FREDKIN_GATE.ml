(* ========================================================================= *)
(*                                                                           *)
(*                          FREDKIN_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2017                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "TOFFOLI_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*24 optical qubits *)
(*5 CZ gates *)
(*------------------**********************-------------*) 

let FREDKIN3_GATE = define 
`FREDKIN3_GATE ((x1:sm), (x2:sm), (x3:sm), (y1:sm), (y2:sm), (y3:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex))) <=> 
(? (c1:sm) (c2:sm) (d1:sm) (d2:sm).
CNOT2_GATE (x1,x2, c1,c2,ten, LH, LV ,m_modes_pro) /\
TOFFOLI1_GATE (c1,c2,x3,d1,d2,y3,ten,LH, LV,m_modes_pro) /\
CNOT2_GATE (d1,d2,y1,y2,ten, LH, LV ,m_modes_pro))` ;;

let FREDKIN1_GATE = define 
`FREDKIN1_GATE ((x1:sm), (x2:sm), (x3:sm), (y1:sm), (y2:sm), (y3:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex))) <=> 
(? (c2:sm) (c3:sm) (d2:sm) (d3:sm).
CNOT1_GATE (x2,x3, c2,c3,ten, LH, LV ,m_modes_pro) /\
TOFFOLI3_GATE (x1,c2,c3,y1,d2,d3,ten,LH, LV,m_modes_pro) /\
CNOT1_GATE (d2,d3, y2,y3,ten, LH, LV ,m_modes_pro))` ;;



let FREDKIN3_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
FREDKIN3_GATE] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `3 = (2+1) /\ 1 <= 1`;tensor_nmlem1;ARITH_RULE 
`(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN CONV_TAC NUM_REDUCE_CONV 
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> 
(8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\  1 <= dimindex (:N) /\ 2 <= dimindex (:N)))`] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d);(ISPECL [`2`] tensor_1mlem1d)] 
THEN SIMP_TAC [ ARITH_RULE `(if i <= 2 /\ 1 <= i then if i = 1 then fd1
else if i = 2 then fd2 else fd3 else g i) = (if i <= 2 /\ 1 <= i then 
if i = 1 then fd1 else  fd2  else g i)`] THEN ASM_SIMP_TAC [LAMBDA_BETA;
ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) /\ 
i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then 
i = k - j else F))`] THEN CONV_TAC NUM_REDUCE_CONV THEN 
SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d;
GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[ARITH_RULE `((i <= 1) /\ (1 <= i)) <=> (i = 1)`] THEN
STRIP_TAC THEN cnot2_tac "fd1" "fd2" "c1" "c2" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex fd2. ((fd2 % f1) y) * ((f2) x) = 
(fd2) * (f1 y * f2 x) /\ ((f1) y) * ((fd2 % f2) x) = (fd2) * (f1 y * f2 x)`] 
THEN SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = 
a % (\y. f1 y)`;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN 
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> 
(8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
IMP_REWRITE_TAC[ARITH_RULE `2 + 1 = 3`;
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX;] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE 
`( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ 
(( i + 1 <= 1) <=> i <= 0 ) /\(~( i <= 1) ==> 1 <= i-1) /\ 
(~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) 
/\ ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ 
i - 1 <= dimindex (:N) /\ i - 2 <= dimindex (:N)) ))`] THEN
SIMP_TAC [ ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2 then 
if i = 1 then fd1 else fd2 else fd3 else g i) = (if i <= 3 /\ 1 <= i
then if i = 1 then fd1 else if i = 2 then  fd2 else fd3 else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
STRIP_TAC THEN toffoli1_tac "c1" "c2" "fd3" "d1" "d2" "fd6" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;ARITH_RULE 
`3 = (2+1)/\1 <= 1`;tensor_nmlem1;ARITH_RULE 
`(8 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> 
(8 <= dimindex (:N) /\ 1 <= dimindex (:N)/\ 2 <= dimindex (:N)))`] 
THEN ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d);
(ISPECL [`2`] tensor_1mlem1d)] THEN SIMP_TAC [ARITH_RULE 
`(if i <= 2 /\ 1 <= i then if i = 1 then fd1 else if i = 2 then fd2 else fd3 else g i)= 
(if i <= 2 /\ 1 <= i then if i = 1 then fd1 else  fd2  else g i)`] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ 
( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
/\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> 
(if (j <= k) then  i = k - j else F))`] THEN
CONV_TAC NUM_REDUCE_CONV THEN   
SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE 
`(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[(ARITH_RULE `((i <= 1) /\ (1 <= i)) <=> (i = 1)`)] THEN 
STRIP_TAC THEN cnot2_tac "d1" "d2"  "fd4" "fd5" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex fd2.  ((fd2 % f1) y) * ((f2) x) = 
(fd2) * (f1 y * f2 x) /\ (( f1) y) * ((fd2 % f2) x) = 
(fd2) * (f1 y * f2 x)`] THEN SIMP_TAC [CFUN_ARITH 
`!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`;
CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN 

ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> 
(8 <= dimindex (:N) /\  3 <= dimindex (:N)))`] THEN
IMP_REWRITE_TAC[ARITH_RULE ` 2 + 1 = 3 `;
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX;] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE 
`( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ 
(( i + 1 <= 1) <=> i <= 0 ) /\ (~( i <= 1) ==> 1 <= i-1) /\ 
(~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N) /\ 
i - 1 <= dimindex (:N) /\ i - 2 <= dimindex (:N)) )) `] THEN
SIMP_TAC [ARITH_RULE `(if i <= 3 /\ 1 <= i then if i <= 2 then 
if i = 1 then fd1 else fd2 else fd3 else g i)= (if i <= 3 /\ 1 <= i
then if i = 1 then fd1 else if i = 2 then  fd2 else fd3 else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[CFUN_SMUL_DISTRIB;GSYM CX_MUL;
REAL_FIELD `(&1 / &4 * &1 / &64) * &1 / &4 = &1 / &1024`];;


    
    

let FREDKIN1_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;FREDKIN1_GATE] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `3 = (1+2)/\  1 <= 2  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\ 4 <= dimindex (:N)  /\  1 <= dimindex (:N)/\ 2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d);(ISPECL [`2`] tensor_1mlem1d)] THEN
SIMP_TAC [ ARITH_RULE 
`(if i <= 2 /\ 1 <= i then if i = 1 then fd1
else if i = 2 then fd2 else fd3  else g i )= 
(if i <= 2 /\ 1 <= i then if i = 1 then fd1
else  fd2  else g i)`] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN    
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
SIMP_TAC[MESON[ARITH]`
(if i <= 2 /\ 1 <= i then if i = 0 then x  else if i = 1 then y else z else g ) = 
( if i <= 2 /\ 1 <= i then if i = 1 then y else z else g)  `] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
STRIP_TAC THEN cnot1_tac "fd2" "fd3" "c2" "c3" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex fd2.  ((fd2 % f1) y) * ((f2) x)  =  (fd2) * (f1 y * f2 x)  /\ 
(( f1) y) * ((fd2 % f2) x)  =  (fd2) * (f1 y * f2 x)`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] 
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
IMP_REWRITE_TAC[ARITH_RULE ` 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX;] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE ` ( i - 1 = 1 <=> i = 2 ) /\ ( i - 1 - 1 = i -2) /\ 
(( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ 
 (1 <= i ==> ((i <= 1) <=> i = 1)) /\
  ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N) /\ i - 2 <= dimindex (:N)) )) `] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
STRIP_TAC THEN toffoli3_tac "fd1" "c2" "c3" "fd4" "d2" "d3" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;ARITH_RULE `3 = (1+2)/\  1 <= 2  `;tensor_nmlem1;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  1 <= dimindex (:N)/\ 2 <= dimindex (:N))) `] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d);(ISPECL [`2`] tensor_1mlem1d)] THEN
SIMP_TAC [ ARITH_RULE 
`(if i <= 2 /\ 1 <= i then if i = 1 then fd1
else if i = 2 then fd2 else fd3  else g i )= 
(if i <= 2 /\ 1 <= i then if i = 1 then fd1
else  fd2  else g i)`] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
    ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 3 <= dimindex (:N) 
    /\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN
    REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) ` ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN   
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
SIMP_TAC[MESON[ARITH]`
(if i <= 2 /\ 1 <= i then if i = 0 then x  else if i = 1 then y else z else g ) = 
( if i <= 2 /\ 1 <= i then if i = 1 then y else z else g)  `] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
STRIP_TAC THEN cnot1_tac "d2" "d3" "fd5" "fd6" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex fd2.  ((fd2 % f1) y) * ((f2) x)  =  (fd2) * (f1 y * f2 x)  /\ 
(( f1) y) * ((fd2 % f2) x)  =  (fd2) * (f1 y * f2 x)`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] 
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
IMP_REWRITE_TAC[ARITH_RULE ` 1 + 2 = 3  `;REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_ASM_SIMP_TAC[(tensor_1mlem1d);ETA_AX;] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH;ARITH_RULE ` ( i - 1 = 1 <=> i = 2 ) /\ 
( i - 1 - 1 = i -2) /\ (( i - 1 <= 1) <=> i <= 2 ) /\ (( i + 1 <= 1) <=> i <= 0 ) /\
 (~( i <= 1) ==> 1 <= i-1) /\ (~( i <= 2) ==> 1 <= i-2) /\ (1 <= i ==> ((i <= 1) <=> i = 1)) /\
    ((8 <= dimindex (:N)) ==>(i <= 3 ==> (i <= dimindex (:N)  
    /\ i - 1 <= dimindex (:N) /\ i - 2 <= dimindex (:N)) )) `] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[CFUN_SMUL_DISTRIB;GSYM CX_MUL;
REAL_FIELD `(&1 / &4 * &1 / &64) * &1 / &4 = &1 / &1024`];;



let FREDKIN3_000 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LH (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LH (fd5) else LH (fd6)):bqs^N)`,FREDKIN3_tactic);;



let FREDKIN3_001 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LH (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LH (fd5) else LV (fd6)):bqs^N)`,FREDKIN3_tactic);;


let FREDKIN3_010 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LV (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LV (fd5) else LH (fd6)):bqs^N)`,FREDKIN3_tactic);;

let FREDKIN3_011 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LV (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LH (fd5) else LV (fd6)):bqs^N)`,FREDKIN3_tactic);;

let FREDKIN3_100 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LH (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LH (fd5) else LH (fd6)):bqs^N)`,FREDKIN3_tactic);;

let FREDKIN3_101 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LH (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LV (fd5) else LV (fd6)):bqs^N)`,FREDKIN3_tactic);;


let FREDKIN3_110 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LV (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LV (fd5) else LH (fd6)):bqs^N)`,FREDKIN3_tactic);;

let FREDKIN3_111 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN3_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LV (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LV (fd5) else LV (fd6)):bqs^N)`,FREDKIN3_tactic);;

 
 
let fredkin3_tac fd1 fd2 fd3 fd4 fd5 fd6 = 
 SUBGOAL_TAC "FREDKIN3_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_000))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_000] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_001))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_010))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_011))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_100))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_101)))))))))
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_110))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN3_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN3_111))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN3_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "FREDKIN3_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "FREDKIN3_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN3_111" (fun thm-> ALL_TAC);;




let FREDKIN1_000 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LH (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LH (fd5) else LH (fd6)):bqs^N)`,FREDKIN1_tactic);;



let FREDKIN1_001 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LH (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LH (fd5) else LV (fd6)):bqs^N)`,FREDKIN1_tactic);;


let FREDKIN1_010 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LV (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LV (fd5) else LH (fd6)):bqs^N)`,FREDKIN1_tactic);;

let FREDKIN1_011 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LH (fd1) else if i = 2 then LV (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LH (fd4) else if i = 2 then LV (fd5) else LV (fd6)):bqs^N)`,FREDKIN1_tactic);;

let FREDKIN1_100 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LH (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LH (fd5) else LH (fd6)):bqs^N)`,FREDKIN1_tactic);;

let FREDKIN1_101 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LH (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LV (fd5) else LH (fd6)):bqs^N)`,FREDKIN1_tactic);;


let FREDKIN1_110 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LV (fd2) else LH (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LH (fd5) else LV (fd6)):bqs^N)`,FREDKIN1_tactic);;

let FREDKIN1_111 = prove(`!(fd1:sm) (fd2:sm) (fd3:sm) (fd4:sm) (fd5:sm) (fd6:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
FREDKIN1_GATE (fd1,fd2,fd3,fd4,fd5,fd6,ten,LH,LV,m_modes_pro)
 ==>
tensor 3 ((lambda i. if i = 1 then LV (fd1) else if i = 2 then LV (fd2) else LV (fd3)):bqs^N) = Cx (&1 / &1024) %
 tensor 3 ((lambda i. if i = 1 then LV (fd4) else if i = 2 then LV (fd5) else LV (fd6)):bqs^N)`,FREDKIN1_tactic);;
 

 
 let fredkin1_tac fd1 fd2 fd3 fd4 fd5 fd6 = 
 SUBGOAL_TAC "FREDKIN1_000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_000))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_000] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_001))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_010))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_011))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_100))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_101)))))))))
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_110))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "FREDKIN1_111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fd1",fd1)
(SPEC_V ("fd2",fd2) (SPEC_V ("fd3",fd3) (SPEC_V("fd4",fd4) 
(SPEC_V ("fd5",fd5) (SPEC_V("fd6",fd6) FREDKIN1_111))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac FREDKIN1_111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "FREDKIN1_000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "FREDKIN1_100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "FREDKIN1_111" (fun thm-> ALL_TAC);;