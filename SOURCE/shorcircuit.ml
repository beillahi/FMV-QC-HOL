(* ========================================================================= *)
(*                                                                           *)
(*                           shor_circuit.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "Flip_gate.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 




let shor_tactics = ASM_SIMP_TAC [ARITH_RULE `4 = ((1+1)+1) + 1 
/\  1 <= 1  `;tensor_nmlem1;ARITH_RULE 
	`(4 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN	
	CONV_TAC NUM_REDUCE_CONV THEN	
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
	<=> (4 <= dimindex (:N) /\  1 <= dimindex (:N))) `]	
THEN ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE 
` ( 1 <= i + 3) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
((4 <= dimindex (:N)) ==>(i <= 1 ==> (i + 3 <= dimindex (:N) 
/\ i + 2 <= dimindex (:N) /\ i + 1 <= dimindex (:N)) ))`] THEN	
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=>
 (if (j <= k) then  i = k - j else F)) ` ] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN	
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN	
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;
GSYM (ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[Hadamard_GATE;Hadamard_In_Output] THEN	
SIMP_TAC[GSYM Hadamard_GATE;GSYM Hadamard_In_Output] THEN
IMP_REWRITE_TAC[HADAMARD_0;HADAMARD_1] THEN
SIMP_TAC[Hadamard_GATE;Hadamard_In_Output] THEN
SIMP_TAC[MESON[EQ_SYM_EQ] `(a2$1 = b2$2 <=>  b2$2 = a2$1) /\ 
(c2$1 = d2$2 <=>  d2$2 = c2$1)` ]
THEN SIMP_TAC[GSYM Hadamard_GATE;GSYM Hadamard_In_Output] THEN
SIMP_TAC[GSYM (MESON[EQ_SYM_EQ] `(a2$1 = b2$2 <=>  b2$2 = a2$1) /\
 (c2$1 = d2$2 <=>  d2$2 = c2$1)` )]
THEN SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL;CFUN_ARITH `!f1:A^N->complex a1 a2 a3 a4. 
 ((a1 % f1) y) * ((a2 % f2) x) * ((a3 % f3) z) * (a4 % f4) t = 
(a1*a2*a3*a4) * f1 y * f2 x * f3 z * f4 t `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `;
CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
SIMP_TAC [COMPLEX_FIELD `(x:complex) * y * z* t = (((x*y)*z)*t)`] THEN 
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 2 + 1 = 3 /\ 3 + 1 = 4 `;
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(4 <= dimindex (:N) ==>  (2 <= dimindex (:N)
 /\ 3 <= dimindex (:N))) `;ARITH] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `(~( i <= 3) ==> 1 <= i-3) /\
  (~( i <= 2) ==> 1 <= i-2) /\ (~( i <= 1) ==> 1 <= i-1) /\ 
((4 <= dimindex (:N)) ==>(i <= 4 ==> (i <= dimindex (:N) 
/\ i - 3 <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
/\ i - 1 <= dimindex (:N) ) ))`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
ASM_SIMP_TAC [ARITH_RULE `4 = 2 + 2 /\  1 <= 2  `;
tensor_nmlem1;ARITH_RULE 
`(4 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
	<=> (4 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN	
ONCE_SIMP_TAC[(tensor_1mlem1d)]	 THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i+2)  /\
	((4 <= dimindex (:N)) ==>(i <= 2 ==> 
(i + 2 <= dimindex (:N)) ))`] THEN
REWRITE_TAC [ ARITH_RULE `(((i:num) + j <= k) <=> 
(if (j <= k) then  i <= k - j else F)) ` ] THEN
CONV_TAC NUM_REDUCE_CONV THEN
 REWRITE_TAC [ARITH_RULE `
(if (i <= 2 /\ 1 <= i)  then if i <= 3 then if i <= 1 
then x1 else x2 else x3 else g i) =
(if (i <= 2 /\ 1 <= i) then if i = 1 then x1 else x2 else g i) /\ 
(if (i <= 2 /\ 1 <= i)  then if i <= 1 then if i <= 0 
then x1 else x2 else x3 else g i) =
(if (i <= 2 /\ 1 <= i) then if i = 1 then x2 else x3 else g i)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
IMP_REWRITE_TAC[IS_CZ_G;CZ_INPUTS] THEN 
SIMP_TAC[GSYM CZ_INPUTS] THEN
IMP_REWRITE_TAC[CZ_00;CZ_11;CZ_10;CZ_01] THEN 
IMP_REWRITE_TAC[CZ_OUTPUTS] THEN 
SIMP_TAC[GSYM CZ_OUTPUTS] THEN
SIMP_TAC [GSYM CX_MUL;
CFUN_ARITH `!f1:A^N->complex a1 a2.  ((a1 % f1) y) * ((a2 % f2) x) = 
(a1*a2) * f1 y * f2 x `] THEN SIMP_TAC [CFUN_ARITH 
`!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`] 
THEN ASM_SIMP_TAC [ARITH_RULE `2 = 1 + 1 /\  1 <= 1`;
tensor_nmlem1;ARITH_RULE 
`(2 <= dimindex (:N) ==>  1 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN	
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(4 <= dimindex (:N) 
<=> (4 <= dimindex (:N) /\  1 <= dimindex (:N))) `] THEN	
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE 
`( 1 <= i + 1) /\ ((4 <= dimindex (:N)) 
==>(i <= 1 ==> ( i + 1 <= dimindex (:N)) ))`] THEN	
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> 
(if (j <= k) then  i = k - j else F)) ` ] THEN
	CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ONCE_SIMP_TAC[(ISPECL [`1`] tensor_1mlem1d)] THEN	
 SIMP_TAC[(ARITH_RULE `(( i <= 1) /\ ( 1 <= i )) 
 <=> ( i = 1)`)] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d;
GSYM (ARITH_RULE `(( i <= 1) /\ 
( 1 <= i )) <=> ( i = 1)`)] THEN
SIMP_TAC[Hadamard_GATE;Hadamard_In_Output] THEN	
SIMP_TAC[GSYM Hadamard_GATE;
GSYM Hadamard_In_Output] THEN
IMP_REWRITE_TAC[HADAMARD_0;HADAMARD_1] THEN
SIMP_TAC[Hadamard_GATE;Hadamard_In_Output] THEN
SIMP_TAC[GSYM Hadamard_GATE;
GSYM Hadamard_In_Output] THEN
SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;
COMPLEX_SUB_LDISTRIB] THEN
SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
SIMP_TAC [GSYM CX_MUL; CFUN_ARITH `!f1:A^N->complex .
        (( f1) y) * ((f2) x) * ((f3) z) * (f4) t = 
	 (f1 y * f2 x) * (f3 z * f4 t) `] THEN
SIMP_TAC [GSYM CX_MUL; CFUN_ARITH `!f1:A^N->complex a1 a2.  
(((a1 % f1) y) * ((f2) x)) * (((a2 % f3) z) * (f4) t) = 
	 (a1*a2) * ((f1 y * f2 x) * (f3 z * f4 t))`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = 
a % (\y. f1 y)  `;
CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 + 1 = 2 /\ 2 + 2 = 4  `;
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;
ARITH_RULE `(4 <= dimindex (:N) ==>  (2 <= dimindex (:N))) `;ARITH] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ONCE_SIMP_TAC[(tensor_1mlem1d);ETA_AX] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` (~( i -2 <= 1) ==> 1 <= i-2-1) /\ 
   (~( i <= 2) ==> 1 <= i-2) /\ (~( i <= 1) ==> 1 <= i-1) /\
((4 <= dimindex (:N)) ==>(i <= 4 ==> (i <= dimindex (:N)  /\
 i - 2 - 1 <= dimindex (:N) /\ i - 2 <= dimindex (:N) 
/\ i - 1 <= dimindex (:N) ) ))`] THEN
ASM_SIMP_TAC [ARITH_RULE `(if (i <= 4 /\ 1 <= i) 
then if i <= 2 then if i <= 1 then x1 else x2
else if i - 2 <= 1 then x3 else x4 else x5) =
(if (i <= 4 /\ 1 <= i) then if  i = 1 then x1 else if i = 2 then
x2 else if i = 3 then x3 else x4 else x5)`] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;
CFUN_ADD_ASSOC;CFUN_ADD_SYM;CFUN_ADD_LID;CFUN_ADD_RID;
CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;CFUN_ADD_LDISTRIB;
CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun) (k:cfun). 
 b%f +   b%d  + b%k  + b%a + c%f +   c%d  + c%k  + c%a =
 (b+c) % f + (b+c) % d + (b+c) % a
 + (b+c) % k`;GSYM CX_ADD;CFUN_ADD_AC;CFUN_SMUL_DISTRIB;
GSYM CX_MUL; GSYM CX_SUB;CFUN_ADD_SYM;
CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun) (k:cfun). 
  b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a
 /\ b%a +  f  + c%a + k = k + f +  (b+c) % a /\
  b%a +  f  + c%a = f +  (b+c) % a 
/\  k + b%a +  f  + c%a = k + f +  (b+c) % a /\
 b%a + k + f  + c%a = k + f +  (b+c) % a /\
b%a + k1 + k2+ k + f1 + f + d + c%a + d1 = 
f + f1 + d + k+  k1 + k2 +d1 + (b+c) % a /\ 
b%a +  k + f + d + d1 + c%a  = f  + d + k+  d1 + (b+c) % a /\
  k1 + b%a + k + f + d + c%a + d1 = f + d + k+ k1 + d1 + (b+c) % a`;
GSYM CX_ADD;CFUN_ADD_AC;CFUN_SUB_AC;CFUN_SMUL_LZERO;
REAL_FIELD `&1 / &2 * &1 / &2 * &1 / &2 * &1 / &4 pow 2 = &1 / &128 
/\ &1 / &2 * &1 / &2 pow 2 * &1 / &4 pow 2 = &1 / &128`;REAL_ADD_AC;
REAL_SUB_REFL;GSYM CX_MUL; GSYM CX_ADD; GSYM CX_SUB;REAL_NEG_NEG;
GSYM CX_NEG;REAL_ADD_LINV; 
REAL_FIELD ` &1 / &128 + &1 / &128 + &1 / &128 + &1 / &128 = &1 / &32 /\
&1 / &128 + &1 / &128 + --(&1 / &128) - (&1 / &128) = &0  `;
REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;REAL_ADD_AC;GSYM CX_MUL; 
GSYM CX_ADD; GSYM CX_SUB;GSYM CX_INV;
CFUN_ADD_AC;SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;
SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;
REAL_MUL_RNEG;CFUN_SMUL_LZERO;GSYM CX_ADD;
REAL_MUL_RID;GSYM CFUN_ADD_RDISTRIB;
CFUN_ADD_LID;REAL_FIELD `inv (sqrt (&2)) = &1 / sqrt (&2)  `;
REAL_ADD_LINV;REAL_MUL_LZERO;REAL_DIV_RMUL;
REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;REAL_SUB_RZERO;
REAL_SUB_REFL;REAL_NEG_NEG;REAL_MUL_LNEG;
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0] 
 ` ((&1 / sqrt (&2)) * sqrt (&2) = &1) `];;





let shor_circuit = prove( `!(x1:sm^N) (f1:sm^N) x2 (f2:sm^N) 
a2 b2 c2 d2 p1 q1 j1 p2 q2 j2 l1 l2 
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
Hadamard_GATE ((x1:sm^N), (a2:sm^N), ten) /\
Hadamard_GATE ((f1:sm^N), (b2:sm^N), ten) /\ a2$1 = b2$2 /\
Hadamard_GATE ((x2:sm^N), (c2:sm^N), ten) /\
Hadamard_GATE ((f2:sm^N), (d2:sm^N), ten) /\ c2$1 = d2$2 /\ 
IS_CZ_G ((b2:sm^N), (p1:sm^N), (q1:sm^N), 
(j1:sm^N),ten, m_modes_pro) /\
IS_CZ_G ((d2:sm^N), (p2:sm^N), (q2:sm^N), 
(j2:sm^N),ten,m_modes_pro) /\
Hadamard_GATE ((j1:sm^N), (l1:sm^N), ten) /\
Hadamard_GATE ((j2:sm^N), (l2:sm^N), ten)  ==>
tensor 4 ((lambda i. if i = 3 then fock (f2$1) 1 
else if i = 2 then  vac (x1$1) else
if i = 1 then  vac (f1$1) else vac (x2$1)):bqs^N) = 
Cx (&1 / &32) % tensor 4 (lambda i. if i = 1 
then vac (l1$1) else if i = 2
then vac (j1$2) else if i = 3 then vac (l2$1) 
else fock (j2$2) 1) +
Cx (&1 / &32) % tensor 4 (lambda i. if i = 1 
then vac (l1$1) else if i = 2
then vac (j1$2) else if i = 3 then fock (l2$1) 1
else vac (j2$2)) +
Cx (&1 / &32) % tensor 4 (lambda i. if i = 1 
then fock (l1$1) 1 else if i = 2
then fock (j1$2) 1 else if i = 3 then vac (l2$1) 
else fock (j2$2) 1) +
Cx (&1 / &32) % tensor 4 (lambda i. if i = 1 then 
fock (l1$1) 1 else if i = 2
then fock (j1$2) 1 else if i = 3 then fock (l2$1) 1 
else vac (j2$2))`,shor_tactics);;