(* ========================================================================= *)
(*                                                                           *)
(*                           NS_gate_2_proj.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "NS_gate_1_proj.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 

(****************************************************************************)
(* All the possible outputs for an input of 2-qubits feds to NS             *)
(****************************************************************************)


let NS_2_TAC=
REWRITE_TAC[is_beam_splitter;pos;is_ns_gate] THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN MULTI_MODE_DECOMPOSE_TAC
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO] THEN
SIMP_TAC[GSYM ONE; GSYM TWO] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) =
(if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN
CONV_TAC(LAND_CONV(REWRITE_CONV [COP_ARITH 
`inv (Cx (sqrt (&2))) % (cr (a$i1) ** cr (a$i1)) = 
(inv (Cx (sqrt (&2))) % I) ** (cr (a$i1) ** cr (a$i1))`]))
THEN SIMP_TAC [GSYM NS_lem] THEN
REWRITE_TAC [COP_ARITH `(f ** f1 ** f2) x = f (f1 (f2 x))`] 
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[keylem;ARITH;COND_ID] THEN
FIRST_ASSUM(fun th -> REWRITE_TAC[(MATCH_MP 
(GSYM COP_TENSOR_CFUN) th)]) 
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[keylem;ARITH;COND_ID] THEN
FIRST_ASSUM(fun th -> REWRITE_TAC[(MATCH_MP 
(GSYM COP_TENSOR_CFUN) th)])
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[keylem;ARITH;COND_ID] THEN
FIRST_ASSUM(fun th -> REWRITE_TAC[(MATCH_MP 
(GSYM COP_TENSOR_CFUN) th)])
THEN ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;
GSYM COP_MUL_THM] THEN IMP_REWRITE_TAC[LINCOP_ADD_MUL_LDISTRIB;
LINCOP_MUL_RMUL;COP_ADD_MUL_RDISTRIB] THEN
ASM_SIMP_TAC[CNJ_MUL;COP_ADD_LDISTRIB;COP_SMUL_ASSOC;
COP_MUL_LSMUL;GSYM CX_MUL;COP_TENSOR_LINEAR;SMUL_LINCOP;
ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN
REWRITE_TAC[REAL_MUL_RNEG;REAL_MUL_LNEG; REAL_NEG_NEG;
CX_NEG;COMPLEX_MUL_ASSOC] THEN IMP_REWRITE_TAC[GSYM SQRT_MUL] 
THEN REPEAT STRIP_TAC THEN (REAL_ARITH_TAC ORELSE ALL_TAC) 
THEN REWRITE_TAC[real_div;GSYM REAL_MUL_ASSOC;REAL_MUL_RID;
REAL_MUL_LID;GSYM REAL_INV_MUL;REAL_OF_NUM_MUL;ARITH;
COP_ADD_ASSOC] THEN CFUN_FLATTEN_TAC THEN 
REWRITE_TAC[GSYM pos;GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!(a:complex) b c. a*b+a*c+d = (a*b+a*c)+d `;
GSYM complex_sub;COMPLEX_SUB_REFL;
COMPLEX_MUL_RZERO;COMPLEX_ADD_LID]
THEN ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_4_3;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM;
ARITH_RULE `~(2=1)`] ` is_tensor ten ==> 
pos ten (cr (d$2)) 2 (pos ten (inv (Cx (sqrt (&2))) % I) 1 
(pos ten op1 m1 (pos ten op2 m2 
(tensor 3 (lambda j. vac (d$3)))))) = 
pos ten (inv (Cx (sqrt (&2))) % I) 1 (pos ten (cr (d$2)) 2 
(pos ten op1 m1 (pos ten op2 m2 
(tensor 3 (lambda j. vac (d$3)))))) `)]
THEN ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_4_3;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM;
ARITH_RULE `~(3=1)`] ` is_tensor ten ==> 
pos ten (cr (d$3)) 3  (pos ten (inv (Cx (sqrt (&2))) % I) 1 
(pos ten op1 m1 (pos ten op2 m2 
(tensor 3 (lambda j. vac (d$3)))))) = 
pos ten (inv (Cx (sqrt (&2))) % I) 1 
(pos ten (cr (d$3)) 3 (pos ten op1 m1 
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) `)] THEN
ASM_SIMP_TAC [MESON[POS_ASSOC;GSYM COP_MUL_THM;
ARITH_RULE `~(3=1)`] ` is_tensor ten ==> pos ten (cr (d$3)) 3
(pos ten (cr (d$1)) 1 (tensor 3 (lambda j. vac (d$3)))) =  
pos ten (cr (d$1)) 1 (pos ten (cr (d$3)) 3 
(tensor 3 (lambda j. vac (d$3))))`] 
THEN ASM_SIMP_TAC [MESON [POS_ASSOC;GSYM COP_MUL_THM;
ARITH_RULE `~(2=1)`] ` is_tensor ten ==>  
pos ten (cr (d$2)) 2 (pos ten (cr (d$1)) 1 
(tensor 3 (lambda j. vac (d$3))))  =  pos ten (cr (d$1)) 1
(pos ten (cr (d$2)) 2 (tensor 3 (lambda j. vac (d$3))))`] THEN 
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_3_2;COP_MUL_RDISTRIB ;
GSYM COP_MUL_THM;ARITH_RULE `~(2=1)`] ` is_tensor ten ==> 
pos ten op1 m1  (pos ten (cr (d$2)) 2 (pos ten (cr (d$1)) 1 
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) = 
pos ten op1 m1 (pos ten (cr (d$1)) 1 (pos ten (cr (d$2)) 2 
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) `)] THEN    
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_3_2;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM;
ARITH_RULE `~(3=1)`]` is_tensor ten ==> 
pos ten op1 m1 (pos ten (cr (d$3)) 3 (pos ten (cr (d$1)) 1
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) = 
pos ten op1 m1 (pos ten (cr (d$1)) 1 (pos ten (cr (d$3)) 3
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) `)] THEN  
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_3_2;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM;
ARITH_RULE `~(2=3)`] ` is_tensor ten ==> 
pos ten op1 m1 (pos ten (cr (d$3)) 3 (pos ten (cr (d$2)) 2
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) = 
pos ten op1 m1 (pos ten (cr (d$2)) 2 (pos ten (cr (d$3)) 3
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) `)] THEN  
ASM_SIMP_TAC [MESON[POS_ASSOC;GSYM COP_MUL_THM;
ARITH_RULE `~(3=2)`] ` is_tensor ten ==> pos ten (cr (d$3)) 3 
(pos ten (cr (d$2)) 2 (tensor 3 (lambda j. vac (d$3)))) =  
pos ten (cr (d$2)) 2 (pos ten (cr (d$3)) 3 
(tensor 3 (lambda j. vac (d$3))))  `] THEN
ASM_SIMP_TAC [MESON[POS_ASSOC;GSYM COP_MUL_THM;
ARITH_RULE `~(3=1)`] ` is_tensor ten ==> pos ten (cr (d$3)) 3
(pos ten (cr (d$1)) 1 (tensor 3 (lambda j. vac (d$3)))) = 
 pos ten (cr (d$1)) 1 (pos ten (cr (d$3)) 3 
(tensor 3 (lambda j. vac (d$3))))`] THEN
ASM_SIMP_TAC [MESON [POS_ASSOC;GSYM COP_MUL_THM;
ARITH_RULE `~(2=1)`] ` is_tensor ten ==>  pos ten (cr (d$2)) 2
(pos ten (cr (d$1)) 1 (tensor 3 (lambda j. vac (d$3))))  =  
pos ten (cr (d$1)) 1 (pos ten (cr (d$2)) 2 
(tensor 3 (lambda j. vac (d$3))))`] THEN
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_3_2;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM;
ARITH_RULE `~(2=3)`] ` is_tensor ten ==> 
pos ten op1 m1  (pos ten (cr (d$3)) 3 (pos ten (cr (d$2)) 2
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) = 
pos ten op1 m1 (pos ten (cr (d$2)) 2 (pos ten (cr (d$3)) 3
(pos ten op2 m2 (tensor 3 (lambda j. vac (d$3)))))) `)] THEN
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_1_1;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM] 
`is_tensor ten ==> pos ten op1 1  (pos ten op2 1 (pos ten op3 m3
(pos ten op4 m4 (tensor 3 (lambda j. vac (d$3)))))) = 
pos ten (op1 ** op2) 1 (pos ten op3 m3
(pos ten op4 m4 (tensor 3 (lambda j. vac (d$3))))) `)] THEN 
ASM_SIMP_TAC [ REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[POS_ASSOC_1_11;COP_MUL_RDISTRIB ;GSYM COP_MUL_THM] 
` is_tensor ten ==> pos ten op1 1  (pos ten op2 1 (pos ten op3 m3
(tensor 3 (lambda j. vac (d$3))))) = pos ten (op1 ** op2) 1 
(pos ten op3 m3 (tensor 3 (lambda j. vac (d$3))))`)] THEN
SIMP_TAC [COP_MUL_RDISTRIB;COP_MUL_LSMUL;COP_MUL_RID;COP_MUL_LID] 
THEN ASM_SIMP_TAC [A_HERM_A_LINEAR;LINCOP_MUL_RSMUL] THEN
SIMP_TAC [COP_MUL_RDISTRIB;COP_MUL_LSMUL;COP_MUL_RID;COP_MUL_LID] 
THEN SIMP_TAC [ COMPLEX_FIELD ` Cx (x) * y = y * Cx(x) /\ 
--Cx (x) * y = y * --Cx(x)`] THEN SIMP_TAC [COMPLEX_ADD_RDISTRIB;
GSYM COMPLEX_MUL_ASSOC;GSYM COMPLEX_ADD_ASSOC] THEN 
REWRITE_TAC [pos] THEN REPEAT STRIP_TAC THEN 
(REAL_ARITH_TAC ORELSE ALL_TAC) THEN REWRITE_TAC[real_div;
GSYM REAL_MUL_ASSOC;REAL_MUL_RID;REAL_MUL_LID;GSYM REAL_INV_MUL;
REAL_OF_NUM_MUL;ARITH;REAL_FIELD`inv (&2) * &2 * x= x /\ 
&2 * inv (&2) * x = x /\  &2 * inv (&6) = inv(&3) /\ 
inv(&3) * &2 * inv (&3) = &2 * inv(&9)`;COP_ADD_ASSOC] THEN 
CFUN_FLATTEN_TAC THEN REWRITE_TAC[GSYM pos;
GSYM COMPLEX_ADD_LDISTRIB; COMPLEX_FIELD 
`!(a:complex) b c. a*b+a*c+d = (a*b+a*c)+d `;GSYM complex_sub;
COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID] THEN 
SIMP_TAC[GSYM CX_NEG;GSYM CX_ADD;GSYM CX_SUB;GSYM CX_MUL] 
THEN SIMP_TAC[SQRT_MUL;SQRT_INV] THEN SIMP_TAC [REAL_FIELD 
` ((a:real)* inv b *a* inv b) * c* inv b *c* inv b+
(inv b *a* inv b)* c* inv b *c* inv b = (a + &1) * a * 
c pow 2 / (b pow 2) pow 2 /\ (((a* inv b *a* inv b)*
(c* inv b) *c*a* inv b + (inv b *a* inv b)*(c* inv b) *c*a* inv b)
+(a* inv b *a* inv b)*c*a* inv b *c* inv b + 
 (inv b *a* inv b)*c*a* inv b *c* inv b) + 
 (c* inv b *c* inv b) *
 (inv b *a*a* inv b - a * inv b * inv b)
 = (&2 * a pow 2 + &3 * a - &1)*
 a* c pow 2 / (b pow 2) pow 2 /\
 (((a* inv b *a* inv b) *c*a* inv b *c*a* inv b + 
 (inv b *a* inv b) *c*a* inv b *c*a* inv b) + 
 ((c * inv b) *c*a* inv b) * 
 (inv b *a*a* inv b - a* inv b * inv b)) +
 (c*a* inv b * c* inv b) * 
 (inv b * a * a * inv b - a * inv b * inv b)
 = (a pow 2 + &3  * a  - &2) * 
 c pow 2 * a pow 2 / (b pow 2) pow 2 /\
 (c*a* inv b *c*a* inv b)*
 (inv b *a*a* inv b - a* inv b * inv b) 
 = (a - &1) * a * a pow 2 * c pow 2 / (b pow 2) pow 2 /\
 (((a* inv b *a* inv b) * --(a*c* inv b) + 
 (inv b *a* inv b) * --(a*c* inv b)) + 
(a* inv b *a* inv b) * --((c* inv b) *a) + 
(inv b *a* inv b) * --((c* inv b) *a))  + 
(inv b * c)*c* inv b *c* inv b = 
(c pow 2 - &2 * (a + &1)* a pow 2)*c / (b * b pow 2) /\ 
(((a* inv b *a* inv b) * 
--(a*c*a* inv b) + (inv b *a* inv b) * --(a*c*a* inv b)) + 
(a* inv b *a* inv b) * --(c*a* inv b *a) + 
(inv b *a* inv b) * --(c*a* inv b *a)) +
 (((c* inv b) *c*a* inv b)* inv b *c + 
(c*a* inv b *c* inv b)* inv b *c)+ --(a*c* inv b)*
(inv b *a*a* inv b - a * inv b * inv b) + --((c* inv b) *a)*
(inv b *a*a* inv b - a* inv b * inv b) = 
(-- &2 * a * a pow 2 - &4 * a pow 2 + 
&2 * a + &2 * c pow 2) * a * c /(b * b pow 2) /\ 
((c*a* inv b *c*a* inv b)* inv b *c + --(a*c*a* inv b)*
 (inv b *a*a* inv b - a* inv b * inv b)) +  --(c*a* inv b *a)*
 (inv b *a*a* inv b - a* inv b * inv b)
 = (c pow 2 - &2 * a pow 2 + &2 * a) *
 c * a pow 2 / (b * b pow 2) /\
((a * a) * (a * inv b * a * inv b + inv b * a * inv b) + 
(inv b * c) * --(a * c * inv b)) + 
(inv b * c) * --((c * inv b) * a) = 
((a + &1) * a pow 2 - &2 * c pow 2) * a / b pow 2 /\
(a * a) * inv b * c = c * a pow 2 /b  /\ ((a * a) * 
(inv b * a * a * inv b - a * inv b * inv b) + 
(inv b * c) * --(a * c * a * inv b)) + 
(inv b * c) * --(c * a * inv b * a) = 
 (a pow 2 - a - &2 * c pow 2) * a pow 2 / (b pow 2) `] 
THEN SIMP_TAC [real_div] THEN SIMP_TAC [MESON[REAL_FIELD 
`&4 - &2 * sqrt (&2)  > &0 <=> sqrt (&2) < (&4)/(&2) `;ARITH;  
MESON[SQRT_MONO_LT_EQ ; REAL_FIELD `(&2) <  (&16)/(&4)`] 
`sqrt (&2) <  sqrt ((&16)/(&4))`;
MESON[SQRT_DIV ; REAL_FIELD `&16 = &4 * &4 /\ &4 = &2 * &2 `;
GSYM REAL_POW_2;POW_2_SQRT;REAL_POS] `sqrt ((&16)/(&4)) = &4 / &2`]  
`&4 - &2 * sqrt (&2) > &0`;SQRT_POW_2;REAL_FIELD ` 
 &4 - &2 * sqrt (&2) > &0 ==> &0 <= &4 - &2 * sqrt (&2)`] THEN
 SIMP_TAC [MESON[REAL_FIELD ` &2 * sqrt (&2) - &2 > &0 <=> 
 (&2)/(&2) < sqrt (&2)`;ARITH; MESON[SQRT_MONO_LT_EQ ; 
 REAL_FIELD `(&4)/(&4) < (&2)`] `sqrt ((&4)/(&4)) < sqrt (&2)`;
 MESON[SQRT_DIV;REAL_FIELD `&4 = &2 * &2`;GSYM REAL_POW_2;
 POW_2_SQRT;REAL_POS]`sqrt ((&4)/(&4)) = &2 / &2`]  
 `&2 * sqrt (&2) - &2 > &0`;SQRT_POW_2;REAL_FIELD` 
 &2 * sqrt (&2) - &2 > &0 ==> &0 <= &2 * sqrt (&2) - &2`] THEN
 SIMP_TAC[REAL_NEG_LMUL] THENL[(SUBGOAL_THEN 
 `((sqrt (&2) - &1 + &1) * (sqrt (&2) - &1) pow 2 -
 &2 * (&2 * sqrt (&2) - &2)) * (sqrt (&2) - &1)/
 (&2 * (&2 - sqrt (&2))) = -- (&2 - sqrt (&2))/
 (&2 * (&2 - sqrt (&2)))` ASSUME_TAC) THENL 
 [(SIMP_TAC[REAL_FIELD `(x:real) * y / z = (x *y) /z`;
 REAL_SUB_LDISTRIB;REAL_POW_2;REAL_SUB_RDISTRIB;REAL_MUL_RID;
 REAL_MUL_LID;REAL_ADD_LDISTRIB;REAL_ADD_RDISTRIB] THEN 
 SIMP_TAC[GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;
 GSYM REAL_MUL_ASSOC; REAL_MUL_AC] THEN SIMP_TAC [REAL_POW_2] 
 THEN CONV_TAC REAL_FIELD);(ASM_SIMP_TAC[GSYM real_div;
 MESON[REAL_FIELD `&0 < &2 -  sqrt (&2) <=> sqrt (&2) < (&2)`;
 ARITH;MESON[SQRT_MONO_LT_EQ;REAL_FIELD `&2 < &4`] `sqrt (&2) < sqrt (&4)`;
 MESON[SQRT_DIV ; REAL_FIELD ` &4 = &2 * &2`;GSYM REAL_POW_2;
 POW_2_SQRT;REAL_POS] `sqrt (&4) = &2`] `&0 < &2 - sqrt (&2)`; 
 REAL_DIV_REFL;REAL_FIELD `&4 - &2 * sqrt (&2) = &2 *(&2- sqrt (&2))`; 
REAL_FIELD `(-- x) / (y * z) = -- ((&1)/y) * (x/z)`;REAL_MUL_RID;
REAL_POS_NZ] THEN SIMP_TAC[real_div;REAL_MUL_LID])];
IMP_REWRITE_TAC[pos;ADD_LINCOP; MUL_LINCOP;SUB_LINCOP;
COP_TENSOR_LINEAR;SMUL_LINCOP];IMP_REWRITE_TAC[pos;ADD_LINCOP; 
MUL_LINCOP;SUB_LINCOP;COP_TENSOR_LINEAR;SMUL_LINCOP]] ;;



let NS_2  = prove(
`!(a:sm^N) b c d (ten:qop^N->(real^N->complex)->(real^N->complex)).
is_tensor ten /\ is_ns_gate (a, b, c, d, ten)  ==>
tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else 
(if i = 1 then fock (a$1) 2 else  vac (a$3))):bqs^N) = 
(Cx((sqrt (&2) - &1 + &1) * (sqrt (&2) - &1) *
(&2 * sqrt (&2) - &2) / (&4 - &2 * sqrt (&2)) pow 2) %
pos ten (inv (Cx (sqrt (&2))) % I) 1 ** pos ten (cr (d$2)) 2
** pos ten (cr (d$2)) 2 ** pos ten (cr (d$2)) 2 +
Cx((&2 * (sqrt (&2) - &1) pow 2 + &3 * (sqrt (&2) - &1) - &1) *
(sqrt (&2) - &1) *
(&2 * sqrt (&2) - &2) / (&4 - &2 * sqrt (&2)) pow 2) %
pos ten (inv (Cx (sqrt (&2))) % I) 1 ** pos ten (cr (d$2)) 2
** pos ten (cr (d$2)) 2 ** pos ten (cr (d$3)) 3 +
Cx(((sqrt (&2) - &1) pow 2 + &3 * (sqrt (&2) - &1) - &2) *
(&2 * sqrt (&2) - &2) *
(sqrt (&2) - &1) pow 2 / (&4 - &2 * sqrt (&2)) pow 2) %
pos ten (inv (Cx (sqrt (&2))) % I) 1 ** pos ten (cr (d$2)) 2
** pos ten (cr (d$3)) 3 ** pos ten (cr (d$3)) 3 +
Cx((sqrt (&2) - &1 - &1) * (sqrt (&2) - &1) *
(sqrt (&2) - &1) pow 2 *
(&2 * sqrt (&2) - &2) / (&4 - &2 * sqrt (&2)) pow 2) %
pos ten (inv (Cx (sqrt (&2))) % I) 1 ** pos ten (cr (d$3)) 3
** pos ten (cr (d$3)) 3 ** pos ten (cr (d$3)) 3 +
Cx ((&2 * sqrt (&2) - &2 - &2 * (sqrt (&2) - &1 + &1) * 
(sqrt (&2) - &1) pow 2) * sqrt (&2 * sqrt (&2) - &2) /
(sqrt (&4 - &2 * sqrt (&2)) * (&4 - &2 * sqrt (&2)))) %
pos ten (inv (Cx (sqrt (&2))) % cr (d$1)) 1
** pos ten (cr (d$2)) 2 ** pos ten (cr (d$2)) 2 +
Cx((-- &2 * (sqrt (&2) - &1) * (sqrt (&2) - &1) pow 2 -
&4 * (sqrt (&2) - &1) pow 2 + &2 * (sqrt (&2) - &1) +
&2 * (&2 * sqrt (&2) - &2)) * (sqrt (&2) - &1) *
sqrt (&2 * sqrt (&2) - &2) /
(sqrt (&4 - &2 * sqrt (&2)) * (&4 - &2 * sqrt (&2)))) %
pos ten (inv (Cx (sqrt (&2))) % cr (d$1)) 1
** pos ten (cr (d$2)) 2 ** pos ten (cr (d$3)) 3 +
Cx((&2 * sqrt (&2) - &2 - &2 * (sqrt (&2) - &1) pow 2 + 
&2 * (sqrt (&2) - &1)) * sqrt (&2 * sqrt (&2) - &2) *
(sqrt (&2) - &1) pow 2 /
(sqrt (&4 - &2 * sqrt (&2)) * (&4 - &2 * sqrt (&2)))) %
pos ten (inv (Cx (sqrt (&2))) % cr (d$1)) 1
** pos ten (cr (d$3)) 3 ** pos ten (cr (d$3)) 3 + 
Cx(-- (&1 / &2)) %
pos ten (inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) 1
** pos ten (cr (d$2)) 2 + Cx(sqrt (&2 * sqrt (&2) - &2) *
(sqrt (&2) - &1) pow 2 / sqrt (&4 - &2 * sqrt (&2))) %
pos ten (inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) 1
** pos ten (cr (d$1)) 1 + Cx(((sqrt (&2) - &1) pow 2 - 
(sqrt (&2) - &1) -  &2 * (&2 * sqrt (&2) - &2)) *
(sqrt (&2) - &1) pow 2 / (&4 - &2 * sqrt (&2))) %
pos ten (inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) 1
** pos ten (cr (d$3)) 3 ) (tensor 3 (lambda j. vac (d$3)))`, NS_2_TAC);;

(****************************************************************************)
(* Some lemmas to prove the projection of NS outputs for 2-qubits input     *)
(****************************************************************************)
   
let lemma1 = prove( `is_sm sm ==> 
vac (sm) = fock sm 0 /\ cr (sm) (vac sm) = fock sm 1 /\  
(inv (Cx (sqrt (&2))) % (cr (sm) **cr (sm))) (vac sm) = fock sm 2 
/\ (inv (Cx (sqrt (&6))) % 
(((cr (sm) ** cr (sm)) ** cr (sm)))) (vac sm) = fock sm 3`,
 ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
 THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO;ARITH_RULE
 `3 = SUC 2`] THEN SIMP_TAC[GSYM ONE; GSYM TWO;ARITH_RULE
 `SUC 2 = 3`] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;
 COP_SMUL_LID;I_THM;ARITH] THEN COP_ARITH_TAC);;



let lemma11 = prove( `!(a:sm^N) b c d 
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_ns_gate (a, b, c, d, ten) /\ 3 <=  dimindex (:N) ==>        
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then x else vac (d$3)):bqs^N))
(tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
else vac (d$3)):bqs^N)) = K (Cx (&0)) /\
m_modes_pro (tensor 3 (lambda i. if i = 2  then fock (d$2) 1 
else if i = 1 then x else vac (d$3))) (tensor 3 ((lambda i. if i = 1 then 
(inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3)) else if i = 3 then 
cr (d$3) (cr (d$3) (vac (d$3)))  else vac (d$3)):bqs^N)) = K (Cx (&0)) /\
m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then x else vac (d$3))) (tensor 3 ((lambda i. if i = 1 then 
(inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) (cr (d$1) (vac (d$3))) 
else vac (d$3)):bqs^N)) =  K (Cx (&0)) /\
m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (d$2) 1 
else if i = 1 then x else vac (d$3))) (tensor 3 ((lambda i. if i = 1 then 
(inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) (vac (d$3)) else 
if i = 3 then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0))`, 
IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter; REWRITE_RULE[ARITH_RULE 
` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3 /\ ~(1 = 0)`] ((SPEC_V ("sm","d$2")) 
((SPEC_V ("k","2")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","0")) 
((SPEC_V ("m1","1")) tensor_proj_zero)))))] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
(3 <=  dimindex (:N) ==> (1 <=  dimindex (:N) /\ 
2 <=  dimindex (:N)))`; LAMBDA_BETA] THEN 
CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[(MESON[is_ns_gate;
is_beam_splitter] `(is_ns_gate (a, b, c, d, ten) 
==> vac (d$3) = vac (d$2))`);is_ns_gate;lemma1;is_beam_splitter]) ;;            
            
     

            
let lemma12 = prove( `!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
  tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N) = inv (Cx (sqrt (&2))) % 
       tensor 3 ((lambda i. if i = 1 then  fock (d$1) 0
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N)$i):bqs^N) /\  
    (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)) = 
    inv (Cx (sqrt (&2))) % (tensor 3 ((lambda i. if i = 1 then  fock (d$1) 0
    else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)$i):bqs^N)) /\
    (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)) = inv (Cx (sqrt (&2))) % (tensor 3 ((lambda i. if i = 1 then  fock (d$1) 1 
    else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)$i):bqs^N)) /\
    (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = inv (Cx (sqrt (&2))) 
     % (tensor 3 ((lambda i. if i = 1 then  fock (d$1) 0
    else (((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)$i)):bqs^N)) /\ 
     (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
     (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
     (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)) = inv (Cx (sqrt (&2))) 
     % (tensor 3 ((lambda i. if i = 1 then  fock (d$1) 0
    else (((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
    (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
    (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)$i)):bqs^N)) /\ 
     (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) 
    (vac (d$3)) else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = inv (Cx (sqrt (&2))) 
     % (tensor 3 ((lambda i. if i = 1 then  fock (d$1) 1
    else (((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) 
    (vac (d$3)) else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)$i)):bqs^N))
    `,  IMP_REWRITE_TAC[
    (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3`]
    (((SPEC_V ("n","2")) ((SPEC_V ("a","inv (Cx (sqrt (&2)))")) 
        ((SPEC_V ("k","1")) ( tensor_blin_smul))))))] THEN
    IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ (3 <=  dimindex (:N) ==> 1 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN 
    ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
     `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`);
    is_ns_gate;lemma1;is_beam_splitter;COP_SMUL_THM;I_THM]) ;;
    

    
let lemma13 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
  m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then fock (d$1) 2 else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)) = K (Cx (&0)) /\
 m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then fock (d$1) 2 else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
     else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
      then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0))   `, 
    IMP_REWRITE_TAC[lemma12;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3 /\ ~(2 = 1)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","1")) 
        ((SPEC_V ("m1","2")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;
        
        
        let lemma14 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
  m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then fock (d$1) 2 else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N)) = K (Cx (&0)) /\
   m_modes_pro (tensor 3 (lambda i. if i = 2  then fock (d$2) 1
    else if i = 1 then fock (d$1) 2 else vac (d$3)))
    (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)) = K (Cx (&0))  /\
    m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
       else if i = 1 then fock (d$1) 2 else vac (d$3)))
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) =  K (Cx (&0)) /\
   m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
       else if i = 1 then fock (d$1) 2 else vac (d$3)))
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
    (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
    (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)) =  K (Cx (&0))`, 
    IMP_REWRITE_TAC[lemma12;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3 /\ ~(2 = 0)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","0")) 
        ((SPEC_V ("m1","2")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
IMP_REWRITE_TAC[CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;



let lemma15 = prove( `is_ns_gate (a, b, c, d, ten) ==>
proj (fock (d$1) 2) ((inv (Cx (sqrt (&2))) % 
(cr (d$1) ** cr (d$1))) (vac (d$3))) = (fock (d$1) 2) /\ 
proj (fock (d$2) 1) (cr (d$2) (vac (d$3))) = 
(fock (d$2) 1) /\ proj (vac (d$3)) (vac (d$3)) = (vac (d$3))`,
ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> (vac (d$3) = vac (d$2) 
/\ vac (d$3) = vac (d$1)))`);is_ns_gate;lemma1;
is_beam_splitter;FOCK_PROJ_N]);;    
    
    
    let lemma16 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = Cx (sqrt (&2)) % 
    (tensor 3 ((lambda i. if i = 2 then  fock (d$2) 2
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)$i):bqs^N)) /\ 
    (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)) = Cx (sqrt (&2)) % 
    (tensor 3 ((lambda i. if i = 2 then  fock (d$2) 2
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)$i):bqs^N))`, IMP_REWRITE_TAC[
    (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3`]
    (((SPEC_V ("n","2")) ((SPEC_V ("a","Cx (sqrt (&2))")) 
        ((SPEC_V ("k","2")) ( tensor_blin_smul))))))] THEN
    IMP_REWRITE_TAC[ARITH_RULE `1 <= 2 /\ (3 <=  dimindex (:N) ==> 2 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
    THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
    GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
    MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&2)) = Cx(&0))`] 
    `(Cx (sqrt (&2)) * inv (Cx (sqrt (&2)))) = Cx(&1)`)]
    `(cr (d$2) ** cr (d$2)) (vac (d$3)) = Cx (sqrt (&2)) % ( inv (Cx (sqrt (&2))) % 
  ((cr (d$2) ** cr (d$2)) (vac (d$3))))`)] THEN
  SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter] THEN
  SIMP_TAC[GSYM is_ns_gate;GSYM is_beam_splitter] THEN
    ASM_MESON_TAC[COP_SMUL_THM;(MESON[is_ns_gate;is_beam_splitter]  
    `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$2))`)]) ;;
    
    
    
let lemma17 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then x else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
    else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else vac (d$3))
    :bqs^N)) = K (Cx (&0)) /\
     m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
       else if i = 1 then x else vac (d$3)))
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 2 then cr (d$2) (cr (d$2) (vac (d$3))) else if i = 3
     then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) =  K (Cx (&0)) `, 
    IMP_REWRITE_TAC[lemma16;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3 /\ ~(1 = 2)`]
   ((SPEC_V ("sm","d$2")) ((SPEC_V ("k","2")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","2")) 
        ((SPEC_V ("m1","1")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;
        
        
        
    let lemma18 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
    (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
    (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)) = Cx (sqrt (&6)) % 
    (tensor 3 ((lambda i. if i = 2 then  fock (d$2) 3
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
    (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
    (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)$i):bqs^N))`, 
    IMP_REWRITE_TAC[
    (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3`]
    (((SPEC_V ("n","2")) ((SPEC_V ("a","Cx (sqrt (&6))")) 
        ((SPEC_V ("k","2")) ( tensor_blin_smul))))))] THEN
    IMP_REWRITE_TAC[ARITH_RULE `1 <= 2 /\ (3 <=  dimindex (:N) ==> 2 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
    THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
    GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
    MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&6)) = Cx(&0))`] 
    `(Cx (sqrt (&6)) * inv (Cx (sqrt (&6)))) = Cx(&1)`)]
    `((cr (d$2) ** cr (d$2)) ** cr (d$2)) (vac (d$3)) = Cx (sqrt (&6)) % ( inv (Cx (sqrt (&6))) % 
  (((cr (d$2) ** cr (d$2)) ** cr (d$2)) (vac (d$3))))`)] THEN
  SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter] THEN
  SIMP_TAC[GSYM is_ns_gate;GSYM is_beam_splitter] THEN
    ASM_MESON_TAC[COP_SMUL_THM;(MESON[is_ns_gate;is_beam_splitter]  
    `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$2))`)]) ;;
    
    let lemma19 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then x else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) 
    (vac (d$3)) else if i = 2 then cr (d$2) (cr (d$2) 
    (cr (d$2) (vac (d$3)))) else vac (d$3)):bqs^N)) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[lemma18;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3 /\ ~(1 = 3)`]
   ((SPEC_V ("sm","d$2")) ((SPEC_V ("k","2")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","3")) 
        ((SPEC_V ("m1","1")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
        IMP_REWRITE_TAC[GSYM lemma1;CFUN_SMUL_RZERO;GSYM cfun_zero] THEN
        SIMP_TAC[GSYM is_ns_gate;GSYM is_beam_splitter] THEN
    ASM_REWRITE_TAC[COP_SMUL_THM;(MESON[is_ns_gate;is_beam_splitter]  
    `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$2))`)] 
    THEN COP_ARITH_TAC) ;;
    
    
    let lemma110 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N)) = Cx (sqrt (&6)) % 
    (tensor 3 ((lambda i. if i = 3 then  fock (d$3) 3
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N)$i):bqs^N))`, 
    IMP_REWRITE_TAC[
    (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 3 /\ 3 <= 3`]
    (((SPEC_V ("n","2")) ((SPEC_V ("a","Cx (sqrt (&6))")) 
        ((SPEC_V ("k","3")) ( tensor_blin_smul))))))] THEN
    IMP_REWRITE_TAC[ARITH_RULE `1 <= 3`;LAMBDA_BETA] THEN 
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
    THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
    GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
    MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&6)) = Cx(&0))`] 
    `(Cx (sqrt (&6)) * inv (Cx (sqrt (&6)))) = Cx(&1)`)]
    `((cr (d$3) ** cr (d$3)) ** cr (d$3)) (vac (d$3)) =
    Cx (sqrt (&6)) % ( inv (Cx (sqrt (&6))) % 
  (((cr (d$3) ** cr (d$3)) ** cr (d$3)) (vac (d$3))))`)] THEN
  SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter] THEN
  COP_ARITH_TAC) ;;
    
    
        let lemma111 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then x else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
     else if i = 3 then cr (d$3) (cr (d$3) (cr (d$3) (vac (d$3))))
       else vac (d$3)):bqs^N)) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[lemma110;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 3 /\ 3 <= 3 /\ ~(0 = 3)`]
   ((SPEC_V ("sm","d$3")) ((SPEC_V ("k","3")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","3")) 
        ((SPEC_V ("m1","0")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
IMP_REWRITE_TAC[lemma1;CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;
    
    
    
    
    let lemma112 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
   (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)) = Cx (sqrt (&2)) % 
    (tensor 3 ((lambda i. if i = 3 then  fock (d$3) 2
     else ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)$i):bqs^N))`, IMP_REWRITE_TAC[
    (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 3 /\ 3 <= 3`]
    (((SPEC_V ("n","2")) ((SPEC_V ("a","Cx (sqrt (&2))")) 
        ((SPEC_V ("k","3")) ( tensor_blin_smul))))))] THEN
    IMP_REWRITE_TAC[ARITH_RULE `1 <= 3 `;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
    THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
    GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
    MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&2)) = Cx(&0))`] 
    `(Cx (sqrt (&2)) * inv (Cx (sqrt (&2)))) = Cx(&1)`)]
    `(cr (d$3) ** cr (d$3)) (vac (d$3)) = Cx (sqrt (&2)) % ( inv (Cx (sqrt (&2))) % 
  ((cr (d$3) ** cr (d$3)) (vac (d$3))))`)] THEN
  SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter]
  THEN COP_ARITH_TAC);; 
  
    
    let lemma113 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then x else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % I) (vac (d$3))
    else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
    then cr (d$3) (cr (d$3) (vac (d$3))) else vac (d$3)):bqs^N)) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[lemma112;PRO_TENSOR_LINEAR;LINCOP_SMUL] THEN
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 3 /\ 3 <= 3 /\ ~(0 = 2)`]
   ((SPEC_V ("sm","d$3")) ((SPEC_V ("k","3")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","2")) 
        ((SPEC_V ("m1","0")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
IMP_REWRITE_TAC[lemma1;CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;
    
    
    
    let lemma114 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then x else vac (d$3)):bqs^N))
  (tensor 3 ((lambda i. if i = 1 then (inv (Cx (sqrt (&2))) % cr (d$1)) (vac (d$3))
     else if i = 2 then cr (d$2) (vac (d$3)) else if i = 3
      then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 3 /\ 3 <= 3 /\ ~(0 = 1)`]
   ((SPEC_V ("sm","d$3")) ((SPEC_V ("k","3")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","1")) 
        ((SPEC_V ("m1","0")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
IMP_REWRITE_TAC[lemma1;CFUN_SMUL_RZERO;GSYM cfun_zero]) ;;
    
    
    let lemma115 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)) (tensor 3 (lambda i. 
  if i = 1 then (inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) 
 (vac (d$3)) else if i = 2 then cr (d$2) (vac (d$3)) else vac (d$3))) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3 /\ ~(1 = 2)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","2")) 
        ((SPEC_V ("m1","1")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter]) ;;
        
        
    let lemma116 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
   m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
  else if i = 1 then  vac (d$1) else vac (d$3)):bqs^N)) (tensor 3 (lambda i. 
  if i = 1 then (inv (Cx (sqrt (&2))) % (cr (d$1) ** cr (d$1))) 
 (vac (d$3)) else if i = 2 then cr (d$2) (vac (d$3)) else vac (d$3))) =  K (Cx (&0)) `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3 /\ ~(0 = 2)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","2")) 
        ((SPEC_V ("m1","0")) tensor_proj_zero))))))] THEN
        IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3 /\
    (3 <=  dimindex (:N) ==> (2 <=  dimindex (:N) /\ 1 <=  dimindex (:N)))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN
SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter]) ;;
    
    
    
let lemma = prove(`is_ns_gate (a, b, c, d, ten) ==> 
 (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else  vac (d$3)):bqs^N))
 =  (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then vac (d$1) else  vac (d$3))):bqs^N)) `,
  IMP_REWRITE_TAC [COND_ID;GSYM (MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`)]);;

(****************************************************************************)
(* The projection of NS outputs for 2-qubits input on 2-qubits fock state    *)
(****************************************************************************)

let NS_2_PROJ_2 = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
  (m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then fock (d$1) 2 else  vac (d$3))):bqs^N)))
  (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else 
     (if i = 1 then fock (a$1) 2 else  vac (a$3))):bqs^N)) =
     Cx(-- (&1 / &2)) %
     (tensor 3 (lambda i. if i = 1 then (fock (d$1) 2)
      else if i = 2 then (fock (d$2) 1) else vac (d$3)))`,
    IMP_REWRITE_TAC[GEN_ALL NS_2;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
    THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR]
    THEN IMP_REWRITE_TAC[lemma14;lemma13;lemma11;
    CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero] THEN
     SIMP_TAC[PRO_TENSOR_CFUN ] THEN
   SIMP_TAC[tensor;ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\  1 = SUC 0`] THEN
   SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
   IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3`;
   ARITH_RULE `3 <= dimindex (:N)  ==> (2 <= dimindex (:N) 
   /\ 1 <= dimindex (:N)) `;LAMBDA_BETA] THEN 
   CONV_TAC NUM_REDUCE_CONV  THEN IMP_REWRITE_TAC [lemma15]);;      
    
(****************************************************************************)
(* The projection of NS outputs for 2-qubits input on 1-qubit fock state    *)
(****************************************************************************)  
    
    let NS_2_PROJ_1 = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
  (m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then fock (d$1) 1 else  vac (d$3))):bqs^N)))
  (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else 
     (if i = 1 then fock (a$1) 2 else  vac (a$3))):bqs^N)) = K (Cx (&0))`,
    IMP_REWRITE_TAC[GEN_ALL NS_2;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
    THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR]
    THEN IMP_REWRITE_TAC[lemma114;lemma113;lemma111;lemma19;lemma17
    ;lemma11;CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero;lemma115]);;
   
(****************************************************************************)
(* The projection of NS outputs for 2-qubits input on vacuum state          *)
(****************************************************************************)   
   
   
   let NS_2_PROJ_0 = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>
  (m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else  vac (d$3)):bqs^N)))
  (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else 
     (if i = 1 then fock (a$1) 2 else  vac (a$3))):bqs^N)) = K (Cx (&0))`,
    IMP_REWRITE_TAC[GEN_ALL NS_2;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
    THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
    ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
    SIMP_TAC [COND_RATOR;I_THM] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR]
    THEN IMP_REWRITE_TAC[lemma;lemma114;lemma113;lemma111;lemma19;lemma17
    ;lemma11;CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero;lemma116]);; 
