(* ========================================================================= *)
(*                                                                           *)
(*                         FLIP_GATE.ml                                      *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "T_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*---------------***********************---------------*)    

let FLip_In_Out = define 
`FLip_In_Out ((x0:sm), (y0:sm),(a:sm^N), (c1:sm^N), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
tensor 1 ((lambda i. LH (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 1 then fock  (a$1) 1  else vac (a$2)):bqs^N)       
/\ tensor 1 ((lambda i. LV (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 2 then fock  (a$2) 1  else vac (a$1)):bqs^N)   
/\ tensor 2 ((lambda j. if j = 1 then fock  (c1$1) 1 else vac (c1$2)):bqs^N)
= tensor 1 ((lambda i. LH (y0)):bqs^N) /\ 
tensor 2 ((lambda j. if j = 2 then fock  (c1$2) 1 else vac (c1$1)):bqs^N) 
= tensor 1 ((lambda i. LV (y0)):bqs^N)  `;; 

let FLIP_G = new_definition 
`FLIP_G ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (!(a:sm^N) (b:sm^N) (c:sm^N) (d:sm^N).
is_beam_splitter (Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),ten,a$1,1,a$2,2,b$1,1,b$2,2) /\
is_beam_splitter (Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),ten,b$1,1,b$2,2,d$1,1,c$2,2) /\
PHASE_SHIFTER (ten,pi,c$2,2,d$2,2) /\ 
FLip_In_Out (x0,y0,a, d, LH, LV)) `;;


let FlIP_0 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  FLIP_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LH (fl0)):bqs^N) =   
tensor 1  (lambda i. LV (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;FLIP_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ; `(b:sm^N)`;`(c:sm^N)` ; `(d:sm^N)`]
THEN IMP_REWRITE_TAC[FLip_In_Output] THEN  
REWRITE_TAC[GSYM FLip_In_Output;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] FLip_In_Output]
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;
COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) 
= (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN
ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN        
SIMP_TAC[keylem;ARITH;COND_ID] THEN
IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
ASM_SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN
SIMP_TAC[COMPLEX_NEG_NEG;CX_NEG;COMPLEX_FIELD `--(x:complex) * --y = x *y`]
SIMP_TAC [CFUN_SMUL_DIS;CFUN_SMUL_ASSOC;
CFUN_SUB_LDISTRIB;GSYM CX_MUL] THEN
SIMP_TAC [REAL_MUL_LNEG;GSYM CX_ADD;CFUN_SUB_NEG;
GSYM CFUN_SMUL_LNEG;GSYM CFUN_ADD_RDISTRIB;
GSYM CX_MUL; GSYM CX_NEG;GSYM CX_ADD; GSYM CX_SUB;
GSYM CX_INV;CFUN_ADD_AC;CFUN_ADD_LID;CFUN_SMUL_LZERO;
SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;
REAL_MUL_SYM;GSYM real_sub;CNJ_CX;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;
REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_MUL_RID;REAL_ADD_LINV;REAL_MUL_LZERO;
REAL_DIV_RMUL;REAL_SUB_RNEG;CFUN_ADD_RID;
REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;
REAL_SUB_RZERO;REAL_SUB_REFL;REAL_NEG_NEG;
REAL_FIELD ` &1 / &2 + &1 / &2 = &1`;CFUN_SMUL_LID] THEN
SIMP_TAC[GSYM CFUN_ADD_ASSOC;GSYM CFUN_ADD_RDISTRIB;CFUN_ADD_LID;
CFUN_SMUL_LZERO;GSYM real_sub;GSYM CX_ADD;REAL_SUB_REFL]);;


let FlIP_1 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  FLIP_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LV (fl0)):bqs^N) =   
tensor 1  (lambda i.  LH (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;FLIP_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ; `(b:sm^N)`;`(c:sm^N)` ; `(d:sm^N)`]
THEN IMP_REWRITE_TAC[FLip_In_Output] THEN  
REWRITE_TAC[GSYM FLip_In_Output;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] FLip_In_Output;]
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;
COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) 
= (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN
ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN        
SIMP_TAC[keylem;ARITH;COND_ID] THEN
IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
ASM_SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN
SIMP_TAC[CEXP_NEG;COMPLEX_MUL_LNEG;COMPLEX_INV_1;
GSYM COMPLEX_NEG_INV;CEXP_II_PI] THEN
SIMP_TAC [CFUN_SMUL_DIS;CFUN_SMUL_ASSOC;
CFUN_SUB_LDISTRIB;GSYM CX_MUL;CFUN_SUB_AC] THEN
SIMP_TAC [REAL_MUL_LNEG;GSYM CX_ADD;CFUN_SUB_NEG;
CFUN_ADD_AC;GSYM CFUN_SMUL_LNEG;GSYM CFUN_ADD_RDISTRIB;
GSYM CX_MUL; GSYM CX_NEG;GSYM CX_ADD; GSYM CX_SUB;
GSYM CX_INV;CFUN_ADD_AC;CFUN_ADD_LID;CFUN_SMUL_LZERO;
SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;
REAL_MUL_SYM;GSYM real_sub;CNJ_CX;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;
REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_MUL_RID;REAL_ADD_LINV;REAL_MUL_LZERO;
REAL_DIV_RMUL;REAL_SUB_RNEG;CFUN_ADD_RID;
REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;
REAL_SUB_RZERO;REAL_SUB_REFL;REAL_NEG_NEG;
REAL_FIELD ` &1 / &2 + &1 / &2 = &1`;CFUN_SMUL_LID;CFUN_ARITH 
`!(f1:cfun) (b:complex) (a:complex) (c:cfun). 
 a % f1 + b % f1  + c = (a+b)% f1 + c`]);;

 
 let flip_tac a b = 
 SUBGOAL_TAC "flip0" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",b) (SPEC_V("fl0",a) FlIP_0))))) 
[IMP_REWRITE_TAC [spec_thm_tac FlIP_0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "flip1" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",b) (SPEC_V("fl0",a) FlIP_1))))) 
[IMP_REWRITE_TAC [spec_thm_tac FlIP_1] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "flip0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "flip1" (fun thm-> ALL_TAC);;