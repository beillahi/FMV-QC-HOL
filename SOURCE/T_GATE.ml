(* ========================================================================= *)
(*                                                                           *)
(*                         T_GATE.ml                                      *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: December 18, 2017                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "HADAMARD_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*---------------***********************---------------*)    


let T_In_Out = define 
`T_In_Out ((x0:sm), (y0:sm),(a:sm^N), (c1:sm^N), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
tensor 1 ((lambda i. LH (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 1 then fock  (a$1) 1  else vac (a$2)):bqs^N)       
/\ tensor 1 ((lambda i. LV (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 2 then fock  (a$2) 1  else vac (a$1)):bqs^N)   
/\ tensor 2 ((lambda j. if j = 1 then fock  (c1$1) 1 else vac (c1$2)):bqs^N)
= tensor 1 ((lambda i. LH (y0)):bqs^N) /\ 
tensor 2 ((lambda j. if j = 2 then fock  (c1$2) 1 else vac (c1$1)):bqs^N) 
= tensor 1 ((lambda i. LV (y0)):bqs^N)  `;; 

let T_GATE = new_definition 
`T_GATE ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (? (a:sm^N) (d:sm^N).
a$1 = d$1  /\ PHASE_SHIFTER (ten,--(pi / &4),a$2,2,d$2,2) /\ 
T_In_Out (x0,y0,a, d, LH, LV)) `;;

let T_STAR_GATE = new_definition 
`T_STAR_GATE ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (? (a:sm^N) (d:sm^N).
a$1 = d$1  /\ PHASE_SHIFTER (ten, pi / &4,a$2,2,d$2,2) /\ 
T_In_Out (x0,y0,a, d, LH, LV)) `;;

let T_0 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  T_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LH (fl0)):bqs^N) =   
tensor 1  (lambda i. LH (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;T_GATE] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[T_In_Out] THEN  
REWRITE_TAC[GSYM T_In_Out;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] T_In_Out]
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;
COMPLEX_INV_1;COP_SMUL_LID]);;

let T_STAR_0 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  T_STAR_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LH (fl0)):bqs^N) =   
tensor 1  (lambda i. LH (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;T_STAR_GATE] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
IMP_REWRITE_TAC[T_In_Out] THEN  
REWRITE_TAC[GSYM T_In_Out;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] T_In_Out]
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;
COMPLEX_INV_1;COP_SMUL_LID]);;

let T_1 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  T_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LV (fl0)):bqs^N) =   
cexp (ii * Cx (pi / &4)) % tensor 1  (lambda i. LV (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;T_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ;  `(d:sm^N)`]
THEN IMP_REWRITE_TAC[T_In_Out] THEN  
REWRITE_TAC[PHASE_SHIFTER;pos] THEN
ONCE_REWRITE_TAC[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`]
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
SIMP_TAC[COMPLEX_NEG_NEG;CX_NEG;COMPLEX_FIELD `--(x:complex) * --y = x *y`]);;


let T_STAR_1 = 
prove(`!(fl0:sm) (fl1:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex)).
is_tensor ten /\  T_STAR_GATE (fl0, fl1,ten,LH, LV)   ==>
tensor 1  ((lambda i. LV (fl0)):bqs^N) =   
cexp (-- ii * Cx (pi / &4)) % tensor 1  (lambda i. LV (fl1))  `, 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;T_STAR_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ;  `(d:sm^N)`]
THEN IMP_REWRITE_TAC[T_In_Out] THEN  
REWRITE_TAC[PHASE_SHIFTER;pos] THEN
ONCE_REWRITE_TAC[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`]
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
SIMP_TAC[COMPLEX_NEG_NEG;CX_NEG;COMPLEX_FIELD `--(x:complex) * --y = x *y`]);;


let TT_tac l = 
 SUBGOAL_TAC "t0" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",(List.nth l 1)) (SPEC_V("fl0",(List.nth l 0)) T_0))))) 
[IMP_REWRITE_TAC [spec_thm_tac T_0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "t1" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",(List.nth l 1)) (SPEC_V("fl0",(List.nth l 0)) T_1))))) 
[IMP_REWRITE_TAC [spec_thm_tac T_1] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "t0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "t1" (fun thm-> ALL_TAC);;

let T_STAR_tac l = 
 SUBGOAL_TAC "t0" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",(List.nth l 1)) (SPEC_V("fl0",(List.nth l 0)) T_STAR_0))))) 
[IMP_REWRITE_TAC [spec_thm_tac T_STAR_0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "t1" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("fl1",(List.nth l 1)) (SPEC_V("fl0",(List.nth l 0)) T_STAR_1))))) 
[IMP_REWRITE_TAC [spec_thm_tac T_STAR_1] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "t0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "t1" (fun thm-> ALL_TAC);;
