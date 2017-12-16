(* ========================================================================= *)
(*                                                                           *)
(*                         FLIP_GATE.ml                                  *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: MAY 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "HADAMARD_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*---------------***********************---------------*)    



let CEXP_II_PI = prove(`cexp (ii * Cx(pi)) = --Cx(&1)`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI;
    SIN_PI;COMPLEX_ADD_RID;COMPLEX_MUL_RZERO;CX_NEG]);;  
	
let CEXP_II_PI_CNJ = prove(`cexp (-- (ii * Cx(pi))) = --Cx(&1)`,
   REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
	REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI;COMPLEX_ADD_RID;
    REAL_POS; SIN_PI;COS_NEG;SIN_NEG;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;CX_NEG] THEN 
	CONV_TAC COMPLEX_FIELD);; 
           
let CEXP_II_PI2 = prove(`cexp (ii * Cx(pi / &2)) = ii`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI2;
    SIN_PI2;COMPLEX_ADD_LID;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID]);; 
	
let CEXP_II_PI2_CNJ = prove(`cexp (--(ii * Cx(pi / &2))) = --ii`,
    REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
	REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI2;COMPLEX_ADD_RID;
    REAL_POS; SIN_PI2;COS_NEG;SIN_NEG;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;CX_NEG] THEN 
	CONV_TAC COMPLEX_FIELD);; 

let SIN_PI4 = prove
 (`sin(pi / &4) = sqrt(&1 / &2)`,
  MP_TAC(SPEC `pi / &4` SIN_CIRCLE) THEN
  SIMP_TAC[SPEC `pi / &4` COS_SIN; REAL_ARITH `p / &2 - p / &4 = p / &4`] THEN
  REWRITE_TAC[REAL_RING `x pow 2  + x pow 2= &1 <=> x pow 2 = &1 / &2 `] THEN
  MP_TAC (SPEC `sin(pi / &4)` (SPEC `&1 / &2` SQRT_UNIQUE)) THEN 
  MP_TAC(SPEC `pi / &4` SIN_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
  
let COS_PI4 = prove
 (`cos(pi / &4) = sqrt(&1 / &2)`,
  SIMP_TAC[SIN_PI4;SPEC `pi / &4` COS_SIN; REAL_ARITH `p / &2 - p / &4 = p / &4`]);;
  
let CEXP_II_PI4 = prove(`cexp (ii * Cx(pi / &4)) = Cx(&1 / sqrt(&2)) + ii * Cx(&1 / sqrt(&2))`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI4;SQRT_DIV;SQRT_1;
REAL_POS; SIN_PI4]);; 

let CEXP_II_PI4_CNJ = prove(`cexp (--(ii * Cx(pi / &4))) = Cx(&1 / sqrt(&2)) - ii * Cx(&1 / sqrt(&2))`,
    REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
	REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI4;SQRT_DIV;SQRT_1;
    REAL_POS; SIN_PI4;COS_NEG;SIN_NEG] THEN 
    REWRITE_TAC[CX_NEG;GSYM complex_sub;COMPLEX_MUL_RNEG]);; 

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



let T_GATE = new_definition 
`T_GATE ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (!(a:sm^N) (d:sm^N).
a$1 = d$1  /\ PHASE_SHIFTER (ten,--(pi / &4),a$2,2,d$2,2) /\ 
T_In_Out (x0,y0,a, d, LH, LV)) `;;


let T_STAR_GATE = new_definition 
`T_STAR_GATE ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (!(a:sm^N) (d:sm^N).
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
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ;  `(d:sm^N)`]
THEN IMP_REWRITE_TAC[T_In_Out] THEN  
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
MAP_EVERY EXISTS_TAC [`(a:sm^N)` ;  `(d:sm^N)`]
THEN IMP_REWRITE_TAC[T_In_Out] THEN  
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

let V2_GATE = define 
   `V2_GATE ((t:sm), (c:sm), (t1:sm),(c1:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (a2:sm) (b1:sm) (b2:sm) (d1:sm) (d2:sm) (e2:sm). 
T_STAR_GATE (c, a1,ten,LH, LV) /\ 
HADAMARD_GATE  (t, a2, ten, LH, LV) /\ 
CNOT2_GATE (a2, a1, b2, b1,ten, LH, LV ,m_modes_pro) /\
T_GATE (b1, d1,ten,LH, LV) /\ 
T_STAR_GATE (b2, d2,ten,LH, LV)  /\ 
CNOT2_GATE (d2,d1,e2,c1,ten,LH, LV,m_modes_pro) /\ 
HADAMARD_GATE  (e2, t1, ten, LH, LV) )` ;;

(*  2 * 2 + 4 * 2 = 12*)
(*2 CZ gates *)

let V2_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;V2_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(a2:sm)`;`(b1:sm)`;`(b2:sm)`;`(d1:sm)`;`(d2:sm)`;`(e2:sm)`] THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test15.txt" [] [("T_STAR_GATE",1);("T_GATE",1)] 0))  
(extract_port [] "(t,1,c,0)" 0 0) 3) 2 0 0 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;


let V2_01 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (t) else  LV (c)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) +
(Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV t1 else LV c1))`, V2_TAC);;


let V2_11 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (t) else  LV (c)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) +
(Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LH t1 else LV c1))`, V2_TAC);;

let V2_10 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (t) else  LH (c)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LV t1 else LH c1)`, V2_TAC);;

let V2_00 = prove( `!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (t) else  LH (c)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH t1 else LH c1)`, V2_TAC);;


let VG2_tac l = 
 SUBGOAL_TAC "v200" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v210" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v201" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v211" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "v200" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v210" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v201" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v211" (fun thm-> ALL_TAC);;

let V_GATE = define 
   `V_GATE ((c:sm), (t:sm), (c1:sm), (t1:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (a2:sm) (b1:sm) (b2:sm) (d1:sm) (d2:sm) (e2:sm). 
T_STAR_GATE (c, a1,ten,LH, LV) /\ 
HADAMARD_GATE  (t, a2, ten, LH, LV) /\ 
CNOT1_GATE (a1,a2, b1,b2,ten, LH, LV ,m_modes_pro) /\
T_GATE (b1, d1,ten,LH, LV) /\ 
T_STAR_GATE (b2, d2,ten,LH, LV)  /\ 
CNOT1_GATE (d1,d2,c1,e2,ten,LH, LV,m_modes_pro) /\ 
HADAMARD_GATE  (e2, t1, ten, LH, LV) )` ;;


let V_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;V_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(a2:sm)`;`(b1:sm)`;`(b2:sm)`;`(d1:sm)`;`(d2:sm)`;`(e2:sm)`] THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test13.txt" [] [("T_STAR_GATE",1);("T_GATE",1)] 0))  
(extract_port [] "(c,0,t,1)" 0 0) 3) 2 0 0 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;

let V_01 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (c) else  LV (t)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH c1 else LV t1)`, V_TAC);;


let V_11 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (c) else  LV (t)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV c1 else LV t1) +
(Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV c1 else LH t1))`, V_TAC);;

let V_10 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (c) else  LH (t)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV c1 else LH t1) +
(Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV c1 else LV t1))`, V_TAC);;


let V_00 = prove( `!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (c) else  LH (t)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH c1 else LH t1)`, V_TAC);;


let VG_tac l = 
 SUBGOAL_TAC "v00" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v10" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v01" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "v11" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "v10" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v01" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v00" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "v11" (fun thm-> ALL_TAC);;

let V2_STAR_GATE = define 
   `V2_STAR_GATE ( (t:sm), (c:sm),(t1:sm),(c1:sm), 
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (a2:sm) (b1:sm) (b2:sm) (d1:sm) (d2:sm) (e2:sm). 
T_GATE (c, a1,ten,LH, LV) /\ 
HADAMARD_GATE  (t, a2, ten, LH, LV) /\ 
CNOT2_GATE (a2,a1, b2,b1,ten, LH, LV ,m_modes_pro) /\
T_STAR_GATE (b1, d1,ten,LH, LV) /\ 
T_GATE (b2, d2,ten,LH, LV)  /\ 
CNOT2_GATE (d2,d1,e2,c1,ten,LH, LV,m_modes_pro) /\ 
HADAMARD_GATE  (e2, t1, ten, LH, LV) )` ;;


let V2_STAR_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;V2_STAR_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(a2:sm)`;`(b1:sm)`;`(b2:sm)`;`(d1:sm)`;`(d2:sm)`;`(e2:sm)`] THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test16.txt" [] [("T_STAR_GATE",1);("T_GATE",1)] 0))  
(extract_port [] "(t,1,c,0)" 0 0) 3) 2 0 0 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;

let V2_STAR_10 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_STAR_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (t) else  LH (c)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LV t1 else LH c1)`, V2_STAR_TAC);;


let V2_STAR_11 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_STAR_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (t) else  LV (c)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) +
(Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LH t1 else LV c1))`, V2_STAR_TAC);;

let V2_STAR_01 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_STAR_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (t) else  LV (c)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) +
(Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV t1 else LV c1))`, V2_STAR_TAC);;


let V2_STAR_00 = prove( `!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V2_STAR_GATE (t,c,t1,c1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (t) else  LH (c)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH t1 else LH c1)`, V2_STAR_TAC);;


let VG2_STAR_tac l = 
 SUBGOAL_TAC "vSTAR_200" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_STAR_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_STAR_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_210" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_STAR_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_STAR_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_201" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_STAR_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_STAR_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_211" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("t",(List.nth l 0)) 
 (SPEC_V("c",(List.nth l 1)) (SPEC_V ("t1",(List.nth l 2)) (SPEC_V("c1",(List.nth l 3)) V2_STAR_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V2_STAR_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "vSTAR_210" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_201" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_200" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_211" (fun thm-> ALL_TAC);;


let V_STAR_GATE = define 
   `V_STAR_GATE ((c:sm), (t:sm), (c1:sm), (t1:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (a1:sm) (a2:sm) (b1:sm) (b2:sm) (d1:sm) (d2:sm) (e2:sm). 
T_GATE (c, a1,ten,LH, LV) /\ 
HADAMARD_GATE  (t, a2, ten, LH, LV) /\ 
CNOT1_GATE (a1,a2, b1,b2,ten, LH, LV ,m_modes_pro) /\
T_STAR_GATE (b1, d1,ten,LH, LV) /\ 
T_GATE (b2, d2,ten,LH, LV)  /\ 
CNOT1_GATE (d1,d2,c1,e2,ten,LH, LV,m_modes_pro) /\ 
HADAMARD_GATE  (e2, t1, ten, LH, LV) )` ;;


let V_STAR_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;V_STAR_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(a1:sm)`;`(a2:sm)`;`(b1:sm)`;`(b2:sm)`;`(d1:sm)`;`(d2:sm)`;`(e2:sm)`] THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test14.txt" [] [("T_STAR_GATE",1);("T_GATE",1)] 0))  
(extract_port [] "(c,0,t,1)" 0 0) 3) 2 0 0 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;

let V_STAR_01 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_STAR_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (c) else  LV (t)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH c1 else LV t1)`, V_STAR_TAC);;


let V_STAR_11 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_STAR_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (c) else  LV (t)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV c1 else LV t1) +
(Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV c1 else LH t1))`, V_STAR_TAC);;

let V_STAR_10 = prove(`!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_STAR_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LV (c) else  LH (t)):bqs^N) = 
Cx (&1 / &16) % ((Cx (&1 / sqrt(&2)) * cexp ((ii * Cx(pi / &4)))) %
tensor 2 (lambda i. if i = 1 then LV c1 else LH t1) +
(Cx (&1 / sqrt(&2)) * cexp (--(ii * Cx(pi / &4)))) %
 tensor 2 (lambda i. if i = 1 then LV c1 else LV t1))`, V_STAR_TAC);;


let V_STAR_00 = prove( `!(c:sm) (t:sm) (c1:sm) (t1:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ 2 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
V_STAR_GATE (c,t,c1,t1,ten,LH,LV,m_modes_pro)  ==>
tensor 2 ((lambda i. if i = 1 then LH (c) else  LH (t)):bqs^N) = Cx (&1 / &16) %
tensor 2 (lambda i. if i = 1 then LH c1 else LH t1)`, V_STAR_TAC);;


let VG_STAR_tac l = 
 SUBGOAL_TAC "vSTAR_00" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_STAR_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_STAR_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_10" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_STAR_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_STAR_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_01" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_STAR_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_STAR_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "vSTAR_11" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("c",(List.nth l 0)) 
 (SPEC_V("t",(List.nth l 1)) (SPEC_V ("c1",(List.nth l 2)) (SPEC_V("t1",(List.nth l 3)) V_STAR_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac V_STAR_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "vSTAR_10" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_01" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_00" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "vSTAR_11" (fun thm-> ALL_TAC);;


quantum_tac (matrix_procedure [] (gate_matrix "test13.txt" [] [] 0) 
     (extract_port [] "(c,0,t,1)" 0 0) 1) 2 0 []);;   

quantum_tac (matrix_procedure [] ((gate_matrix "test13.txt" [] [("T_STAR_GATE",1);("T_GATE",1)] 0))  
(extract_port [] "(c,0,t,1)" 0 0) 3) 2 0 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;


(--(((Cx (--(&(1 * 1) / (&4 * sqrt (&2)))) * cexp (ii * Cx (pi / &4))) *
          cexp (--ii * Cx (pi / &4))) *
         Cx (&1 / &4)) *
      Cx (&1 / sqrt (&2)) +
      Cx (&(1 * 1) / &(4 * 4) * (&1 / sqrt (&2)) pow 2))

SIMP_TAC[COMPLEX_MUL_LNEG;CEXP_NEG_RMUL;CEXP_NEG_LMUL;thm3;GSYM CEXP_ADD;
GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM COMPLEX_MUL_ASSOC;
COMPLEX_MUL_SYM;GSYM CX_ADD;GSYM CX_MUL;GSYM real_sub;
COMPLEX_ADD_LINV;COMPLEX_ADD_RINV;COMPLEX_SUB_REFL;CEXP_0;
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW;REAL_MUL_SYM;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG;GSYM COMPLEX_NEG_ADD; GSYM COMPLEX_MUL_2;COMPLEX_NEG_NEG;
COMPLEX_MUL_RNEG;MESON[CX_MUL; COMPLEX_MUL_ASSOC] 
` Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x2`] 
THEN SIMP_TAC[REAL_FIELD `((x1:real)/y)+(x2/y)=(x1+x2)/y /\ (pi / & 4) * &2 =  pi / &2`;
REAL_POW_DIV;thm1;thm2;SQRT_DIV;SQRT_1;
GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG] THEN SIMP_TAC[COMPLEX_FIELD `x * ii = ii * x`;COMPLEX_NEG_NEG;
CEXP_NEG;COMPLEX_MUL_LNEG;COMPLEX_INV_1;GSYM COMPLEX_NEG_INV
;CEXP_II_PI2;CEXP_II_PI;COMPLEX_MUL_RNEG;COMPLEX_MUL_RID;COMPLEX_INV_II] 
THEN CONV_TAC NUM_REDUCE_CONV THEN CFUN_ARITH_TAC




	
SIMP_TAC[GSYM CX_ADD;GSYM CX_MUL; 
    GSYM CX_SUB;REAL_ADD_AC;REAL_SUB_REFL;
    REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
    REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_SYM;GSYM real_sub;
    GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
    CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
    REAL_MUL_LNEG] THEN SIMP_TAC[thm1;thm2;SQRT_DIV;SQRT_1;
    GSYM REAL_POW_2;REAL_POS;SQRT_POW_2]
quantum_sub_tac (List.nth L i) m new_circuits

 [quantum_sub_tac [["0"; "T_STAR_GATE"; "1"; "c"; "a1"];
    ["1"; "HADAMARD_GATE"; "1"; "t"; "a2"]] 2 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)] THEN
   quantum_sub_tac [["0"; "CNOT1_GATE"; "2"; "a1"; "a2"; "b1"; "b2"]] 2 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)] THEN
   quantum_sub_tac [["0"; "T_GATE"; "1"; "b1"; "d1"]; ["1"; "T_STAR_GATE"; "1"; "b2"; "d2"]] 2 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)] THEN
   quantum_sub_tac [["0"; "CNOT1_GATE"; "2"; "d1"; "d2"; "c1"; "e2"]] 2 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)] THEN
   quantum_sub_tac [["1"; "HADAMARD_GATE"; "1"; "e2"; "t1"]] 2 [("T_STAR_GATE",T_STAR_tac);("T_GATE",TT_tac)];;

quantum_sub_tac l m new_circuits =   
    let ll = main_tab_gates [["0"; "T_STAR_GATE"; "1"; "c"; "a1"];
    ["1"; "HADAMARD_GATE"; "1"; "t"; "a2"]] 2 in
    let len = List.length [["0"; "T_STAR_GATE"; "1"; "c"; "a1"];
    ["1"; "HADAMARD_GATE"; "1"; "t"; "a2"]] in
    ASM_SIMP_TAC ([(main_comp_inputs ll 2);tensor_nmlem1] @ 
    (one_less 2)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l ll) THEN
    rewrite_decompose_tac  2 ll 0 0 THEN
    rew_condition_tac  2 ll  0 THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l ll)) THEN
    STRIP_TAC THEN (rewrite_gates_tac l 0 new_circuits) THEN
    SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
    COMPLEX_ADD_LDISTRIB;
    COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
    SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    SIMP_TAC ((GSYM CX_MUL) :: (rewr_dev len 0)) THEN
    SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) =
    a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
    (if len = 1 then ALL_TAC else
    IMP_REWRITE_TAC[GSYM (main_comp_inputs ll m);
    REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
    ONCE_SIMP_TAC (rewrite_l [m]) THEN 
    rewrite_recompose_tac  m ll 0 0 THEN
    SIMP_TAC[condition_recompose m ll] THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l [m])) ;;

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