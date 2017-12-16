(* ========================================================================= *)
(*                                                                           *)
(*                          HADAMARD_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "CZ_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)      
let CEXP_II_PI = prove(`cexp (ii * Cx(pi)) = --Cx(&1)`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI;
    SIN_PI;COMPLEX_ADD_RID;COMPLEX_MUL_RZERO;CX_NEG]);;  
           
let CEXP_II_PI2 = prove(`cexp (ii * Cx(pi / &2)) = ii`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI2;
    SIN_PI2;COMPLEX_ADD_LID;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID]);; 

let Hadamard_In_Output = define 
`Hadamard_In_Output ((x0:sm), (y0:sm), (a:sm^N), (c:sm^N), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
tensor 1 ((lambda i. LH (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 1 then fock  (a$1) 1  else vac (a$1)):bqs^N)       
/\ tensor 1 ((lambda i. LV (x0)):bqs^N) =
tensor 2 ((lambda i. if i = 2 then fock  (a$2) 1  else vac (a$1)):bqs^N)
/\ tensor 1 ((lambda i. vac (x0)):bqs^N) =
tensor 2 ((lambda i. vac (a$1)):bqs^N)         
/\ tensor 2 ((lambda j. if j = 1 then fock  (c$1) 1 else vac (c$2)):bqs^N)
= tensor 1 ((lambda i. LH (y0)):bqs^N) /\ 
tensor 2 ((lambda j. if j = 2 then fock  (c$2) 1 else vac (c$2)):bqs^N) 
= tensor 1 ((lambda i. LV (y0)):bqs^N) /\ 
tensor 2 ((lambda j. vac (c$2)):bqs^N) 
= tensor 1 ((lambda i. vac (y0)):bqs^N) `;; 


let HADAMARD_GATE  = new_definition 
`HADAMARD_GATE ((x0:sm), (y0:sm), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  
<=>  (!(a:sm^N) (b:sm^N) (c:sm^N). 
(is_beam_splitter (Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),ten,a$1,1,a$2,2,c$1,1,b$2,2) /\ 
PHASE_SHIFTER (ten,pi,b$2,2,c$2,2) /\ 
Hadamard_In_Output (x0,y0,a, c, LH, LV)))`;;
       

let HADAMARD_1 = 
 prove( `!hd0 hd1 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (LH:sm->(real->complex))  (LV:sm->(real->complex)).
 is_tensor ten /\ HADAMARD_GATE  ((hd0:sm), (hd1:sm), ten, LH, LV) ==>
tensor 1  ((lambda i. LV  (hd0)):bqs^N) =      
 Cx (sqrt (&1 / &2)) %  
tensor 1  (lambda i.  LH  (hd1)) -  
Cx (sqrt (&1 / &2)) % 
tensor 1  (lambda i. LV  (hd1)) `,
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;HADAMARD_GATE] THEN 
REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`(a:sm^N)`;`(b:sm^N)`;`(c:sm^N)`] 
THEN IMP_REWRITE_TAC[Hadamard_In_Output] THEN   
REWRITE_TAC[GSYM Hadamard_In_Output;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] Hadamard_In_Output;] 
THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  THEN 
MULTI_MODE_DECOMPOSE_TAC THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;
COP_SMUL_LID] THEN ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB] 
THEN SIMP_TAC[CEXP_NEG;COMPLEX_MUL_LNEG;COMPLEX_INV_1;GSYM COMPLEX_NEG_INV;
COP_SUB_THM;COP_SMUL_THM;CEXP_II_PI;COMPLEX_MUL_RNEG;COMPLEX_MUL_RID;
COP_SMUL_ASSOC;GSYM COP_SUB;COP_SMUL_LNEG]);;



let HADAMARD_0 = 
 prove( `!hd0 hd1 (ten:qop^N->(real^N->complex)-> (real^N->complex))
 (LH:sm->(real->complex))  (LV:sm->(real->complex)).
is_tensor ten /\ HADAMARD_GATE ((hd0:sm), (hd1:sm), ten, LH, LV) ==>
tensor 1  ((lambda i. LH  (hd0)):bqs^N)=   
Cx (sqrt (&1 / &2)) %  
tensor 1  (lambda i.  LH  (hd1)) +  
Cx (sqrt (&1 / &2)) % 
tensor 1  (lambda i. LV  (hd1)) `,
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;HADAMARD_GATE] THEN 
REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`(a:sm^N)`;`(b:sm^N)`;`(c:sm^N)`] 
THEN IMP_REWRITE_TAC[Hadamard_In_Output] THEN   
REWRITE_TAC[GSYM Hadamard_In_Output;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] Hadamard_In_Output;] 
THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]  THEN 
MULTI_MODE_DECOMPOSE_TAC THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;
COP_SMUL_LID] THEN ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB] THEN
SIMP_TAC[CEXP_NEG;COMPLEX_MUL_LNEG;COMPLEX_INV_1;GSYM COMPLEX_NEG_INV;
COP_SUB_THM;COP_SMUL_THM;CEXP_II_PI;COMPLEX_MUL_RNEG;COMPLEX_MUL_RID;
COP_SMUL_ASSOC;GSYM COP_SUB;COP_SMUL_LNEG] THEN SIMP_TAC[COP_SMUL_THM;
COP_ADD_THM;GSYM COP_SMUL_LNEG] THEN CFUN_ARITH_TAC);;

let HADAMARD_vac = 
 prove( `!hd0 hd1 (ten:qop^N->(real^N->complex)-> (real^N->complex))
 (LH:sm->(real->complex))  (LV:sm->(real->complex)).
is_tensor ten /\ HADAMARD_GATE ((hd0:sm), (hd1:sm), ten, LH, LV) ==>
tensor 1  ((lambda i. vac  (hd0)):bqs^N) = 
tensor 1  ((lambda i.  vac  (hd1)):bqs^N) `,
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;HADAMARD_GATE] THEN 
REPEAT GEN_TAC THEN MAP_EVERY EXISTS_TAC [`(a:sm^N)`;`(b:sm^N)`;`(c:sm^N)`] 
THEN IMP_REWRITE_TAC[Hadamard_In_Output] THEN   
REWRITE_TAC[GSYM Hadamard_In_Output;is_beam_splitter;PHASE_SHIFTER;pos] THEN
SIMP_TAC[REWRITE_RULE[CFUN_ARITH `tensor 2 x = tensor 1 y <=> 
tensor 1 y = tensor 2 x`] Hadamard_In_Output;] 
THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]);;


let hadamard_tac a b = 
 SUBGOAL_TAC "hadamard0" (concl (UNDISCH_ALL (spec_thm_tac 
 (SPEC_V ("hd1",b) (SPEC_V("hd0",a) HADAMARD_0)))))
[IMP_REWRITE_TAC [ spec_thm_tac HADAMARD_0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "hadamard1" (concl (UNDISCH_ALL (spec_thm_tac 
 (SPEC_V ("hd1",b) (SPEC_V("hd0",a) HADAMARD_1)))))
[IMP_REWRITE_TAC [ spec_thm_tac HADAMARD_1] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "hadamardvac" (concl (UNDISCH_ALL (spec_thm_tac 
 (SPEC_V ("hd1",b) (SPEC_V("hd0",a) HADAMARD_vac)))))
[IMP_REWRITE_TAC [spec_thm_tac HADAMARD_vac] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "hadamard0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "hadamard1" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "hadamardvac" (fun thm-> ALL_TAC);;

