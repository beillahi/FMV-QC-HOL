(* ========================================================================= *)
(*                                                                           *)
(*                  boson_sampling_circuit_8_modes.ml                        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2019                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "boson_sampling_circuit_7_modes.ml";;



(*------------------------ helper theorems--------------------- -----------*)

(***********************************************************)


let thm813 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 8 <= dimindex (:N) /\ is_tensor ten /\ is_sm (m$7) /\ is_sm (m$8)
 /\ vac ((m:sm^N)$7) = vac (m$8)  ==> 
 pos ten (cr (m$7)) 2
     (pos ten (cr (m$8)) 1 (tensor 8 ((lambda j. vac (m$8)):bqs^N))) =
tensor 8 ((lambda i. if i = 2 then  fock (m$7) 1 else (if i = 1 then fock (m$8) 1  else vac (m$8))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm823 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
8 <= dimindex (:N) /\ is_tensor ten /\ is_sm (m$7) /\ is_sm (m$8)
 /\ vac ((m:sm^N)$7) = vac (m$8)  ==> 
 pos ten (cr (m$8)) 1
     (pos ten (cr (m$7)) 2 (tensor 8 ((lambda j. vac (m$8)):bqs^N))) =
tensor 8 ((lambda i. if i = 1 then  fock (m$8) 1 else (if i = 2 then fock (m$7) 1  else vac (m$8))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm803 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
8 <= dimindex (:N) /\ is_tensor ten /\ is_sm (m$7) /\ is_sm (m$8)
 /\ vac ((m:sm^N)$7) = vac (m$8)  ==> 
pos ten (cr (m$7)) 2
     (pos ten (cr (m$8)) 1 (tensor 8 ((lambda j. vac (m$8)):bqs^N))) =
pos ten (cr (m$8)) 1
     (pos ten (cr (m$7)) 2 (tensor 8 ((lambda j. vac (m$8)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm823;thm813] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 8)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 8 2 [1;2] [2;1])]);;




(*-----------------------------------------------------*)

let thm_help10 = (prove(`
(Boson_eight_Circuit5 (a,m,ten))  ==> 
(vac ((m:sm^N)$1) = vac (m$8) /\ vac (m$6) = vac (m$8) /\ 
vac (m$2) = vac (m$8) /\ vac (m$5) = vac (m$8) /\ vac (m$7) = vac (m$8) /\  
vac (m$3) = vac (m$8) /\ vac (m$4) = vac (m$8) )`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_eight_Circuit5] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;

let thm_help11 = (prove(`
(Boson_seven_Circuit3 (a,k,ten))  ==> (vac (a$7) = vac (k$7))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_seven_Circuit3] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;

  
let thm_help12 = COP_ARITH`
 Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$7)) 1 (tensor 8 (lambda j. vac (m$8)))) +
  Cx (&5631896372397850801449 / &122070312500000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$6)) 2 (tensor 8 (lambda j. vac (m$8))))   = 
(Cx (&1814169961918137077002917 / &9765625000000000000000000)  %
 (pos ten (cr (k$7)) 1 ** (pos ten (cr (k$7)) 1)) +
  Cx (&5631896372397850801449 / &122070312500000000000000) %
 (pos ten (cr (k$7)) 1 ** (pos ten (cr (k$6)) 2)) ) (tensor 8 (lambda j. vac (m$8)))`;;
 
(*------------------------Circuit Definition---------------------*)
 
 let Boson_eight_Circuit5 = new_definition 
`Boson_eight_Circuit5 ((a:sm^N), (m:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)))  
<=>  (? (b:sm^N) (c:sm^N) (d:sm^N) (e:sm^N) (f:sm^N) (l:sm^N) (k:sm^N).
8 <= dimindex (:N) /\ is_tensor ten /\ 
Boson_seven_Circuit3 (a,k,ten) /\ 
boson_seven_thm0110 (a,k,ten) /\
mirror (ten,k$8,1,m$8,1) /\ vac (a$8) = vac (a$7) /\ 
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$7,1,l$8,2,k$8,1,m$7,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$6,2,f$8,3,l$8,2,m$6,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$5,3,e$8,4,f$8,3,m$5,4) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$4,4,d$8,5,e$8,4,m$4,5) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$3,5,c$8,6,d$8,5,m$3,6) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$2,6,b$8,7,c$8,6,m$2,7) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,k$1,7,a$8,8,b$8,7,m$1,8)  )`;;


(*------------------------ Goal--------------------------------*)

g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (m:sm^N).
8 <= dimindex (:N) /\ is_tensor ten /\
Boson_eight_Circuit5(a,m,ten)  ==>
tensor 8 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$8))):bqs^N) =   
   Cx (&658099988741255562480063393 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (m$8) 2 else vac (m$8)) +
  Cx (&5631896372397850801449 / &12207031250000000000000000) %
 tensor 8 (lambda i. if i = 2 then  fock (m$7) 1 else (if i = 3 then fock (m$6) 1  else vac (m$8))) +
 Cx (&20830249435157397858440097 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (m$7) 2 else vac (m$8)) +
 Cx (&50687067351580657213041 / &12207031250000000000000000) %
 tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 3 then fock (m$6) 1  else vac (m$8))) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) %
  tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 2 then fock (m$7) 1  else vac (m$8)))`;;
  


(*------------------------ Tactics--------------------- -----------*)
  
REPEAT STRIP_TAC THEN 

SUBGOAL_THEN ` (vac ((m:sm^N)$1) = vac (m$8) /\ vac (m$6) = vac (m$8) /\ 
vac (m$2) = vac (m$8) /\ vac (m$5) = vac (m$8) /\ vac (m$7) = vac (m$8) /\  
vac (m$3) = vac (m$8) /\ vac (m$4) = vac (m$8) )` ASSUME_TAC THEN

IMP_REWRITE_TAC[thm_help10] THEN 

REPEAT (POP_ASSUM MP_TAC) THEN   
     
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_eight_Circuit5] THEN 
integer_equiv 8 THEN REWRITE_TAC[boson_seven_thm0110] THEN REPEAT STRIP_TAC THEN 
    
ASM_SIMP_TAC ([(main_comp_inputs [7;1] 8);tensor_nmlem1] @ 
(one_less 8)) THEN CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_SIMP_TAC (rewrite_l [7;1]) THEN
rewrite_decompose_tac  8 [7;1] 0 0 THEN
rew_condition_tac  8 [7;1]  0 THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [7;1])) THEN
    

    
ASM_SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;
CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;
COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
ASM_SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
ASM_SIMP_TAC ((GSYM CX_MUL) :: (rewr_dev 2 0)) THEN 
ASM_SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) =
 a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
(IMP_REWRITE_TAC[GSYM (main_comp_inputs [7;1] 8);
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
ONCE_ASM_SIMP_TAC (rewrite_l [8]) THEN 
rewrite_recompose_tac  8 [7;1] 0 0 THEN
IMP_REWRITE_TAC[thm_help11] THEN 
ASM_SIMP_TAC[condition_recompose 8 [7;1]]   THEN 
ASM_SIMP_TAC[ETA_AX;condition0_recompose0 8 [7;1] [[3];[]] [3];
condition0_recompose0 8 [7;1] [[4];[]] [4];
condition0_recompose0 8 [7;1] [[2];[]] [2];
condition0_recompose0 8 [7;1] [[1];[]] [1];
condition0_recompose0 8 [7;1] [[5];[]] [5];
condition0_recompose0 8 [7;1] [[6];[]] [6];
condition0_recompose01 8 [7;1] [[8];[8]] [8];
condition0_recompose0 8 [7;1] [[1;2];[]] [1;2];
condition0_recompose0 8 [7;1] [[1;4];[]] [1;4];
condition0_recompose0 8 [7;1] [[1;3];[]] [1;3];
condition0_recompose0 8 [7;1] [[1;5];[]] [1;5];
condition0_recompose0 8 [7;1] [[1;6];[]] [1;6];
condition0_recompose0 8 [7;1] [[2;3];[]] [2;3];
condition0_recompose0 8 [7;1] [[2;4];[]] [2;4];
condition0_recompose0 8 [7;1] [[2;5];[]] [2;5];
condition0_recompose0 8 [7;1] [[2;6];[]] [2;6];
condition0_recompose0 8 [7;1] [[5;6];[]] [5;6];
condition0_recompose0 8 [7;1] [[4;5];[]] [4;5];
condition0_recompose0 8 [7;1] [[4;6];[]] [4;6];
condition0_recompose0 8 [7;1] [[3;5];[]] [3;5];
condition0_recompose0 8 [7;1] [[3;6];[]] [3;6];
condition0_recompose0 8 [7;1] [[3;4];[]] [3;4]] THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [8])) ;;

    
SUBGOAL_THEN `(vac ((k:sm^N)$1) = vac (k$7) /\ vac (k$6) = vac (k$7) /\ 
vac (k$2) = vac (k$7) /\ vac (k$5) = vac (k$7) /\  
vac (k$3) = vac (k$7) /\ vac (k$4) = vac (k$7) )` ASSUME_TAC THEN
IMP_REWRITE_TAC[thm_help7] THEN 
REPEAT (POP_ASSUM MP_TAC) THEN 


REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN NUMBER_SFG_TAC1 [] THEN 
SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN 
NUMBER_SFG_TAC2 [] THEN 
CONV_TAC NUM_REDUCE_CONV THEN 
SIMP_TAC[COP_POW_2;COP_MUL;BETA_THM;COP_SMUL_THM] THEN
SIMP_TAC[GSYM ONE] THEN
IMP_REWRITE_TAC[CFUN_ARITH `~(a = Cx (&0)) ==> a % (inv (a:complex) % (x:bqs)) = x`;
(SIMP_CONV[CX_INJ;SQRT_EQ_0] THENC REAL_RAT_REDUCE_CONV)` ~(Cx (sqrt (&2)) = Cx (&0))`]
THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN 

REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_ARITH` vac (a$8) =  vac (a$7) <=> vac (a$7) = vac (a$8)`]
THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[] THEN 

MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN MULTI_MODE_DECOMPOSE_TAC 
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN

SIMP_TAC[GSYM pos]

THEN SIMP_TAC[thm_help12] THEN 


ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;GSYM COP_MUL_THM;pos] THEN
ASM_SIMP_TAC[COP_ADD_LDISTRIB;COP_SMUL_ASSOC; GSYM  pos] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ 
a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN ASM_SIMP_TAC[pos] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        
(* CPU time (user): 1453.697004*)       
(*CPU time (user): 1588.76947*) 
IMP_REWRITE_TAC[pos;COP_TENSOR_LINEAR;LINCOP_MUL_DISTRIB_CLAUSES;COP_SMUL_ASSOC;COP_MUL_LSMUL;
LINCOP_ADD_MUL_LDISTRIB;LINCOP_MUL_RMUL;COP_ADD_MUL_RDISTRIB;COP_ADD_ASSOC;ARITH_LINCOP_CLAUSES]
THEN ASM_SIMP_TAC[ARITH_LINCOP_CLAUSES ;COP_TENSOR_LINEAR;CNJ_MUL;COP_ADD_LDISTRIB;COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
COP_TENSOR_LINEAR;SMUL_LINCOP;ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG]
THEN REWRITE_TAC[REAL_MUL_RNEG;REAL_MUL_LNEG; REAL_NEG_NEG;CX_NEG;COMPLEX_MUL_ASSOC;COP_ADD_ASSOC] 
THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN 
ASM_SIMP_TAC[CNJ_MUL;COP_ADD_LDISTRIB;COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
COP_TENSOR_LINEAR;SMUL_LINCOP;ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
REWRITE_TAC[COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM]
THEN REWRITE_TAC[GSYM pos;CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG]
THEN complex_simp_tactic3 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic1 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV  
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
 
(* 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN *)
        

IMP_REWRITE_TAC[thm803] THEN       
 


REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CFUN_ARITH_TAC;;


let boson_eight_thm1 = top_thm();;

(*--------------------**********************-----------*) 

(*---------------------------------------------------*)
(*
   To simplify the proof we define the boson_seven input 
   in term of outputs which have an emplititude that 
   is bigger than 0.01
                                                       *)
(*--------------------**********************-----------*) 

let boson_eight_them0110 = new_definition
 `boson_eight_them0110 ((a:sm^N), (m:sm^N), (ten:qop^N->(real^N->complex)-> (real^N->complex))) <=>
((8 <= dimindex (:N) /\ is_tensor ten /\ Boson_eight_Circuit5(a,m,ten))  ==>
tensor 8 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$8))):bqs^N) =   
  Cx (&658099988741255562480063393 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (m$8) 2 else vac (m$8)) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) %
  tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 2 then fock (m$7) 1  else vac (m$8)))) `;;
 
(*--------------Useless Formalization------------------*)
(*--------------------**********************-----------*) 

(*

 

 Cx (&658099988741255562480063393 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (m$8) 2 else vac (m$8)) +
  Cx (&20830249435157397858440097 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 2 then  fock (m$7) 1 else (if i = 3 then fock (m$6) 1  else vac (m$8))) +
 Cx (&175875631794776829710462283 / &625000000000000000000000000) %
 tensor 8 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (m$7) 2 else vac (m$8)) +
 Cx (&50687067351580657213041 / &12207031250000000000000000) %
 tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 3 then fock (m$6) 1  else vac (m$8))) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) %
  tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 2 then fock (m$7) 1  else vac (m$8))) 
  
 
 
 
  Cx (&658099988741255562480063393 / &4882812500000000000000000000) %
 tensor 8 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (m$8) 2 else vac (m$8)) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) %
  tensor 8 (lambda i. if i = 1 then  fock (m$8) 1 else (if i = 2 then fock (m$7) 1  else vac (m$8))) 

 
 Cx (&658099988741255562480063393 / &4882812500000000000000000000) % 
 pos ten (cr (m$8)) 1 (pos ten (cr (m$8)) 1 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) % 
 pos ten (cr (m$8)) 1 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) 

 
 Cx (&5631896372397850801449 / &12207031250000000000000000) %  0.00046136495082683193765470208
 pos ten (cr (m$7)) 2 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) % 0.053369746613794242310000896
 pos ten (cr (m$8)) 1 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&50687067351580657213041 / &12207031250000000000000000) % 0.00415228455744148743889231872
 pos ten (cr (m$8)) 1 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&20830249435157397858440097 / &4882812500000000000000000000) % 0.004266035084320235081408531865
 pos ten (cr (m$7)) 2 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&658099988741255562480063393 / &4882812500000000000000000000) % 0.134778877694209139195916982886
 pos ten (cr (m$8)) 1 (pos ten (cr (m$8)) 1 (tensor 8 (lambda j. vac (m$8)))) 
 
 
 Cx (&5631896372397850801449 / &12207031250000000000000000) %
 pos ten (cr (m$7)) 2 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&208475572710133759023441 / &3906250000000000000000000) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&50687067351580657213041 / &12207031250000000000000000) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&20830249435157397858440097 / &4882812500000000000000000000) %
 pos ten (cr (m$7)) 2 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&658099988741255562480063393 / &4882812500000000000000000000) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$8)) 1 (tensor 8 (lambda j. vac (m$8)))) 
 
 
Cx (-- &295439379753090521913363 / &25000000000000000000000000) % 0.01181757519012362087653452
 pos ten (cr (m$8)) 1 (pos ten (cr (m$8)) 1 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&526269427687399169335401 / &7812500000000000000000000) % 0.067362486743987093674931328
 pos ten (cr (m$7)) 2 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&175875631794776829710462283 / &625000000000000000000000000) % 0.2814010108716429275367396528
 pos ten (cr (m$7)) 2 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 (Cx (&18147221644393074804669 / &1562500000000000000000000) * ii) % 0.01161422185241156787498816
 pos ten (cr (m$8)) 1 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 (Cx (&7316209485640102735165527 / &62500000000000000000000000) * ii) % 0.117059351770241643762648432
 pos ten (cr (m$8)) 1 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8))))
 
 
 
 
 
 
 
 
 
Cx (-- &295439379753090521913363 / &25000000000000000000000000) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$8)) 1 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&526269427687399169335401 / &7812500000000000000000000) %
 pos ten (cr (m$7)) 2 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 Cx (&175875631794776829710462283 / &625000000000000000000000000) %
 pos ten (cr (m$7)) 2 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8)))) +
 (Cx (&18147221644393074804669 / &1562500000000000000000000) * ii) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$6)) 3 (tensor 8 (lambda j. vac (m$8)))) +
 (Cx (&7316209485640102735165527 / &62500000000000000000000000) * ii) %
 pos ten (cr (m$8)) 1 (pos ten (cr (m$7)) 2 (tensor 8 (lambda j. vac (m$8))))




                                              *)

    
(****************************************************************************************)    
(****************************************************************************************)
    