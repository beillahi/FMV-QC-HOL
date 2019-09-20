(* ========================================================================= *)
(*                                                                           *)
(*                  boson_sampling_circuit_7_modes.ml                        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2019                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "boson_sampling_circuit_6_modes.ml";;



(*------------------------ helper theorems--------------------- -----------*)

(***********************************************************)


let thm713 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 7 <= dimindex (:N) /\ is_tensor ten /\ is_sm (k$6) /\ is_sm (k$7)
 /\ vac ((k:sm^N)$6) = vac (k$7)  ==> 
 pos ten (cr (k$6)) 2
     (pos ten (cr (k$7)) 1 (tensor 7 ((lambda j. vac (k$7)):bqs^N))) =
tensor 7 ((lambda i. if i = 2 then  fock (k$6) 1 else (if i = 1 then fock (k$7) 1  else vac (k$7))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm723 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 7 <= dimindex (:N) /\ is_tensor ten /\  is_sm (k$6)  /\ is_sm (k$7)
 /\ vac ((k:sm^N)$6) = vac (k$7)  ==> 
 pos ten (cr (k$7)) 1
     (pos ten (cr (k$6)) 2 (tensor 7 ((lambda j. vac (k$7)):bqs^N))) =
tensor 7 ((lambda i. if i = 1 then  fock (k$7) 1 else (if i = 2 then fock (k$6) 1  else vac (k$7))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm703 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 7 <= dimindex (:N) /\ is_tensor ten /\  is_sm (k$6)  /\ is_sm (k$7)
 /\ vac ((k:sm^N)$6) = vac (k$7)  ==> 
 pos ten (cr (k$6)) 2
     (pos ten (cr (k$7)) 1 (tensor 7 ((lambda j. vac (k$7)):bqs^N))) =
 pos ten (cr (k$7)) 1
     (pos ten (cr (k$6)) 2 (tensor 7 ((lambda j. vac (k$7)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm723;thm713] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 7)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 7 2 [1;2] [2;1])]);;




(*-----------------------------------------------------*)

let thm_help7 = (prove(`
(Boson_seven_Circuit3 (a,k,ten))  ==> 
(vac ((k:sm^N)$1) = vac (k$7) /\ vac (k$6) = vac (k$7) /\ 
vac (k$2) = vac (k$7) /\ vac (k$5) = vac (k$7) /\  
vac (k$3) = vac (k$7) /\ vac (k$4) = vac (k$7) )`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_seven_Circuit3] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;

let thm_help8 = (prove(`
(Boson_six_Circuit3 (a,l,ten))  ==> (vac (a$6) = vac (l$6))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_six_Circuit3] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;


let thm_help9 = COP_ARITH`
 Cx (&10575340251395085747 / &976562500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&142433637600420388593 / &610351562500000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$6)) 1 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&4483670787141399 / &244140625000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$3)) 4 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&2095428329740690119 / &195312500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 7 (lambda j. vac (k$7))))  = 
( Cx (&10575340251395085747 / &976562500000000000000) %
 (pos ten (cr (l$6)) 1 ** (pos ten (cr (l$5)) 2 )) +
 Cx (&142433637600420388593 / &610351562500000000000) %
 (pos ten (cr (l$6)) 1 ** (pos ten (cr (l$6)) 1 )) +
 Cx (&4483670787141399 / &244140625000000000) %
 (pos ten (cr (l$6)) 1 ** (pos ten (cr (l$3)) 4 )) +
 Cx (&2095428329740690119 / &195312500000000000000) %
 (pos ten (cr (l$6)) 1 ** (pos ten (cr (l$4)) 3)) ) (tensor 7 (lambda j. vac (k$7)))`;;
 
(*------------------------Circuit Definition---------------------*)
 
 let Boson_seven_Circuit3 = new_definition 
`Boson_seven_Circuit3 ((a:sm^N), (k:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)))  
<=>  (? (b:sm^N) (c:sm^N) (d:sm^N) (e:sm^N) (f:sm^N) (l:sm^N).
7 <= dimindex (:N) /\ is_tensor ten /\ 
Boson_six_Circuit3 (a,l,ten) /\ 
boson_six_thm0110 (a,l,ten) /\
mirror (ten,l$7,1,k$7,1) /\ vac (a$7) = vac (a$6) /\ 
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$6,1,f$7,2,l$7,1,k$6,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$5,2,e$7,3,f$7,2,k$5,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$4,3,d$7,4,e$7,3,k$4,4) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$3,4,c$7,5,d$7,4,k$3,5) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$2,5,b$7,6,c$7,5,k$2,6) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,l$1,6,a$7,7,b$7,6,k$1,7) )`;;


(*------------------------ Goal--------------------------------*)

g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (k:sm^N).
7 <= dimindex (:N) /\ is_tensor ten /\
Boson_seven_Circuit3(a,k,ten)  ==>
tensor 7 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$7))):bqs^N) =   
  Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (k$7) 2 else vac (k$7))  +
 Cx (&5631896372397850801449 / &122070312500000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 2 then fock (k$6) 1  else vac (k$7))) +
 Cx (&10378408129084754073 / &39062500000000000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 3 then fock (k$5) 1  else vac (k$7))) +
 Cx (&93405673161762786657 / &39062500000000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 3 then fock (k$5) 1  else vac (k$7))) +
 Cx (&187373137831588551087 / &19531250000000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 4 then fock (k$4) 1  else vac (k$7))) + 
 Cx (&27664141064300191358523 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (k$6) 2 else vac (k$7)) +
 Cx (&4483670787141399 / &24414062500000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 5 then fock (k$3) 1  else vac (k$7))) +
 Cx (&20819237536843172343 / &19531250000000000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 4 then fock (k$4) 1  else vac (k$7))) +
 Cx (&40353037084272591 / &24414062500000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 5 then fock (k$3) 1  else vac (k$7)))`;;

(*------------------------ Tactics--------------------- -----------*)
  
REPEAT STRIP_TAC THEN 

SUBGOAL_THEN ` (vac ((k:sm^N)$1) = vac (k$7) /\ vac (k$6) = vac (k$7) /\ 
vac (k$2) = vac (k$7) /\ vac (k$5) = vac (k$7) /\  
vac (k$3) = vac (k$7) /\ vac (k$4) = vac (k$7) )` ASSUME_TAC THEN

IMP_REWRITE_TAC[thm_help7] THEN 

REPEAT (POP_ASSUM MP_TAC) THEN   
     
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_seven_Circuit3] THEN 
integer_equiv 7 THEN REWRITE_TAC[boson_six_thm0110] THEN REPEAT STRIP_TAC THEN 
    
ASM_SIMP_TAC ([(main_comp_inputs [6;1] 7);tensor_nmlem1] @ 
(one_less 7)) THEN CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_SIMP_TAC (rewrite_l [6;1]) THEN
rewrite_decompose_tac  7 [6;1] 0 0 THEN
rew_condition_tac  7 [6;1]  0 THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [6;1])) THEN
    

    
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
(IMP_REWRITE_TAC[GSYM (main_comp_inputs [6;1] 7);
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
ONCE_ASM_SIMP_TAC (rewrite_l [7]) THEN 
rewrite_recompose_tac  7 [6;1] 0 0 THEN
IMP_REWRITE_TAC[thm_help8] THEN 
ASM_SIMP_TAC[condition_recompose 7 [6;1]]   THEN 
ASM_SIMP_TAC[ETA_AX;condition0_recompose0 7 [6;1] [[3];[]] [3];
condition0_recompose0 7 [6;1] [[4];[]] [4];
condition0_recompose0 7 [6;1] [[2];[]] [2];
condition0_recompose0 7 [6;1] [[1];[]] [1];
condition0_recompose0 7 [6;1] [[5];[]] [5];
condition0_recompose0 7 [6;1] [[6];[]] [6];
condition0_recompose01 7 [6;1] [[7];[7]] [7];
condition0_recompose0 7 [6;1] [[1;2];[]] [1;2];
condition0_recompose0 7 [6;1] [[1;4];[]] [1;4];
condition0_recompose0 7 [6;1] [[1;3];[]] [1;3];
condition0_recompose0 7 [6;1] [[1;5];[]] [1;5];
condition0_recompose0 7 [6;1] [[1;6];[]] [1;6];
condition0_recompose0 7 [6;1] [[2;3];[]] [2;3];
condition0_recompose0 7 [6;1] [[2;4];[]] [2;4];
condition0_recompose0 7 [6;1] [[2;5];[]] [2;5];
condition0_recompose0 7 [6;1] [[2;6];[]] [2;6];
condition0_recompose0 7 [6;1] [[5;6];[]] [5;6];
condition0_recompose0 7 [6;1] [[4;5];[]] [4;5];
condition0_recompose0 7 [6;1] [[4;6];[]] [4;6];
condition0_recompose0 7 [6;1] [[3;5];[]] [3;5];
condition0_recompose0 7 [6;1] [[3;6];[]] [3;6];
condition0_recompose0 7 [6;1] [[3;4];[]] [3;4]] THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [7])) ;;

    
SUBGOAL_THEN `(vac ((l:sm^N)$1) = vac (l$6) /\ vac (l$2) = vac (l$6) /\ 
vac (l$3) = vac (l$6) /\ vac (l$4) = vac (l$6) /\ vac (l$5) = vac (l$6))` ASSUME_TAC THEN
IMP_REWRITE_TAC[thm_help5] THEN 
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
REWRITE_TAC[CFUN_ARITH` vac (a$7) =  vac (a$6) <=> vac (a$6) = vac (a$7)`]
THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[] THEN 

MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN MULTI_MODE_DECOMPOSE_TAC 
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN

SIMP_TAC[GSYM pos]

THEN SIMP_TAC[thm_help9] THEN 


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
        

IMP_REWRITE_TAC[thm703] THEN       
 


REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CFUN_ARITH_TAC;;


let boson_sevn_thm1 = top_thm();;

(*--------------------**********************-----------*) 

(*---------------------------------------------------*)
(*
   To simplify the proof we define the boson_seven input 
   in term of outputs which have an emplititude that 
   is bigger than 0.01
                                                       *)
(*--------------------**********************-----------*) 

let boson_seven_thm0110 = new_definition
 `boson_seven_thm0110 ((a:sm^N), (k:sm^N), (ten:qop^N->(real^N->complex)-> (real^N->complex))) <=>
((7 <= dimindex (:N) /\ is_tensor ten /\ Boson_seven_Circuit3(a,k,ten))  ==>
tensor 7 ((lambda i. if i = 2 then  fock (a$2) 1 else (if i = 3 then fock (a$3) 1  else vac (a$7))):bqs^N) =    
 Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (k$7) 2 else vac (k$7)) +
 Cx (&5631896372397850801449 / &122070312500000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 2 then fock (k$6) 1  else vac (k$7)))) `;;
 
(*--------------Useless Formalization------------------*)
(*--------------------**********************-----------*) 

(*

 

 Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (k$7) 2 else vac (k$7))  +
 Cx (&5631896372397850801449 / &122070312500000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 2 then fock (k$6) 1  else vac (k$7))) +
 Cx (&10378408129084754073 / &39062500000000000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 3 then fock (k$5) 1  else vac (k$7))) +
 Cx (&93405673161762786657 / &39062500000000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 3 then fock (k$5) 1  else vac (k$7)))
 Cx (&187373137831588551087 / &19531250000000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 4 then fock (k$4) 1  else vac (k$7))) + 
 Cx (&27664141064300191358523 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (k$6) 2 else vac (k$7)) +
 Cx (&4483670787141399 / &24414062500000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 5 then fock (k$3) 1  else vac (k$7))) +
 Cx (&20819237536843172343 / &19531250000000000000000) %
 tensor 7 (lambda i. if i = 2 then  fock (k$6) 1 else (if i = 4 then fock (k$4) 1  else vac (k$7))) +
 Cx (&40353037084272591 / &24414062500000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 5 then fock (k$3) 1  else vac (k$7)))+
 
  Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$7)) 1 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&5631896372397850801449 / &122070312500000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 
 
  Cx (&1814169961918137077002917 / &9765625000000000000000000) %
 tensor 7 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (k$7) 2 else vac (k$7)) +
 Cx (&5631896372397850801449 / &122070312500000000000000) %
 tensor 7 (lambda i. if i = 1 then  fock (k$7) 1 else (if i = 2 then fock (k$6) 1  else vac (k$7))) +
 
 
 
 
 
  Cx (&1814169961918137077002917 / &9765625000000000000000000) %  0.1857710041004172366850987008
 pos ten (cr (k$7)) 1 (pos ten (cr (k$7)) 1 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&5631896372397850801449 / &122070312500000000000000) % 0.046136495082683193765470208
 pos ten (cr (k$7)) 1 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&10378408129084754073 / &39062500000000000000000) % 0.0002656872481045697042688
 pos ten (cr (k$6)) 2 (pos ten (cr (k$5)) 3 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&93405673161762786657 / &39062500000000000000000) % 0.0023911852329411273384192
 pos ten (cr (k$7)) 1 (pos ten (cr (k$5)) 3 (tensor 7 (lambda j. vac (k$7))))
 Cx (&187373137831588551087 / &19531250000000000000000) % 0.0095935046569773338156544
 pos ten (cr (k$7)) 1 (pos ten (cr (k$4)) 4 (tensor 7 (lambda j. vac (k$7)))) + 
 Cx (&27664141064300191358523 / &9765625000000000000000000) % 0.0028328080449843395951127552
 pos ten (cr (k$6)) 2 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&4483670787141399 / &24414062500000000000) % 0.00018365115544131170304
 pos ten (cr (k$6)) 2 (pos ten (cr (k$3)) 5 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&20819237536843172343 / &19531250000000000000000) % 0.0010659449618863704239616
 pos ten (cr (k$6)) 2 (pos ten (cr (k$4)) 4 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&40353037084272591 / &24414062500000000000) %  0.00165286039897180532736
 pos ten (cr (k$7)) 1 (pos ten (cr (k$3)) 5 (tensor 7 (lambda j. vac (k$7)))) +
 
 
 
 
 
 
 
 
 
 
 Cx (-- &17988653767623040855647 / &4882812500000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$7)) 1 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&201574440213126341889213 / &9765625000000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&10378408129084754073 / &39062500000000000000000) %
 pos ten (cr (k$6)) 2 (pos ten (cr (k$5)) 3 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&95178062262555771723 / &97656250000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$5)) 3 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&10532142678995146251 / &1220703125000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$4)) 4 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&27664141064300191358523 / &9765625000000000000000000) %
 pos ten (cr (k$6)) 2 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&248977269578701722226707 / &9765625000000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$6)) 2 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&1850147269453383158714211 / &9765625000000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$7)) 1 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&4483670787141399 / &24414062500000000000) %
 pos ten (cr (k$6)) 2 (pos ten (cr (k$3)) 5 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&20819237536843172343 / &19531250000000000000000) %
 pos ten (cr (k$6)) 2 (pos ten (cr (k$4)) 4 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&276672241283702389839 / &195312500000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$5)) 3 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&40353037084272591 / &24414062500000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$3)) 5 (tensor 7 (lambda j. vac (k$7)))) +
 Cx (&18858854967666211071 / &19531250000000000000000) %
 pos ten (cr (k$7)) 1 (pos ten (cr (k$4)) 4 (tensor 7 (lambda j. vac (k$7))))




                                              *)

    
(****************************************************************************************)    
(****************************************************************************************)
    