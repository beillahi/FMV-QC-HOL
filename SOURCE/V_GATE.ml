(* ========================================================================= *)
(*                                                                           *)
(*                         V_GATE.ml                                      *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: December 18, 2017                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)




(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*  2 * 2 + 4 * 2 = 12*)
(*  2 CZ gates *)
(*---------------***********************---------------*)    

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

