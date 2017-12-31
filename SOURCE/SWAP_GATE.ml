(* ========================================================================= *)
(*                                                                           *)
(*                             SWAP_GATE.ml                                 *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "CNOT_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*16 optical qubits *)
(*3 CZ gates *)
(*--------------------**********************------------------*) 


let SWAP_GATE = define 
   `SWAP_GATE ((x1:sm), (x2:sm), (y1:sm), (y2:sm),
   (ten:qop^N->(real^N->complex)-> (real^N->complex)), 
    (LH:sm->(real->complex)), (LV:sm->(real->complex)),
    (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(! (c1:sm) (c2:sm) (d1:sm) (d2:sm).
CNOT2_GATE (x1,x2, c1,c2,ten, LH, LV ,m_modes_pro) /\
CNOT1_GATE (c1,c2,d1,d2,ten,LH, LV,m_modes_pro) /\
CNOT2_GATE (d1,d2, y1,y2,ten, LH, LV ,m_modes_pro))` ;;

let SWAP_tactic = 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;SWAP_GATE] THEN
REPEAT GEN_TAC THEN
MAP_EVERY EXISTS_TAC [`(c1:sm)`; `(c2:sm)`; `(d1:sm)`;`(d2:sm)`] THEN
STRIP_TAC THEN cnot2_tac "sw1" "sw2" "c1" "c2" THEN cnot1_tac "c1" "c2" "d1" "d2" THEN
cnot2_tac "d1" "d2" "sw3" "sw4" THEN
REPEAT (POP_ASSUM MP_TAC) THEN
SIMP_TAC[IMP_IMP;CFUN_SMUL_DISTRIB;GSYM CX_MUL;
REAL_FIELD `(&1 / &4 * &1 / &4) * &1 / &4 = &1 / &64`];;




let SWAP_00 = prove(`!(sw1:sm) (sw2:sm) (sw3:sm) (sw4:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE (sw1,sw2,sw3,sw4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i. if i = 1 then LH (sw1) else  LH (sw2) ):bqs^N) = Cx (&1 / &64) %
tensor 2 ((lambda i. if i = 1 then LH (sw3) else  LH (sw4) ):bqs^N)`,SWAP_tactic);;



let SWAP_01 = prove(`!(sw1:sm) (sw2:sm) (sw3:sm) (sw4:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE (sw1,sw2,sw3,sw4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i. if i = 1 then LH (sw1) else  LV (sw2)):bqs^N) = Cx (&1 / &64) %
tensor 2 ((lambda i. if i = 1 then LV (sw3) else LH (sw4)):bqs^N)`,SWAP_tactic);;


let SWAP_10 = prove(`!(sw1:sm) (sw2:sm) (sw3:sm) (sw4:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE (sw1,sw2,sw3,sw4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i. if i = 1 then LV (sw1) else LH (sw2)):bqs^N) = Cx (&1 / &64) %
tensor 2 ((lambda i. if i = 1 then LH (sw3) else  LV (sw4)):bqs^N)`,SWAP_tactic);;

let SWAP_11 = prove(`!(sw1:sm) (sw2:sm) (sw3:sm) (sw4:sm)
  (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE (sw1,sw2,sw3,sw4,ten,LH,LV,m_modes_pro) ==>
tensor 2 ((lambda i. if i = 1 then LV (sw1) else LV (sw2)):bqs^N) = Cx (&1 / &64) %
tensor 2 ((lambda i. if i = 1 then LV (sw3) else LV (sw4)):bqs^N)`,SWAP_tactic);;




let swap_tac a0 b0 c0 d0 = 
 SUBGOAL_TAC "swap00" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("sw1",a0) 
 (SPEC_V("sw2",b0) (SPEC_V ("sw3",c0) (SPEC_V("sw4",d0) SWAP_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac SWAP_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "swap10" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("sw1",a0) 
 (SPEC_V("sw2",b0) (SPEC_V ("sw3",c0) (SPEC_V("sw4",d0) SWAP_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac SWAP_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "swap01" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("sw1",a0) 
 (SPEC_V("sw2",b0) (SPEC_V ("sw3",c0) (SPEC_V("sw4",d0) SWAP_01))))))) 
[IMP_REWRITE_TAC [spec_thm_tac SWAP_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "swap11" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("sw1",a0) 
 (SPEC_V("sw2",b0) (SPEC_V ("sw3",c0) (SPEC_V("sw4",d0) SWAP_11))))))) 
[IMP_REWRITE_TAC [spec_thm_tac SWAP_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "swap10" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "swap01" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "swap00" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "swap11" (fun thm-> ALL_TAC);;