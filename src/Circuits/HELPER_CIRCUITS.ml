(* ========================================================================= *)
(*                                                                           *)
(*                      HELPER_CIRCUITS.ml                                   *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: December 18, 2017                                            *)
(*                                                                           *)
(* ========================================================================= *)

(* 8 * 4 +  2 * 4 + 4 * 2 + 12 * 8  = 32+16+96=144*)
(*3 * 8 + 4 * 2 + 2 = 34 CZ gates *)

let CIRCUIT3 = define 
`CIRCUIT3 ((a0:sm), (a1:sm), (a2:sm), (a3:sm), 
(i0:sm), (h1:sm), (g2:sm), (i3:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=>  
(?(b1:sm)  (b0:sm) ( c0 :sm) (b2:sm) ( c1:sm) ( d0:sm) ( c2:sm) ( e0:sm) ( f0:sm) ( b3:sm) 
(d2:sm) ( g0:sm) ( e2:sm) ( e1:sm) ( c3:sm) ( f2:sm) ( d3:sm) ( f1:sm) ( e3:sm) 
(g1:sm) ( f3:sm) ( h3:sm) ( d1:sm)  ( h0:sm) .
SWAP_GATE(a0,a1,b1,b0,ten,LH,LV,m_modes_pro) /\
V2_GATE(b0,a2,c0,b2,ten,LH,LV,m_modes_pro) /\
V_GATE(b1,c0,c1,d0,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d0,b2,c2,e0,ten,LH,LV,m_modes_pro) /\
V2_GATE(e0,a3,f0,b3,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(c1,c2,d1,d2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d2,f0,g0,e2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d1,g0,h0,e1,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(e2,b3,c3,f2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(e1,c3,d3,f1,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(d3,f1,e3,g1,ten,LH,LV,m_modes_pro) /\
V2_STAR_GATE(h0,e3,i0,f3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(f3,g1,h1,h3,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(h3,f2,g2,i3,ten,LH,LV,m_modes_pro))` ;;


let CIRCUIT_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;CIRCUIT3] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test17.txt" [] [("V_GATE",2);("V2_GATE",2);("V2_STAR_GATE",2)] 0))  
(extract_port [] "(ad1,0,ad2,1,ad3,1,ad4,0)" 0 0) 4) 4 0 0 [("V_GATE",VG_tac);("V2_GATE",VG2_tac);("V2_STAR_GATE",VG2_STAR_tac)];;


let circuit3_1111 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4
          ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
    Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT_TAC);;


let circuit3_1110 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4
          (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT_TAC);;

                          
let circuit3_1101 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4
          (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT_TAC);;
                          
let circuit3_1100 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_1011 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_1010 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1 then LV ad5 else if i = 2
then LV ad6 else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_1001 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
                          
                          
let circuit3_1000 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_0111 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
let circuit3_0110 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT_TAC);;

let circuit3_0101 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_0100 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4  (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
                          
let circuit3_0011 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT_TAC);;
                    
let circuit3_0010 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
let circuit3_0001 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT_TAC);;
                          
let circuit3_0000 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT3 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &295147905179352825856) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT_TAC);;
                         

let circuit3_tac l = 
 SUBGOAL_TAC "circuit3_0000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0000))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0000] THEN CFUN_ARITH_TAC] THEN 
 SUBGOAL_TAC "circuit3_0001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0001))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0010))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0011))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0100))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0101))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0110))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit3_0111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit3_0111))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit3_0111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "circuit3_0000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "circuit3_0100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit3_0111" (fun thm-> ALL_TAC) ;;   

(* ========================================================================= *)
(* 8 * 4 +  2 * 4 + 4 * 2 + 12 * 4  = 96*)
(*3 * 4 + 4 * 2 + 2 = 22 CZ gates *)

let CIRCUIT1 = define 
`CIRCUIT1 ((a0:sm), (a1:sm), (a2:sm), (a3:sm), 
(i0:sm), (f1:sm), (f2:sm), (c3:sm),
(ten:qop^N->(real^N->complex)-> (real^N->complex)), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=>  
(? (b1:sm) (b0:sm) (c0:sm) (b2:sm) (c1:sm) (d0:sm) (c2:sm) (e0:sm) (f0:sm) 
(b3:sm) (d2:sm) (g0:sm) (e2:sm) (e1:sm) (d1:sm) (h0:sm).
SWAP_GATE(a0,a1,b1,b0,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b0,a2,b2,c0,ten,LH,LV,m_modes_pro) /\
V2_GATE(c0,a3,d0,b3,ten,LH,LV,m_modes_pro) /\ 
V_GATE(b2,d0,c2,e0,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c2,e0,f0,d2,ten,LH,LV,m_modes_pro) /\
V_GATE(b1,f0,c1,g0,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(d2,b3,e2,c3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c1,g0,h0,d1,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(d1,e2,e1,f2,ten,LH,LV,m_modes_pro) /\ 
V2_STAR_GATE(h0,e1,i0,f1,ten,LH,LV,m_modes_pro))` ;;


let CIRCUIT1_TAC = REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;CIRCUIT1] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
quantum_tac (matrix_procedure [] ((gate_matrix "test18.txt" [] [("V_GATE",2);("V2_GATE",2);("V2_STAR_GATE",2)] 0))  
(extract_port [] "(ad1,0,ad2,1,ad3,1,ad4,0)" 0 0) 4) 4 0 0 [("V_GATE",VG_tac);("V2_GATE",VG2_tac);("V2_STAR_GATE",VG2_STAR_tac)];;

   
let circuit1_1111 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4
          ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
 tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT1_TAC);;


let circuit1_1110 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4
          (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT1_TAC);;

                          
let circuit1_1101 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
let circuit1_1100 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_1011 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_1010 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_1001 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
                          
                          
let circuit1_1000 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LV (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_0111 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
let circuit1_0110 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT1_TAC);;

let circuit1_0101 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4  (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_0100 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LV (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4  (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT1_TAC);;
                          
                          
let circuit1_0011 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LV ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LV ad8)`,CIRCUIT1_TAC);;
                    
let circuit1_0010 = prove( `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LV (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LH ad8)`,CIRCUIT1_TAC);;
                          
let circuit1_0001 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LV (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LV ad6
                          else if i = 3 then LV ad7 else LV ad8)`,CIRCUIT1_TAC);;
                          
let circuit1_0000 = prove(  `!(ad1:sm) (ad2:sm) (ad3:sm) (ad4:sm)  (ad5:sm) (ad6:sm) (ad7:sm) (ad8:sm)
(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CIRCUIT1 (ad1,ad2,ad3,ad4,ad5,ad6,ad7,ad8,ten,LH,LV,m_modes_pro)
==>
tensor 4 ((lambda i. if i = 1 then LH (ad1) 
else  if i = 2 then LH (ad2) else if i = 3 then 
LH (ad3) else LH (ad4) ):bqs^N) =     
Cx (&1 / &17592186044416) %
tensor 4 (lambda i. if i = 1
                     then LH ad5
                     else if i = 2
                          then LH ad6
                          else if i = 3 then LH ad7 else LH ad8)`,CIRCUIT1_TAC);;
                         

let circuit1_tac l = 
 SUBGOAL_TAC "circuit1_0000" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0000))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0000] THEN CFUN_ARITH_TAC] THEN 
 SUBGOAL_TAC "circuit1_0001" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0001))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0001] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0010" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0010))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0010] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0011" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0011))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0011] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0100" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0100))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0100] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0101" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0101))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0101] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0110" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0110))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0110] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "circuit1_0111" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("ad1",(List.nth l 0))
(SPEC_V ("ad2",(List.nth l 1)) (SPEC_V ("ad3",(List.nth l 2)) (SPEC_V("ad4",(List.nth l 3)) 
(SPEC_V ("ad5",(List.nth l 4)) (SPEC_V("ad6",(List.nth l 5)) (SPEC_V ("ad7",(List.nth l 6)) 
(SPEC_V("ad8",(List.nth l 7)) circuit1_0111))))))))))) 
[IMP_REWRITE_TAC [spec_thm_tac circuit1_0111] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "circuit1_0000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "circuit1_0100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_0111" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "circuit1_1000" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1001" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1010" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1011" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "circuit1_1100" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1101" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1110" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "circuit1_1111" (fun thm-> ALL_TAC);;   

