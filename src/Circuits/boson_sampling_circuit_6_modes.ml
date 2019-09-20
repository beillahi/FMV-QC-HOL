(* ========================================================================= *)
(*                                                                           *)
(*                  boson_sampling_circuit_6_modes.ml                        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2019                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "boson_sampling_circuit_5_modes.ml";;



(*------------------------ helper theorems--------------------- -----------*)

(***********************************************************)


let thm61 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$5)) 2
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 2 then  fock (l$5) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm62 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$4)) 3
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 3 then  fock (l$4) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm60 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$4)) 3
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$5)) 2
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm62;thm61] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [2;3] [3;2])]);;


let thm611 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$4)) 3
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 3 then  fock (l$4) 1 else (if i = 1 then fock (l$6) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm621 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$6)) 1
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 1 then  fock (l$6) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm601 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$4)) 3
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$6)) 1
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))` ,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm621;thm611] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [1;3] [3;1])]);;


let thm612 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$3)) 4
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 4 then  fock (l$3) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm622 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$4)) 3
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 3 then  fock (l$4) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm602 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$3)) 4
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$4)) 3
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm622;thm612] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [3;4] [4;3])]);;

let thm613 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$5)) 2
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 2 then  fock (l$5) 1 else (if i = 1 then fock (l$6) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm623 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$6)) 1
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 1 then  fock (l$6) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm603 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$5)) 2
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$6)) 1
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm623;thm613] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [1;2] [2;1])]);;


let thm614 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==> 
 pos ten (cr (l$3)) 4
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 4 then  fock (l$3) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm624 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
 pos ten (cr (l$5)) 2
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 2 then  fock (l$5) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm604 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$3)) 4
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$5)) 2
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm624;thm614] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [2;4] [4;2])]);;
           
           
let thm615 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$3)) 4
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 4 then  fock (l$3) 1 else (if i = 1 then fock (l$6) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm625 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$6)) 1
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm605 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$3)) 4
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$6)) 1
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm625;thm615] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [1;4] [4;1])]);;


           
let thm616 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 5 then  fock (l$2) 1 else (if i = 1 then fock (l$6) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm626 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$6)) 1
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 1 then  fock (l$6) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm606 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$6)) 1
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm626;thm616] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [1;5] [5;1])]);;



           
let thm617 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 5 then  fock (l$2) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm627 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$5)) 2
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 2 then  fock (l$5) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm607 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$5)) 2
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm627;thm617] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [2;5] [5;2])]);;


           
let thm618 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 5 then  fock (l$2) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm628 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$4)) 3
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 3 then  fock (l$4) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm608 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$4)) 3
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm628;thm618] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [3;5] [5;3])]);;


           
let thm619 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 5 then  fock (l$2) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm629 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$3)) 4
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 4 then  fock (l$3) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm609 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$3)) 4
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[thm629;thm619] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [4;5] [5;4])]);;


let thm6110 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 6 then fock (l$1) 1 else (if i = 1 then fock (l$6) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6210 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$6)) 1
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 1 then  fock (l$6) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6010 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$6)) 1 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$6)) 1
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm6210;thm6110] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [1;6] [6;1])]);;



           
let thm6111 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 6 then fock (l$1) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6211 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$5)) 2
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 2 then  fock (l$5) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6011 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$5)) 2 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$5)) 2
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm6211;thm6111] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [2;6] [6;2])]);;


           
let thm6112 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 6 then fock (l$1) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6212 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$4)) 3
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 3 then  fock (l$4) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6012 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$4)) 3 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$4)) 3
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm6212;thm6112] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [3;6] [6;3])]);;


           
let thm6113 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 6 then fock (l$1) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6213 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$3)) 4
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 4 then  fock (l$3) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6013 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$3)) 4 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$3)) 4
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[thm6213;thm6113] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [4;6] [6;4])]);;
 
let thm6114 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)   ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 6 then  fock (l$1) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6214 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$2)) 5
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N))) =
tensor 6 ((lambda i. if i = 5 then  fock (l$2) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm6014 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 6 <= dimindex (:N) /\ is_tensor ten /\ is_sm (l$1) /\ is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6) ==>
pos ten (cr (l$1)) 6
     (pos ten (cr (l$2)) 5 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))= 
pos ten (cr (l$2)) 5
     (pos ten (cr (l$1)) 6 (tensor 6 ((lambda j. vac (l$6)):bqs^N)))`,
REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[thm6214;thm6114] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 6)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 6 2 [5;6] [6;5])]);;

(*-----------------------------------------------------*)

let thm_help5 = (prove(`
(Boson_six_Circuit3 (a,l,ten))  ==> (vac (l$1) = vac (l$6) /\ vac (l$2) = vac (l$6) /\ 
vac (l$3) = vac (l$6) /\ vac (l$4) = vac (l$6) /\ vac (l$5) = vac (l$6))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_six_Circuit3] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;

let thm_help6 = (prove(`
(Boson_five_Circuit2 (a,f,ten))  ==> (vac (a$5) = vac (f$5))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_five_Circuit2] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;


let thm_help4 = COP_ARITH`
  Cx (&1875860265100059 / &39062500000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$3)) 3 (tensor 6 (lambda j. vac (l$6)))) +
  Cx (&23352911966097 / &781250000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$2)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &128776848733749951 / &1953125000000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$4)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&992789705736364599 / &3906250000000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$5)) 1 (tensor 6 (lambda j. vac (l$6)))) = 
 (Cx (&1875860265100059 / &39062500000000000) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$3)) 3 )) +
  Cx (&23352911966097 / &781250000000000) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$2)) 4 )) +
 Cx (-- &128776848733749951 / &1953125000000000000) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$4)) 2 )) +
 Cx (&992789705736364599 / &3906250000000000000) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$5)) 1))) (tensor 6 (lambda j. vac (l$6)))`;;
 
(*------------------------Circuit Definition---------------------*)
 
 let Boson_six_Circuit3 = new_definition 
`Boson_six_Circuit3 ((a:sm^N), (l:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)))  
<=>  (? (b:sm^N) (c:sm^N) (d:sm^N) (e:sm^N) (f:sm^N).
6 <= dimindex (:N) /\ is_tensor ten /\ 
Boson_five_Circuit2 (a,f,ten) /\ 
boson_five_thm0110(a,f,ten) /\
mirror (ten,f$6,1,l$6,1) /\ vac (a$6) = vac (a$5) /\ 
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,f$5,1,e$6,2,f$6,1,l$5,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,f$4,2,d$6,3,e$6,2,l$4,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,f$3,3,c$6,4,d$6,3,l$3,4) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,f$2,4,b$6,5,c$6,4,l$2,5) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,f$1,5,a$6,6,b$6,5,l$1,6) )`;;


(*------------------------ Goal--------------------------------*)

g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (l:sm^N).
6 <= dimindex (:N) /\ is_tensor ten /\  
Boson_six_Circuit3 (a,l,ten)  ==>
tensor 6 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$6))):bqs^N) =  
  Cx (-- &8192330734451657409 / &4882812500000000000000) %
 tensor 6 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (l$5) 2 else vac (l$6)) +
 Cx (&10575340251395085747 / &976562500000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))) +
 Cx (&210176207694873 / &78125000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&23352911966097 / &78125000000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&142433637600420388593 / &610351562500000000000) %
 tensor 6 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (l$6) 2  else vac (l$6)) +
 Cx (&4483670787141399 / &244140625000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (&2095428329740690119 / &195312500000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (&232825369971187791 / &195312500000000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (&498185643015711 / &244140625000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) `;;
 
 

(*------------------------ Tactics--------------------- -----------*)
  
REPEAT STRIP_TAC THEN 

SUBGOAL_THEN ` (vac ((l:sm^N)$1) = vac (l$6) /\ 
vac (l$2) = vac (l$6) /\ vac (l$5) = vac (l$6) /\  
vac (l$3) = vac (l$6) /\ vac (l$4) = vac (l$6) )` ASSUME_TAC THEN

IMP_REWRITE_TAC[thm_help5] THEN 

REPEAT (POP_ASSUM MP_TAC) THEN   
     
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_six_Circuit3] THEN 
integer_equiv 6 THEN REWRITE_TAC[boson_five_thm0110] THEN REPEAT STRIP_TAC THEN 
    
ASM_SIMP_TAC ([(main_comp_inputs [5;1] 6);tensor_nmlem1] @ 
(one_less 6)) THEN CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_SIMP_TAC (rewrite_l [5;1]) THEN
rewrite_decompose_tac  6 [5;1] 0 0 THEN
rew_condition_tac  6 [5;1]  0 THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [5;1])) THEN
    

    
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
(IMP_REWRITE_TAC[GSYM (main_comp_inputs [5;1] 6);
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
ONCE_ASM_SIMP_TAC (rewrite_l [6]) THEN 
rewrite_recompose_tac  6 [5;1] 0 0 THEN
IMP_REWRITE_TAC[thm_help6] THEN 
ASM_SIMP_TAC[condition_recompose 6 [5;1]]   THEN 
ASM_SIMP_TAC[ETA_AX;condition0_recompose0 6 [5;1] [[3];[]] [3];
condition0_recompose0 6 [5;1] [[4];[]] [4];
condition0_recompose0 6 [5;1] [[2];[]] [2];
condition0_recompose0 6 [5;1] [[1];[]] [1];
condition0_recompose0 6 [5;1] [[5];[]] [5];
condition0_recompose01 6 [5;1] [[6];[6]] [6];
condition0_recompose0 6 [5;1] [[1;2];[]] [1;2];
condition0_recompose0 6 [5;1] [[1;4];[]] [1;4];
condition0_recompose0 6 [5;1] [[1;3];[]] [1;3];
condition0_recompose0 6 [5;1] [[1;5];[]] [1;5];
condition0_recompose0 6 [5;1] [[2;3];[]] [2;3];
condition0_recompose0 6 [5;1] [[2;4];[]] [2;4];
condition0_recompose0 6 [5;1] [[2;5];[]] [2;5];
condition0_recompose0 6 [5;1] [[4;5];[]] [4;5];
condition0_recompose0 6 [5;1] [[3;5];[]] [3;5];
condition0_recompose0 6 [5;1] [[3;4];[]] [3;4]] THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [6])) ;;

    
SUBGOAL_THEN ` (
vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ 
vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) )` ASSUME_TAC THEN

IMP_REWRITE_TAC[thm_help3] THEN 

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
REWRITE_TAC[CFUN_ARITH` vac (a$6) =  vac (a$5) <=> vac (a$5) = vac (a$6)`]
THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[] THEN 

MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN

SIMP_TAC[GSYM pos]

THEN SIMP_TAC[thm_help4] THEN 


ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;GSYM COP_MUL_THM;pos] THEN
ASM_SIMP_TAC[COP_ADD_LDISTRIB;COP_SMUL_ASSOC; GSYM  pos] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ 
a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN ASM_SIMP_TAC[pos] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        
(* CPU time (user): 1453.697004*)       
(*CPU time (user): 1588.76947*) 
(*CPU time (user): 792.593507*)
(*CPU time (user): 188.750306*)
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
         
(*REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN *)
        

SUBGOAL_THEN `6 <= dimindex (:N) /\ is_tensor (ten:qop^N->(real^N->complex)->(real^N->complex))  /\ is_sm (l$1) /\ 
is_sm (l$4) /\ is_sm (l$3) /\ is_sm (l$2) /\ is_sm (l$5) /\ is_sm (l$6)  
 /\ vac ((l:sm^N)$1) = vac (l$5) /\ vac (l$2) = vac (l$5) /\ 
 vac (l$3) = vac (l$5) /\ vac (l$4) = vac (l$5) /\ vac (l$5) = vac (l$6)` ASSUME_TAC 
 
THEN ASM_SIMP_TAC[] THEN  

ASM_SIMP_TAC[thm603] THEN CFUN_ARITH_TAC;;
 
(*ASM_SIMP_TAC[thm609;thm608;thm607;thm606;thm605;thm604;thm603;thm602;thm601; thm60;
thm6010;thm6011;thm6012;thm6013;thm6014] THEN 
        
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV ;;*)



let boson_six_thm1 = top_thm();;

(*--------------------**********************-----------*) 

(*---------------------------------------------------*)
(*
   To simplify the proof we define the boson_six input 
   in term of outputs which have an emplititude that 
   is bigger than 0.01
                                                       *)
(*--------------------**********************-----------*) 

let boson_six_thm0110 = new_definition
 `boson_six_thm0110 ((a:sm^N), (l:sm^N), (ten:qop^N->(real^N->complex)-> (real^N->complex))) <=>
((6 <= dimindex (:N) /\ is_tensor ten /\ Boson_six_Circuit3(a,l,ten))  ==>
tensor 6 ((lambda i. if i = 2 then  fock (a$2) 1 else (if i = 3 then fock (a$3) 1  else vac (a$6))):bqs^N) =    
 Cx (&10575340251395085747 / &976562500000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))) +
 Cx (&142433637600420388593 / &610351562500000000000) % 
 tensor 6 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (l$6) 2  else vac (l$6)) +
 Cx (&4483670787141399 / &244140625000000000) % 
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (&2095428329740690119 / &195312500000000000000) % 
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6)))) `;;
 
(*--------------Useless Formalization------------------*)
(*-----------

 Cx (-- &8192330734451657409 / &4882812500000000000000) % (*0.0016777893344156994373632*)
 tensor 6 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (l$5) 2 else vac (l$6)) +
 Cx (&10575340251395085747 / &976562500000000000000) % (*0.010829148417428567804928*)
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))) +
 Cx (&210176207694873 / &78125000000000000) % (*0.0026902554584943744*)
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&23352911966097 / &78125000000000000) % (*0.0002989172731660416*)
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&142433637600420388593 / &610351562500000000000) % (*0.2333632718445287646707712*)
 tensor 6 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (l$6) 2  else vac (l$6)) +
 Cx (&4483670787141399 / &244140625000000000) % (*0.018365115544131170304*)
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (&2095428329740690119 / &195312500000000000000) % (*0.01072859304827233340928*)
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (&232825369971187791 / &195312500000000000000) % (*0.00119206589425248148992*)
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (&498185643015711 / &244140625000000000) % (*0.002040568393792352256*)
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6)))
 
`Cx (-- &8192330734451657409 / &4882812500000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&10575340251395085747 / &976562500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&210176207694873 / &78125000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&23352911966097 / &78125000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&142433637600420388593 / &610351562500000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$6)) 1 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&4483670787141399 / &244140625000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&2095428329740690119 / &195312500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&232825369971187791 / &195312500000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&498185643015711 / &244140625000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6))))
 

 
 

  
 
 
 

  +
 Cx (&2832504412216483028493 / &12207031250000000000000) %
  +
  Cx (&5825112854364157977 / &610351562500000000000) %
  +
 Cx (&50035253134072563 / &3051757812500000000) %
  +
  Cx (&949484152412271 / &244140625000000000) %
   +
 Cx (&187765319241772983 / &48828125000000000000) %
  +
  Cx (&89136970676268757263 / &6103515625000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
  Cx (&401357166454917 / &488281250000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1034949360681 / &19531250000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6))))
 
 tensor 6 (lambda i. if i = 5 then  Cx (sqrt (&2)) % fock (l$2) 2  else vac (l$6)) +
 Cx (-- &841 / &25000000000) %
 tensor 6 (lambda i. if i = 6 then  Cx (sqrt (&2)) % fock (l$1) 2 else vac (l$6)) +
 Cx (-- &48987349986681 / &156250000000000000) %
 tensor 6 (lambda i. if i = 4 then  Cx (sqrt (&2)) % fock (l$3) 2 else vac (l$6)) +
 Cx (-- &701055169543773 / &976562500000000000) %
 tensor 6 (lambda i. if i = 3 then  Cx (sqrt (&2)) % fock (l$4) 2 else vac (l$6)) +
 Cx (&644166840807 / &2441406250000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
  Cx (-- &372099 / &312500000000 ) %
 tensor 6 (lambda i. if i = 5 then  fock (l$2) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
 Cx (-- &3411798003 / &390625000000000) %
 tensor 6 (lambda i. if i = 3 then  fock (l$4) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
  Cx (-- &276777125631 / &1953125000000000) %
 tensor 6 (lambda i. if i = 3 then  fock (l$4) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (-- &69286509303831 / &190734863281250000) %
 tensor 6 (lambda i. if i = 3 then  Cx (sqrt (&2)) % fock (l$4) 2  else vac (l$6)) + 
  Cx (-- &701055169543773 / &976562500000000000 ) %
 tensor 6 (lambda i. if i = 3 then  fock (l$4) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (-- &90676685061 / &781250000000000) %
 tensor 6 (lambda i. if i = 4 then  fock (l$3) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) + 
  Cx (-- &42926931 / &62500000000000) %
 tensor 6 (lambda i. if i = 4 then  fock (l$3) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
  Cx (&980353579202248851 / &305175781250000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (&2832504412216483028493 / &12207031250000000000000) %
 tensor 6 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (l$6) 2  else vac (l$6)) +
  Cx (&5825112854364157977 / &610351562500000000000) %
tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6)))  +
 Cx (&50035253134072563 / &3051757812500000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
  Cx (&949484152412271 / &244140625000000000) %
  tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&187765319241772983 / &48828125000000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
  Cx (&89136970676268757263 / &6103515625000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 2 then fock (l$5) 1  else vac (l$6))) +
  Cx (&401357166454917 / &488281250000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 5 then fock (l$2) 1  else vac (l$6))) +
 Cx (&1034949360681 / &19531250000000000) %
  
 
 Cx (-- &416286201276829989 / &95367431640625000000) %
 tensor 6 (lambda i. if i = 2 then  Cx (sqrt (&2)) % fock (l$5) 2 else vac (l$6)) +
 Cx (-- &1804779178240705317 / &9765625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 3 then fock (l$4) 1  else vac (l$6))) +
 Cx (-- &96799941 / &3125000000000000) %
 tensor 6 (lambda i. if i = 3 then  fock (l$4) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
 Cx (-- &219501 / &1250000000000) %
 tensor 6 (lambda i. if i = 5 then  fock (l$2) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
 Cx (-- &627907640043213 / &7812500000000000000) %
 tensor 6 (lambda i. if i = 3 then  fock (l$4) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (-- &161459037 / &15625000000000) %
 tensor 6 (lambda i. if i = 5 then Cx (sqrt (&2)) % fock (l$2) 2 else vac (l$6)) + 
 Cx (-- &9548526526174377 / &390625000000000000000) %
 tensor 6 (lambda i. if i = 1 then  fock (l$6) 1 else (if i = 4 then fock (l$3) 1  else vac (l$6))) +
 Cx (-- &841 / &25000000000) %
 pos ten (cr (l$1)) 6 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &25264784601 / &156250000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &48987349986681 / &156250000000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &1472026689 / &156250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &16574990476779 / &3906250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &4980533716306971 / &7812500000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &955128372219 / &78125000000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
 Cx (-- &253779 / &250000000000) %
 pos ten (cr (l$2)) 5 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &27197584083 / &3125000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &37585012419 / &1562500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &11860370286039 / &78125000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &69286509303831 / &190734863281250000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &143768357703 / &1562500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &323999468386913387439 / &24414062500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &433878831 / &62500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&33176093712712668549 / &9765625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&2832504412216483028493 / &12207031250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$6)) 1 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1306909060105338333 / &9765625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&6414060927687462441 / &390625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&2032798761 / &156250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&3035948771857113 / &781250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&13186060440907473 / &390625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&4609521 / &62500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&680547351091988416491 / &24414062500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&12002579310771 / &3906250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&91894896609721189299 / &9765625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1603835306199 / &156250000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&645486464423223 / &781250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1488936493493276391 / &390625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1725536263311 / &6250000000000000) %
 tensor 6 (lambda i. if i = 2 then  fock (l$5) 1 else (if i = 6 then fock (l$1) 1  else vac (l$6))) +
 Cx (&8277562086687 / &156250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) 
 
 
 Cx (-- &416286201276829989 / &95367431640625000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &1804779178240705317 / &9765625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &96799941 / &3125000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &219501 / &1250000000000) %
 pos ten (cr (l$2)) 5 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &627907640043213 / &7812500000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &161459037 / &15625000000000) %
 pos ten (cr (l$2)) 5 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &9548526526174377 / &390625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &841 / &25000000000) %
 pos ten (cr (l$1)) 6 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &25264784601 / &156250000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &48987349986681 / &156250000000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &1472026689 / &156250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &16574990476779 / &3906250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &4980533716306971 / &7812500000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &955128372219 / &78125000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &253779 / &250000000000) %
 pos ten (cr (l$2)) 5 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &27197584083 / &3125000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &37585012419 / &1562500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &11860370286039 / &78125000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &69286509303831 / &190734863281250000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &143768357703 / &1562500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &323999468386913387439 / &24414062500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &433878831 / &62500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&33176093712712668549 / &9765625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&2832504412216483028493 / &12207031250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$6)) 1 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1306909060105338333 / &9765625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&6414060927687462441 / &390625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&2032798761 / &156250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&3035948771857113 / &781250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&13186060440907473 / &390625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&4609521 / &62500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&680547351091988416491 / &24414062500000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$5)) 2 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&12002579310771 / &3906250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&91894896609721189299 / &9765625000000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1603835306199 / &156250000000000000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&645486464423223 / &781250000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$2)) 5 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1488936493493276391 / &390625000000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&1725536263311 / &6250000000000000) %
 pos ten (cr (l$6)) 1 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&8277562086687 / &156250000000000000) %
    
(****************************************************************************************)

`


 

 
 




 
let rewrite_add_cfun n = 
    let rec make_add_cfun1 n i = if (i<n) then 
        "x" :: (string_of_int i) :: " + " :: make_add_cfun1 n (i+1)
        else  "(x" :: (string_of_int i) :: " :cfun) " :: [] in
    let rec make_add_cfun2 n i = if (i<n) then 
	   if (i == 0) then "x1 + x0 + " :: make_add_cfun1 n (i+2)
	   else  "x" :: (string_of_int i) :: " + " :: make_add_cfun1 n (i+1)
        else  "(x" :: (string_of_int i) :: " :cfun) " :: [] in
   (prove( (mk_eq ((parse_term (String.concat ""  (make_add_cfun1 n 0))), (parse_term (String.concat ""  (make_add_cfun2 n 0))))),
   CFUN_ARITH_TAC));;




 

 

 
 
 
 
 
 =
 
  Cx (-- &701055169543773 / &976562500000000000 ) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &69286509303831 / &190734863281250000) %
 pos ten (cr (l$4)) 3 (pos ten (cr (l$4)) 3 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (-- &42926931 / &62500000000000) %
 pos ten (cr (l$3)) 4 (pos ten (cr (l$1)) 6 (tensor 6 (lambda j. vac (l$6)))) +
 Cx (&187765319241772983 / &48828125000000000000) %
 pos ten (cr (l$5)) 2 (pos ten (cr (l$3)) 4 (tensor 6 (lambda j. vac (l$6)))) +


 
    
(****************************************************************************************)
    