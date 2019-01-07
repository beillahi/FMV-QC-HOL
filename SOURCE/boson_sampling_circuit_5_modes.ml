(* ========================================================================= *)
(*                                                                           *)
(*                  boson_sampling_circuit_5_modes.ml                        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2019                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "boson_sampling_circuit_4_modes.ml";;



(*------------------------ helper theorems--------------------- -----------*)

(***********************************************************)

let thm51 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$4)) 2
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 2 then  fock (f$4) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm52 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$3)) 3
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 3 then  fock (f$3) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm50 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$3)) 3
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$4)) 2
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm52;thm51] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [2;3] [3;2])]);;


let thm511 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$3)) 3
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 3 then  fock (f$3) 1 else (if i = 1 then fock (f$5) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm521 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$5)) 1
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 1 then  fock (f$5) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm501 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$3)) 3
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$5)) 1
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))` ,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm521;thm511] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [1;3] [3;1])]);;


let thm512 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$2)) 4
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 4 then  fock (f$2) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm522 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$3)) 3
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 3 then  fock (f$3) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm502 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$2)) 4
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$3)) 3
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm522;thm512] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [3;4] [4;3])]);;

let thm513 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$4)) 2
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 2 then  fock (f$4) 1 else (if i = 1 then fock (f$5) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm523 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$5)) 1
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 1 then  fock (f$5) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm503 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor (ten:qop^N->(real^N->complex)->(real^N->complex)) /\ 
 is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$4)) 2
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$5)) 1
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm523;thm513] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [1;2] [2;1])]);;

g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (f:sm^N).
5 <= dimindex (:N) /\ is_tensor ten /\
Boson_five_Circuit(a,f,ten)  ==>
tensor 5 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$5))):bqs^N) =    
  Boson_five_Circuit_output(f,ten) `;;


let thm514 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==> 
 pos ten (cr (f$2)) 4
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 4 then  fock (f$2) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm524 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
 pos ten (cr (f$4)) 2
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 2 then  fock (f$4) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm504 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$2)) 4
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$4)) 2
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm524;thm514] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [2;4] [4;2])]);;
           
           
let thm515 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$2)) 4
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 4 then  fock (f$2) 1 else (if i = 1 then fock (f$5) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm525 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$5)) 1
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 1 then  fock (f$5) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm505 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$2)) 4
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$5)) 1
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm525;thm515] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [1;4] [4;1])]);;


           
let thm516 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 5 then  fock (f$1) 1 else (if i = 1 then fock (f$5) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm526 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$5)) 1
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 1 then  fock (f$5) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm506 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$5)) 1 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$5)) 1
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm526;thm516] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [1;5] [5;1])]);;



           
let thm517 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 5 then  fock (f$1) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm527 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$4)) 2
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 2 then  fock (f$4) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm507 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$4)) 2 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$4)) 2
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm527;thm517] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [2;5] [5;2])]);;


           
let thm518 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 5 then  fock (f$1) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm528 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$3)) 3
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 3 then  fock (f$3) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm508 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$3)) 3 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$3)) 3
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm528;thm518] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [3;5] [5;3])]);;


           
let thm519 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5)   ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 5 then  fock (f$1) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm529 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$2)) 4
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N))) =
tensor 5 ((lambda i. if i = 4 then  fock (f$2) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm509 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 5 <= dimindex (:N) /\ is_tensor ten /\ is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) ==>
pos ten (cr (f$1)) 5
     (pos ten (cr (f$2)) 4 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))= 
pos ten (cr (f$2)) 4
     (pos ten (cr (f$1)) 5 (tensor 5 ((lambda j. vac (f$5)):bqs^N)))`,
REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[thm529;thm519] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 5)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 5 2 [4;5] [5;4])]);;

(*************************************************************************)


let thm_help1 = (prove(`
(4 <= dimindex (:N) /\ is_tensor ten /\
Boson_four_Circuit2 (a,e,ten))  ==> (vac (a$4) = vac (e$4))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_four_Circuit2] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;

let thm_help3 = (prove(`
(Boson_five_Circuit2 (a,f,ten))  ==> (vac (f$1) = vac (f$5) /\ 
vac (f$2) = vac (f$5) /\  vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5))`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_five_Circuit2] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;




let thm_help2 = COP_ARITH` Cx (-- &21437109 / &4882812500) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &841 / &2500000) %
 pos ten (cr (e$1)) 4 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &8310740697 / &48828125000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$3)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &76299 / &15625000) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (&1515602907 / &9765625000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &153207 / &9765625) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (-- &906453 / &390625000) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&26851419 / &781250000) % 
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&41986141911 / &195312500000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$4)) 1 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&735884919 / &48828125000) %
pos ten (cr (e$3)) 2 (pos ten (cr (e$3)) 2 (tensor 5 (lambda j. vac (f$5)))) = 
 (Cx (-- &21437109 / &4882812500) %
 (pos ten (cr (e$3)) 2 ** (pos ten (cr (e$2)) 3 )) +
 Cx (-- &841 / &2500000) %
 (pos ten (cr (e$1)) 4 ** (pos ten (cr (e$1)) 4 )) +
 Cx (-- &8310740697 / &48828125000) %
 (pos ten (cr (e$4)) 1 ** (pos ten (cr (e$3)) 2 )) +
 Cx (-- &76299 / &15625000) %
 (pos ten (cr (e$2)) 3 ** (pos ten (cr (e$1)) 4 )) +
  Cx (&1515602907 / &9765625000) %
 (pos ten (cr (e$4)) 1 ** (pos ten (cr (e$2)) 3 )) +
 Cx (-- &153207 / &9765625) %
 (pos ten (cr (e$2)) 3 ** (pos ten (cr (e$2)) 3 )) +
  Cx (-- &906453 / &390625000) %
 (pos ten (cr (e$3)) 2 ** (pos ten (cr (e$1)) 4 )) +
 Cx (&26851419 / &781250000) % 
 (pos ten (cr (e$4)) 1 ** (pos ten (cr (e$1)) 4 )) +
 Cx (&41986141911 / &195312500000) %
 (pos ten (cr (e$4)) 1 ** (pos ten (cr (e$4)) 1)) +
 Cx (&735884919 / &48828125000) %
(pos ten (cr (e$3)) 2 ** (pos ten (cr (e$3)) 2))) (tensor 5 (lambda j. vac (f$5)))`;;




(*------------------------Circuit Definition---------------------*)

let Boson_five_Circuit2 = new_definition 
`Boson_five_Circuit2 ((a:sm^N), (f:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)))  
<=>  (? (b:sm^N) (c:sm^N) (d:sm^N) (e:sm^N).
5 <= dimindex (:N) /\ is_tensor ten /\ 
Boson_four_Circuit2 (a,e,ten) /\
mirror (ten,e$5,1,f$5,1) /\ vac (a$5) = vac (a$4) /\ 
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,e$4,1,d$5,2,e$5,1,f$4,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,e$3,2,c$5,3,d$5,2,f$3,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,e$2,3,b$5,4,c$5,3,f$2,4) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,e$1,4,a$5,5,b$5,4,f$1,5) )`;;


(*------------------------ Goal--------------------- -----------*)


g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (f:sm^N).
5 <= dimindex (:N) /\ is_tensor ten /\
Boson_five_Circuit2(a,f,ten)  ==>
tensor 5 ((lambda i. if i = 2 then  fock (a$2) 1 else
  (if i = 3 then fock (a$3) 1  else vac (a$5))):bqs^N) =    
  Cx (&5053589271 / &15625000000000) %
 tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 Cx (-- &841 / &250000000) %
  tensor 5 (lambda i. if i = 5 then Cx (sqrt (&2)) %  fock (f$1) 2 else vac (f$5))+
 Cx (-- &314654553 / &625000000000) %
 tensor 5 (lambda i. if i = 4 then Cx (sqrt (&2)) %  fock (f$2) 2   else vac (f$5)) +
  Cx (&2854723669047 / &781250000000000) %
 tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
 Cx (-- &524697 / &6250000000) %
 tensor 5 (lambda i. if i = 4 then  fock (f$2) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 Cx (-- &23366782087307001 / &3906250000000000000) %
 tensor 5 (lambda i. if i = 2 then Cx (sqrt (&2)) %  fock (f$4) 2 else vac (f$5)) +
 Cx (-- &5874616984977 / &1562500000000000) %
 tensor 5 (lambda i. if i = 3 then Cx (sqrt (&2)) %  fock (f$3) 2 else vac (f$5)) +
  Cx (-- &46084751091 / &15625000000000) %
   tensor 5 (lambda i. if i = 3 then  fock (f$3) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
  Cx (&1875860265100059 / &39062500000000000) %
 tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))) +
  Cx (&23352911966097 / &781250000000000) %
 tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
  Cx (-- &82298259 / &312500000000) %
 tensor 5 (lambda i. if i = 3 then  fock (f$3) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 Cx (-- &128776848733749951 / &1953125000000000000) %
 tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))) +
 Cx (&371029011203709 / &39062500000000000) %
 tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))) +
 Cx (&48561884721 / &15625000000000) %
 tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 Cx (&992789705736364599 / &3906250000000000000) %
 tensor 5 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (f$5) 2  else vac (f$5))   `;;
  
 
     

(*------------------------ Tactics--------------------- -----------*)

REPEAT STRIP_TAC THEN 
SUBGOAL_THEN `(vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ 
vac (f$3) = vac (f$5) /\ vac (f$4) = vac (f$5) )` ASSUME_TAC THEN 
(r 2) THEN IMP_REWRITE_TAC[thm_help3] THEN 
     
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_five_Circuit2] THEN 
integer_equiv 5 THEN REPEAT STRIP_TAC THEN 
    
ASM_SIMP_TAC ([(main_comp_inputs [4;1] 5);tensor_nmlem1] @ 
(one_less 5)) THEN CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_SIMP_TAC (rewrite_l [4;1]) THEN
rewrite_decompose_tac  5 [4;1] 0 0 THEN
rew_condition_tac  5 [4;1]  0 THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [4;1])) THEN

IMP_REWRITE_TAC[boson_four_thm1] THEN 
    
ASM_SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;
CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
ASM_SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
ASM_SIMP_TAC ((GSYM CX_MUL) :: (rewr_dev 2 0)) THEN 
ASM_SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) =
 a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
(IMP_REWRITE_TAC[GSYM (main_comp_inputs [4;1] 5);
REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
ONCE_ASM_SIMP_TAC (rewrite_l [5]) THEN 
rewrite_recompose_tac  5 [4;1] 0 0 THEN
IMP_REWRITE_TAC[thm_help1] THEN 
ASM_SIMP_TAC[condition_recompose 5 [4;1]]   THEN 
ASM_SIMP_TAC[ETA_AX;condition0_recompose0 5 [4;1] [[3];[]] [3];
condition0_recompose0 5 [4;1] [[4];[]] [4];
condition0_recompose0 5 [4;1] [[2];[]] [2];
condition0_recompose0 5 [4;1] [[1];[]] [1];
condition0_recompose01 5 [4;1] [[5];[5]] [5];
condition0_recompose0 5 [4;1] [[1;2];[]] [1;2];
condition0_recompose0 5 [4;1] [[1;4];[]] [1;4];
condition0_recompose0 5 [4;1] [[1;3];[]] [1;3];
condition0_recompose0 5 [4;1] [[2;3];[]] [2;3];
condition0_recompose0 5 [4;1] [[2;4];[]] [2;4];
condition0_recompose0 5 [4;1] [[3;4];[]] [3;4]] THEN
ASM_SIMP_TAC (map GSYM (rewrite_l [5])) THEN 

    
SUBGOAL_THEN ` (vac ((e:sm^N)$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ 
vac (e$3) = vac (e$4) )` ASSUME_TAC 

THEN IMP_REWRITE_TAC[thm_help0] THEN 

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
REWRITE_TAC[CFUN_ARITH` vac (a$5) =  vac (a$4) <=> vac (a$4) = vac (a$5)`]
THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[] THEN 

MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN MULTI_MODE_DECOMPOSE_TAC 
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN

SIMP_TAC[GSYM pos] THEN 
SIMP_TAC[thm_help2] THEN


ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;GSYM COP_MUL_THM;pos] THEN
ASM_SIMP_TAC[COP_ADD_LDISTRIB;COP_SMUL_ASSOC; GSYM  pos] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ 
a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN ASM_SIMP_TAC[pos] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        
        
IMP_REWRITE_TAC[pos;COP_TENSOR_LINEAR;LINCOP_MUL_DISTRIB_CLAUSES;COP_SMUL_ASSOC;COP_MUL_LSMUL;
LINCOP_ADD_MUL_LDISTRIB;LINCOP_MUL_RMUL;COP_ADD_MUL_RDISTRIB;COP_ADD_ASSOC;ARITH_LINCOP_CLAUSES]
THEN ASM_SIMP_TAC[ARITH_LINCOP_CLAUSES ;COP_TENSOR_LINEAR;
CNJ_MUL;COP_ADD_LDISTRIB;COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
COP_TENSOR_LINEAR;SMUL_LINCOP;ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG]
THEN REWRITE_TAC[REAL_MUL_RNEG;REAL_MUL_LNEG; REAL_NEG_NEG;CX_NEG;COMPLEX_MUL_ASSOC;COP_ADD_ASSOC] 
THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN 
ASM_SIMP_TAC[CNJ_MUL;COP_ADD_LDISTRIB;COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
COP_TENSOR_LINEAR;SMUL_LINCOP;ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
REWRITE_TAC[COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM]
THEN REWRITE_TAC[GSYM pos;CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d /\ a*b+a*c-d = (a*b+a*c)-d /\ a*b-a*c+d = (a*b-a*c)+d`;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG]
THEN complex_simp_tactic3 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic1 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV 
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV  
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
         
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 

SUBGOAL_THEN `5 <= dimindex (:N) /\ is_tensor (ten:qop^N->(real^N->complex)->(real^N->complex)) /\ 
is_sm (f$1) /\ is_sm (f$4) /\ is_sm (f$3) /\ is_sm (f$2) /\ is_sm (f$5)  
 /\ vac ((f:sm^N)$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ vac (f$3) = vac (f$5) 
 /\ vac (f$4) = vac (f$5)` ASSUME_TAC 
 
THEN ASM_SIMP_TAC[] THEN        
ASM_SIMP_TAC[thm509;thm508;thm507;thm506;thm505;thm504;thm503;thm502;thm501;thm50] THEN 


REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CFUN_ARITH_TAC;;


let boson_five_thm1 = top_thm();;

(*--------------------**********************-----------*) 
(*--------------Useless Formalization------------------*)
(*-----------
REMOVE_THEN "asm_p1" (fun thm-> ALL_TAC);;
 
REMOVE_THEN "asm_p2" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p3" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p4" (fun thm-> ALL_TAC) THEN REMOVE_THEN "asm_p11" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p12" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p20" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p21" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p22" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p23" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p24" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p31" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p32" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p33" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p34" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p35" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p42" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p43" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p44" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p45" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p46" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p53" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p54" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p55" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p56" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p57" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p62" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p63" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "asm_p64" (fun thm-> ALL_TAC) THEN 
 
HYP IMP_REWRITE_TAC "asm_p0 asm_p5 asm_p8 asm_p16 asm_p27 asm_p38 asm_p49 asm_p58 asm_p59 asm_p60 asm_p61" 
[thm509;thm508;thm507;thm506;thm505;thm504;thm503;thm502;thm501;thm50]

    
IMP_REWRITE_TAC[thm509;thm508;thm507;thm506;thm505;thm504;thm503;thm502;thm501; thm50;
MESON[] ` (vac (e$5) = vac (f$5) /\ vac (c$5) = vac (f$2) /\ 
vac (e$5) = vac (f$4) /\ vac (d$5) = vac (e$5) /\
vac (d$5) = vac (f$3) /\ vac (c$5) = vac (d$5) /\ vac (b$5) = vac (f$1) /\ vac (b$5) = vac (c$5))
==> vac (f$1) = vac (f$5) /\ vac (f$2) = vac (f$5) /\ ((vac (f$3)):bqs) = vac (f$5) /\ vac (f$4) = vac (f$5)`] THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CFUN_ARITH_TAC;;


let Boson_five_Circuit_output = new_definition 
`Boson_five_Circuit_output ((f:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex))) = 
  Cx (&36598743125 / &115964116992) %
 tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
 Cx (&36598743125 / &231928233984) %
  tensor 5 (lambda i. if i = 3 then Cx (sqrt (&2)) %  fock (f$3) 2 else vac (f$5)) + 
 Cx (&914968578125 / &1649267441664) %
  tensor 5 (lambda i. if i = 2 then Cx (sqrt (&2)) %  fock (f$4) 2  else vac (f$5)) +
 Cx (&1463949725 / &32614907904) %
  tensor 5 (lambda i. if i = 4 then Cx (sqrt (&2)) %  fock (f$2) 2  else vac (f$5)) +
 Cx (&1005046301 / &509607936) %
  tensor 5 (lambda i. if i = 5 then Cx (sqrt (&2)) %  fock (f$1) 2 else vac (f$5)) +
 (Cx (-- &1341933203125 / &1649267441664) + Cx (-- &288286328125 / &25769803776) * ii) %
  tensor 5 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (f$5) 2  else vac (f$5)) +
 (Cx (-- &115256428353125 / &8349416423424) + Cx (&646550740625 / &173946175488) * ii) %
  tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))) +
 (Cx (-- &644211571625 / &43486543872) + Cx (&137282632375 / &10871635968) * ii) %
  tensor 5 (lambda i. if i = 3 then  fock (f$3) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
 (Cx (-- &4262889745625 / &521838526464) +  Cx (&806963153125 / &86973087744) * ii) %
  tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
 (Cx (-- &209909485625 / &28991029248) + Cx (&31194266875 / &7247757312) * ii) % 
  tensor 5 (lambda i. if i = 3 then Cx (sqrt (&2)) %  fock (f$3) 2 else vac (f$5)) +
 (Cx (-- &1339016640625 / &115964116992) + Cx (-- &67994480546875 / &7421703487488) * ii) %
  tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 2 then fock (f$4) 1  else vac (f$5))) +
 (Cx (-- &2785286875 / &452984832) + Cx (&102849569375 / &14495514624) * ii) %
  tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 (Cx (-- &1064783921875 / &57982058496) +  Cx (-- &3621449234375 / &309237645312) * ii) %
  tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 3 then fock (f$3) 1  else vac (f$5))) +
 (Cx (-- &3301378671875 / &618475290624) +  Cx (&58458109375 / &77309411328) * ii) %
  tensor 5 (lambda i. if i = 2 then Cx (sqrt (&2)) %  fock (f$4) 2 else vac (f$5)) +
 (Cx (-- &536842109375 / &28991029248) +  Cx (&10515671875 / &12884901888) * ii) %
  tensor 5 (lambda i. if i = 1 then  fock (f$5) 1 else (if i = 4 then fock (f$2) 1  else vac (f$5))) +
 (Cx (&10570314545 / &2038431744) + Cx (&717890215 / &169869312) * ii) %
  tensor 5 (lambda i. if i = 4 then  fock (f$2) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 (Cx (&45629989825 / &16307453952) + Cx (&123774175 / &12582912) * ii) %
  tensor 5 (lambda i. if i = 3 then  fock (f$3) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5))) +
 (Cx (&7738019975 / &4076863488) + Cx (&12501191675 / &1358954496) * ii) %
  tensor 5 (lambda i. if i = 4 then Cx (sqrt (&2)) %  fock (f$2) 2   else vac (f$5)) +
 (Cx (&90993151375 / &130459631616) + Cx (&8344086625 / &1358954496) * ii) %
  tensor 5 (lambda i. if i = 2 then  fock (f$4) 1 else (if i = 5 then fock (f$1) 1  else vac (f$5)))`;;
  
  
  let thm_help2 = COP_ARITH`Cx (&1195061 / &884736) %
 pos ten (cr (e$1)) 4 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&206045 / &65536) + Cx (&853615 / &294912) * ii) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &25375 / &294912) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &13776875 / &2359296) + Cx (&671875 / &6291456) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &655338125 / &56623104) + Cx (&11900875 / &2359296) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &20046875 / &4194304) + Cx (-- &217421875 / &50331648) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$3)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &4592875 / &2359296) + Cx (&11900875 / &4718592) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &1074390625 / &301989888) + Cx (&3715625 / &25165824) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$3)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&9596825 / &14155776) + Cx (&14864675 / &2359296) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$1)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &8984375 / &33554432) + Cx (-- &14921875 / &8388608) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$4)) 1 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&11687725 / &14155776) + Cx (&6917225 / &1179648) * ii) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$2)) 3 (tensor 5 (lambda j. vac (f$5)))) = 
 (Cx (&1195061 / &884736) %
 (pos ten (cr (e$1)) 4 ** pos ten (cr (e$1)) 4) +
 (Cx (&206045 / &65536) + Cx (&853615 / &294912) * ii) %
 (pos ten (cr (e$2)) 3 ** pos ten (cr (e$1)) 4 ) +
 (Cx (-- &25375 / &294912) * ii) %
 (pos ten (cr (e$4)) 1 ** pos ten (cr (e$1)) 4 ) +
 (Cx (-- &13776875 / &2359296) + Cx (&671875 / &6291456) * ii) %
 (pos ten (cr (e$4)) 1 ** pos ten (cr (e$2)) 3 ) +
 (Cx (-- &655338125 / &56623104) + Cx (&11900875 / &2359296) * ii) %
 (pos ten (cr (e$3)) 2 ** pos ten (cr (e$2)) 3 ) +
 (Cx (-- &20046875 / &4194304) + Cx (-- &217421875 / &50331648) * ii) %
 (pos ten (cr (e$4)) 1 ** pos ten (cr (e$3)) 2) +
 (Cx (-- &4592875 / &2359296) + Cx (&11900875 / &4718592) * ii) %
 (pos ten (cr (e$4)) 1 ** pos ten (cr (e$1)) 4 ) +
 (Cx (-- &1074390625 / &301989888) + Cx (&3715625 / &25165824) * ii) %
 (pos ten (cr (e$3)) 2 ** pos ten (cr (e$3)) 2) +
 (Cx (&9596825 / &14155776) + Cx (&14864675 / &2359296) * ii) %
 (pos ten (cr (e$3)) 2 ** pos ten (cr (e$1)) 4) +
 (Cx (-- &8984375 / &33554432) + Cx (-- &14921875 / &8388608) * ii) %
 (pos ten (cr (e$4)) 1 ** pos ten (cr (e$4)) 1)  +
 (Cx (&11687725 / &14155776) + Cx (&6917225 / &1179648) * ii) %
 (pos ten (cr (e$2)) 3 ** pos ten (cr (e$2)) 3)) (tensor 5 (lambda j. vac (f$5)))`;;
 
 
 let thm_help4 = COP_ARITH`
 Cx (&36598743125 / &115964116992) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&36598743125 / &231928233984) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&914968578125 / &1649267441664) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$4)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&1463949725 / &32614907904) %
 pos ten (cr (f$2)) 4 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&1005046301 / &509607936) %
 pos ten (cr (f$1)) 5 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &1341933203125 / &1649267441664) +
  Cx (-- &288286328125 / &25769803776) * ii) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$5)) 1 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &115256428353125 / &8349416423424) +
  Cx (&646550740625 / &173946175488) * ii) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &644211571625 / &43486543872) +
  Cx (&137282632375 / &10871635968) * ii) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &4262889745625 / &521838526464) +
  Cx (&806963153125 / &86973087744) * ii) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &209909485625 / &28991029248) +
  Cx (&31194266875 / &7247757312) * ii) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &1339016640625 / &115964116992) +
  Cx (-- &67994480546875 / &7421703487488) * ii) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$4)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &2785286875 / &452984832) + Cx (&102849569375 / &14495514624) * ii) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &1064783921875 / &57982058496) +
  Cx (-- &3621449234375 / &309237645312) * ii) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &3301378671875 / &618475290624) +
  Cx (&58458109375 / &77309411328) * ii) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$4)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (-- &536842109375 / &28991029248) +
  Cx (&10515671875 / &12884901888) * ii) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&10570314545 / &2038431744) + Cx (&717890215 / &169869312) * ii) %
 pos ten (cr (f$2)) 4 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&45629989825 / &16307453952) + Cx (&123774175 / &12582912) * ii) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&7738019975 / &4076863488) + Cx (&12501191675 / &1358954496) * ii) %
 pos ten (cr (f$2)) 4 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 (Cx (&90993151375 / &130459631616) + Cx (&8344086625 / &1358954496) * ii) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) = 
 (Cx (&36598743125 / &115964116992) %
 (pos ten (cr (f$4)) 2 ** (pos ten (cr (f$2)) 4 )) +
 Cx (&36598743125 / &231928233984) %
 (pos ten (cr (f$3)) 3 ** (pos ten (cr (f$3)) 3 )) +
 Cx (&914968578125 / &1649267441664) %
 (pos ten (cr (f$4)) 2 **  (pos ten (cr (f$4)) 2 )) +
 Cx (&1463949725 / &32614907904) %
 (pos ten (cr (f$2)) 4 ** (pos ten (cr (f$2)) 4 )) +
 Cx (&1005046301 / &509607936) %
 (pos ten (cr (f$1)) 5 ** (pos ten (cr (f$1)) 5 )) +
 (Cx (-- &1341933203125 / &1649267441664) + Cx (-- &288286328125 / &25769803776) * ii) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$5)) 1 )) +
 (Cx (-- &115256428353125 / &8349416423424) + Cx (&646550740625 / &173946175488) * ii) %
 (pos ten (cr (f$4)) 2 **  (pos ten (cr (f$3)) 3 )) +
 (Cx (-- &644211571625 / &43486543872) + Cx (&137282632375 / &10871635968) * ii) %
 (pos ten (cr (f$3)) 3 ** (pos ten (cr (f$2)) 4 )) +
 (Cx (-- &4262889745625 / &521838526464) + Cx (&806963153125 / &86973087744) * ii) %
 (pos ten (cr (f$4)) 2 ** (pos ten (cr (f$2)) 4 )) +
 (Cx (-- &209909485625 / &28991029248) + Cx (&31194266875 / &7247757312) * ii) %
 (pos ten (cr (f$3)) 3 ** (pos ten (cr (f$3)) 3 )) +
 (Cx (-- &1339016640625 / &115964116992) + Cx (-- &67994480546875 / &7421703487488) * ii) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$4)) 2 )) +
 (Cx (-- &2785286875 / &452984832) + Cx (&102849569375 / &14495514624) * ii) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$1)) 5 )) +
 (Cx (-- &1064783921875 / &57982058496) + Cx (-- &3621449234375 / &309237645312) * ii) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$3)) 3 )) +
 (Cx (-- &3301378671875 / &618475290624) + Cx (&58458109375 / &77309411328) * ii) %
 (pos ten (cr (f$4)) 2 ** (pos ten (cr (f$4)) 2 )) +
 (Cx (-- &536842109375 / &28991029248) + Cx (&10515671875 / &12884901888) * ii) %
 (pos ten (cr (f$5)) 1 ** (pos ten (cr (f$2)) 4 )) +
 (Cx (&10570314545 / &2038431744) + Cx (&717890215 / &169869312) * ii) %
 (pos ten (cr (f$2)) 4 ** (pos ten (cr (f$1)) 5 )) +
 (Cx (&45629989825 / &16307453952) + Cx (&123774175 / &12582912) * ii) %
 (pos ten (cr (f$3)) 3 ** (pos ten (cr (f$1)) 5)) +
 (Cx (&7738019975 / &4076863488) + Cx (&12501191675 / &1358954496) * ii) %
 (pos ten (cr (f$2)) 4 ** (pos ten (cr (f$2)) 4)) +
 (Cx (&90993151375 / &130459631616) + Cx (&8344086625 / &1358954496) * ii) %
 (pos ten (cr (f$4)) 2 ** (pos ten (cr (f$1)) 5))) (tensor 5 (lambda j. vac (f$5)))`
 
 
 

  Cx (&5053589271 / &15625000000000) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &841 / &250000000) %
 pos ten (cr (f$1)) 5 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &314654553 / &625000000000) %
 pos ten (cr (f$2)) 4 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (&2854723669047 / &781250000000000) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &524697 / &6250000000) %
 pos ten (cr (f$2)) 4 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &23366782087307001 / &3906250000000000000) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$4)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &5874616984977 / &1562500000000000) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (-- &46084751091 / &15625000000000) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (&1875860265100059 / &39062500000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (&23352911966097 / &781250000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$2)) 4 (tensor 5 (lambda j. vac (f$5)))) +
  Cx (-- &82298259 / &312500000000) %
 pos ten (cr (f$3)) 3 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (-- &128776848733749951 / &1953125000000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$4)) 2 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&371029011203709 / &39062500000000000) %
 pos ten (cr (f$4)) 2 (pos ten (cr (f$3)) 3 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&48561884721 / &15625000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$1)) 5 (tensor 5 (lambda j. vac (f$5)))) +
 Cx (&992789705736364599 / &3906250000000000000) %
 pos ten (cr (f$5)) 1 (pos ten (cr (f$5)) 1 (tensor 5 (lambda j. vac (f$5))))  
  
                               ------------------------*)
(*--------------------------End------------------------*)
(*--------------------**********************-----------*) 


    
(****************************************************************************************)
    