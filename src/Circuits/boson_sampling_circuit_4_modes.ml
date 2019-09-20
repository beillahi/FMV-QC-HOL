(* ========================================================================= *)
(*                                                                           *)
(*                  boson_sampling_circuit_4_modes.ml                        *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2019                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "../Tactics/tactics_1.ml";;


(*----------------- Common Tactics --------------------------*)

let complex_simp_tactic1 = SIMP_TAC[thm4;GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
COMPLEX_NEG_ADD;COMPLEX_NEG_LMUL;COMPLEX_NEG_NEG;
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG] ;;
let complex_simp_tactic2 =  SIMP_TAC[thm4;GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
COMPLEX_NEG_ADD;COMPLEX_NEG_LMUL;COMPLEX_NEG_NEG;
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG] THEN SIMP_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2 ;
MESON[CX_MUL;CX_ADD; COMPLEX_MUL_ASSOC;COMPLEX_ADD_AC;COMPLEX_MUL_AC] 
` Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x2 /\ 
x1 * Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x1 * x2 /\ 
x1 * Cx((y1:real)) * Cx(y2)  = Cx(y1 * y2) * x1 /\ 
 Cx((y1:real)) + Cx(y2) + (x2: complex) = Cx(y1 + y2)  + x2 /\
  (x2: complex) +  Cx((y1:real)) + Cx(y2) = Cx(y1 + y2)  + x2 /\
x1 + Cx((y1:real)) + Cx(y2) + (x2: complex) = Cx(y1 + y2)  + x1 + x2`;
COMPLEX_MUL_AC;GSYM CX_ADD;GSYM CX_MUL;COMPLEX_MUL_RID;
COMPLEX_ADD_AC;complex_sub;
COMPLEX_ADD_LINV;COMPLEX_ADD_RINV;COMPLEX_SUB_REFL;COMPLEX_MUL_LNEG;
COMPLEX_SUB_LDISTRIB;COMPLEX_SUB_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_ADD_RDISTRIB;REAL_NEG_NEG;
COMPLEX_NEG_ADD;COMPLEX_NEG_NEG;
COMPLEX_MUL_RNEG];;
let complex_simp_tactic3 =  SIMP_TAC[COMPLEX_POW_II_2; GSYM COMPLEX_POW_2 ;
MESON[CX_MUL;CX_ADD; COMPLEX_MUL_ASSOC;COMPLEX_ADD_AC;COMPLEX_MUL_AC] 
` Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x2 /\ 
x1 * Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x1 * x2 /\ 
x1 * Cx((y1:real)) * Cx(y2)  = Cx(y1 * y2) * x1 /\ 
 Cx((y1:real)) + Cx(y2) + (x2: complex) = Cx(y1 + y2)  + x2 /\
  (x2: complex) +  Cx((y1:real)) + Cx(y2) = Cx(y1 + y2)  + x2 /\
x1 + Cx((y1:real)) + Cx(y2) + (x2: complex) = Cx(y1 + y2)  + x1 + x2`;
COMPLEX_MUL_AC;GSYM CX_ADD;GSYM CX_MUL;COMPLEX_MUL_RID;
COMPLEX_ADD_AC;complex_sub;
COMPLEX_ADD_LINV;COMPLEX_ADD_RINV;COMPLEX_SUB_REFL;COMPLEX_MUL_LNEG;
COMPLEX_SUB_LDISTRIB;COMPLEX_SUB_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_ADD_RDISTRIB;REAL_NEG_NEG;
COMPLEX_NEG_ADD;COMPLEX_NEG_NEG;
COMPLEX_MUL_RNEG];;
   
let condition_new_thm n1 n3 l1 l2 = 
    let rec make_concl n i l = if (i<n) then 
        "if i = " :: (string_of_int (List.nth l i)) :: " then x" :: 
        (string_of_int (List.nth l i)) :: " else " :: (make_concl n (i+1) l) 
        else "xi" :: " else " :: ["g i):A"] in
    let make_cond0 n1 n2 l1 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl n2 0 l1) in
    let make_cond n1 n2 l2 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl n2 0 l2) in
    let main_make_cond n1 n2 l1 = parse_term (String.concat "" (make_cond n1 n2 l1)) in 
    let main_make_cond0 n1 n2 l2 = parse_term (String.concat "" (make_cond0 n1 n2 l2)) in 
    (prove( (mk_eq ((main_make_cond0 n1 n3 l1), (main_make_cond n1 n3 l2))), 
    conditionThm0Tac n1));;
	
let condition0_recompose0 m l lk1 lk2 = 
    let rec make_concl1 n i lk = if (i<n) then 
        "if i = " :: (string_of_int (List.nth lk i)) :: " then x" :: (string_of_int i) :: 
        " else " :: (make_concl1 n (i+1) lk) 
        else  "x" :: (string_of_int i) :: " else " :: ["g i):A"] in
    let make_cond1 n1 n2 lk = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl1 n2 0 lk) in
    let main_make_cond n1 n2 lk = parse_term (String.concat "" (make_cond1 n1 n2 lk)) in
    let rec make_concl n i lk j = if (i<n) then 
        "if i = " :: (string_of_int (List.nth lk i)) :: " then x" :: 
        (string_of_int j) :: " else " :: (make_concl n (i+1) lk (j+1)) 
        else  "x" :: (string_of_int (j)) :: [""] in
    let rec main_make_concl l i lk j = 
        let len1 = List.length l in
		let len2 = List.length l in
            if (i<len1 or i<len2) then
                (make_concl (List.length (List.nth lk i)) 0 (List.nth lk i) j) @ [" else " ] @ 
                (main_make_concl l (i+1) lk (j+(List.length (List.nth lk i))))
            else [] in
        let rec make_fst_cond l i k = 
            let len = List.length l in
            if (i<(len-1)) then
            (make_fst_cond l (i+1) (k+(List.nth l i))) @ 
            ("if i <= " :: (string_of_int (k+(List.nth l i))) :: " then ":: []) 
            else [""] in
   (prove( (mk_eq ((parse_term (String.concat ""  ("(if i <= " :: 
    (string_of_int m) :: " /\ 1 <= i then " :: 
    (make_fst_cond l 0 0) @ (main_make_concl l 0 lk1 0) @ [" g i):A"]))), (main_make_cond m (List.length lk2) lk2))),
   condRecomposeTac 0 0 l));;
 
let condition0_recompose01 m l lk1 lk2 = 
    let rec make_concl1 n i lk = if (i<n) then 
        "if i = " :: (string_of_int (List.nth lk i)) :: " then x" :: (string_of_int (List.nth lk i)) :: 
        " else " :: (make_concl1 n (i+1) lk) 
        else  "x" :: (string_of_int 0) :: " else " :: ["g i):A"] in
    let make_cond1 n1 n2 lk = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl1 n2 0 lk) in
    let main_make_cond n1 n2 lk = parse_term (String.concat "" (make_cond1 n1 n2 lk)) in
    let rec make_concl n i lk j = if (i<n) then 
        "if i = " :: (string_of_int (List.nth lk i)) :: " then x" :: 
        (string_of_int (List.nth lk i)) :: " else " :: (make_concl n (i+1) lk (j+1)) 
        else  "x" :: (string_of_int 0) :: [""] in
    let rec main_make_concl l i lk j = 
        let len1 = List.length l in
		let len2 = List.length l in
            if (i<len1 or i<len2) then
                (make_concl (List.length (List.nth lk i)) 0 (List.nth lk i) j) @ [" else " ] @ 
                (main_make_concl l (i+1) lk (j+(List.length (List.nth lk i))))
            else [] in
        let rec make_fst_cond l i k = 
            let len = List.length l in
            if (i<(len-1)) then
            (make_fst_cond l (i+1) (k+(List.nth l i))) @ 
            ("if i <= " :: (string_of_int (k+(List.nth l i))) :: " then ":: []) 
            else [""] in
   (prove( (mk_eq ((parse_term (String.concat ""  ("(if i <= " :: 
    (string_of_int m) :: " /\ 1 <= i then " :: 
    (make_fst_cond l 0 0) @ (main_make_concl l 0 lk1 0) @ [" g i):A"]))), (main_make_cond m (List.length lk2) lk2))),
   condRecomposeTac 0 0 l));;
    
(***********************************************************)

(*------------------------ helper theorems--------------------- -----------*)

(***********************************************************)


let thm1 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$3)) 2
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 2 then  fock (e$3) 1 else (if i = 3 then fock (e$2) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm2 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$2)) 3
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 3 then  fock (e$2) 1 else (if i = 2 then fock (e$3) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm0 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$2)) 3
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$3)) 2
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm2;thm1] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [2;3] [3;2])]);;


let thm11 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$2)) 3
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 3 then  fock (e$2) 1 else (if i = 1 then fock (e$4) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm21 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$4)) 1
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 1 then  fock (e$4) 1 else (if i = 3 then fock (e$2) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm01 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$2)) 3
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$4)) 1
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))` ,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm21;thm11] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [1;3] [3;1])]);;


let thm12 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$1) = vac (e$4) /\vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 4 then  fock (e$1) 1 else (if i = 3 then fock (e$2) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm22 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$2)) 3
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 3 then  fock (e$2) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm02 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$2)) 3 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$2)) 3
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm22;thm12] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [3;4] [4;3])]);;

let thm13 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$1) = vac (e$4) /\vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$3)) 2
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 2 then  fock (e$3) 1 else (if i = 1 then fock (e$4) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm23 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$4)) 1
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 1 then  fock (e$4) 1 else (if i = 2 then fock (e$3) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm03 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$3)) 2
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$4)) 1
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm23;thm13] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [1;2] [2;1])]);;


let thm14 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2) /\ vac (e$1) = vac (e$4) /\vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 4 then  fock (e$1) 1 else (if i = 2 then fock (e$3) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm24 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\ is_sm (e$2)  /\ 
  vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$3)) 2
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 2 then  fock (e$3) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm04 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\ is_sm (e$2)  /\ 
 vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$3)) 2 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$3)) 2
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm24;thm14] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [2;4] [4;2])]);;
           
let thm15 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\ is_sm (e$2) /\ 
 vac (e$1) = vac (e$4) /\vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 4 then  fock (e$1) 1 else (if i = 1 then fock (e$4) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm25 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$4)) 1
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N))) =
tensor 4 ((lambda i. if i = 1 then  fock (e$4) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))):bqs^N)`,
REWRITE_TAC[pos] THEN REPEAT STRIP_TAC THEN 
ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
           THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
           THEN MULTI_MODE_DECOMPOSE_TAC 
           THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
           SIMP_TAC[GSYM ONE] THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID]);;
           
let thm05 = prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)).  
 4 <= dimindex (:N) /\ is_tensor ten /\ is_sm (e$1) /\ is_sm (e$4) /\ is_sm (e$3) /\
 is_sm (e$2)  /\ vac (e$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) ==>
pos ten (cr (e$1)) 4
     (pos ten (cr (e$4)) 1 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))= 
pos ten (cr (e$4)) 1
     (pos ten (cr (e$1)) 4 (tensor 4 ((lambda j. vac (e$4)):bqs^N)))`,
REPEAT STRIP_TAC THEN ASM_SIMP_TAC[thm25;thm15] THEN 
ONCE_ASM_SIMP_TAC [(ISPECL [mk_numeral (Int 4)] tensor_1mlem1d)] THEN 
ASM_SIMP_TAC[(condition_new_thm 4 2 [1;4] [4;1])]);;


(**************************************************************************************)


let thm_help0 = (prove(`
(4 <= dimindex (:N) /\ is_tensor ten /\
Boson_four_Circuit2 (a,e,ten))  ==> (vac (e$1) = vac (e$4) /\ 
vac (e$2) = vac (e$4) /\ vac (e$3) = vac (e$4) )`,
REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_four_Circuit2] THEN 
REWRITE_TAC[is_beam_splitter;pos;mirror] THEN REPEAT STRIP_TAC THEN
ASM_MESON_TAC[]));;


(*------------------------Circuit Definition---------------------*)

let Boson_four_Circuit2 = new_definition 
`Boson_four_Circuit2 ((a:sm^N), (e:sm^N), 
(ten:qop^N->(real^N->complex)-> (real^N->complex)))  
<=>  (? (b:sm^N) (c:sm^N) (d:sm^N).
mirror (ten,a$1,1,b$1,1) /\
mirror (ten,b$2,1,c$2,1) /\
mirror (ten,c$3,1,d$3,1) /\
mirror (ten,d$4,1,e$4,1) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,d$3,1,c$4,2,d$4,1,e$3,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,c$2,1,b$3,2,c$3,1,d$2,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,d$2,2,b$4,3,c$4,2,e$2,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,b$1,1,a$2,2,b$2,1,c$1,2) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,c$1,2,a$3,3,b$3,2,d$1,3) /\
is_beam_splitter (--Cx((&9 / &10))*ii,Cx((&1 / &10)),--Cx((&42 / &100)),Cx((&58 / &100))*ii,ten,d$1,3,a$4,4,b$4,3,e$1,4)) `;;


(*------------------------ Goal--------------------- -----------*)


g `!(ten:qop^N->(real^N->complex)-> (real^N->complex)) (a:sm^N) (e:sm^N). 
4 <= dimindex (:N) /\ is_tensor ten /\
Boson_four_Circuit2 (a,e,ten)  ==> 
tensor 4 ((lambda i. if i = 2 then  fock (a$2) 1 else 
(if i = 3 then fock (a$3) 1  else vac (a$4))):bqs^N) =   Cx (-- &21437109 / &4882812500) %
 tensor 4 (lambda i. if i = 2 then  fock (e$3) 1 else (if i = 3 then fock (e$2) 1  else vac (e$4))) +
 Cx (-- &841 / &2500000) %
 tensor 4 (lambda i. if i = 4 then Cx (sqrt (&2)) % fock (e$1) 2 else vac (e$4)) +
 Cx (-- &8310740697 / &48828125000) %
 tensor 4 (lambda i. if i = 1 then  fock (e$4) 1 else (if i = 2 then fock (e$3) 1  else vac (e$4))) +
 Cx (-- &76299 / &15625000) %
 tensor 4 (lambda i. if i = 3 then  fock (e$2) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))) +
  Cx (&1515602907 / &9765625000) %
 tensor 4 (lambda i. if i = 1 then  fock (e$4) 1 else (if i = 3 then fock (e$2) 1  else vac (e$4))) +
 Cx (-- &153207 / &9765625) %
 tensor 4 (lambda i. if i = 3 then Cx (sqrt (&2)) % fock (e$2) 2 else vac (e$4)) +
  Cx (-- &906453 / &390625000) %
 tensor 4 (lambda i. if i = 2 then  fock (e$3) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))) +
 Cx (&26851419 / &781250000) % 
  tensor 4 (lambda i. if i = 1 then  fock (e$4) 1 else (if i = 4 then fock (e$1) 1  else vac (e$4))) +
 Cx (&41986141911 / &195312500000) %
 tensor 4 (lambda i. if i = 1 then  Cx (sqrt (&2)) % fock (e$4) 2 else vac (e$4)) +
 Cx (&735884919 / &48828125000) %
 tensor 4 (lambda i. if i = 2 then Cx (sqrt (&2)) % fock (e$3) 2 else vac (e$4)) `;;
 
 

 

 
(*------------------------ Tactics--------------------- -----------*)
 
REPEAT STRIP_TAC THEN 

SUBGOAL_THEN ` (
vac ((e:sm^N)$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ 
vac (e$3) = vac (e$4) )` ASSUME_TAC THEN


IMP_REWRITE_TAC[thm_help0] THEN 

REPEAT (POP_ASSUM MP_TAC) THEN 
REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;Boson_four_Circuit2] THEN 
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
THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID]
THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN MULTI_MODE_DECOMPOSE_TAC 
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT] THEN
SIMP_TAC[GSYM ONE] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;CFUN_SMUL_LID] THEN
ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;GSYM COP_MUL_THM] THEN
IMP_REWRITE_TAC[COP_TENSOR_LINEAR;LINCOP_MUL_DISTRIB_CLAUSES;COP_SMUL_ASSOC;COP_MUL_LSMUL;
LINCOP_ADD_MUL_LDISTRIB;LINCOP_MUL_RMUL;COP_ADD_MUL_RDISTRIB;COP_ADD_ASSOC;ARITH_LINCOP_CLAUSES]
THEN ASM_SIMP_TAC[ARITH_LINCOP_CLAUSES ;COP_TENSOR_LINEAR;CNJ_MUL;
COP_ADD_LDISTRIB;COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
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
THEN complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
REWRITE_TAC[GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!a b c. a*b+a*c+d = (a*b+a*c)+d  /\ a*b+a*c-d = (a*b+a*c)-d  /\ a*b-a*c+d = (a*b-a*c)+d`;
COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID; 
CNJ_MUL;GSYM CX_MUL;CNJ_CX;CNJ_II;GSYM CX_NEG] THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 

SUBGOAL_THEN `4 <= dimindex (:N) /\ is_tensor (ten:qop^N->(real^N->complex)->(real^N->complex))  /\ is_sm (e$1) /\ 
is_sm (e$4) /\ is_sm (e$3) /\ is_sm (e$2) 
 /\ vac ((e:sm^N)$1) = vac (e$4) /\ vac (e$2) = vac (e$4) /\ 
 vac (e$3) = vac (e$4)` ASSUME_TAC 
 
THEN ASM_SIMP_TAC[] THEN 

 ASM_SIMP_TAC[thm05;thm04;thm03;thm02;thm01; thm0] THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN 
REWRITE_TAC[CFUN_SUB_AC;CFUN_ADD_AC;GSYM CFUN_ADD_RDISTRIB_NEW] THEN
complex_simp_tactic2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CFUN_ARITH_TAC;;


let boson_four_thm1 = top_thm();;

(*--------------------------End------------------------*)
(*--------------------**********************-----------*) 
(*--------------------******
Cx (-- &841 / &2500000) %
 pos ten (cr (e$1)) 4 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (&2523 / &1562500) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (&16443 / &1562500) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (-- &98658 / &1953125) + Cx (&12776211 / &195312500) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (-- &5569225389 / &78125000000) + Cx (&6198986619 / &390625000000) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$3)) 2 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (-- &115101 / &125000000) + Cx (-- &3337929 / &3125000000) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (-- &3319137 / &312500000) + Cx (-- &158949 / &62500000) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (-- &658503 / &39062500) + Cx (-- &1827 / &1562500) * ii) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&219501 / &62500000) + Cx (&609 / &2500000) * ii) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&245439693 / &9765625000) + Cx (&15735951 / &1562500000) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&28155042153 / &390625000000) + Cx (-- &60761421 / &15625000000) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$4)) 1 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&4609521 / &3125000000) + Cx (&12789 / &125000000) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&4472512443 / &97656250000) + Cx (&561784167 / &39062500000) * ii) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$3)) 2 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&16443 / &1562500) + Cx (-- &4258737 / &312500000) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 (Cx (&345303 / &39062500) + Cx (&461646297 / &39062500000) * ii) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4))))



 Cx (-- &21437109 / &4882812500) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (-- &841 / &2500000) %
 pos ten (cr (e$1)) 4 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (-- &8310740697 / &48828125000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$3)) 2 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (-- &76299 / &15625000) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
  Cx (&1515602907 / &9765625000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (-- &153207 / &9765625) %
 pos ten (cr (e$2)) 3 (pos ten (cr (e$2)) 3 (tensor 4 (lambda j. vac (e$4)))) +
  Cx (-- &906453 / &390625000) %
 pos ten (cr (e$3)) 2 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (&26851419 / &781250000) % 
 pos ten (cr (e$4)) 1 (pos ten (cr (e$1)) 4 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (&41986141911 / &195312500000) %
 pos ten (cr (e$4)) 1 (pos ten (cr (e$4)) 1 (tensor 4 (lambda j. vac (e$4)))) +
 Cx (&735884919 / &48828125000) %
pos ten (cr (e$3)) 2 (pos ten (cr (e$3)) 2 (tensor 4 (lambda j. vac (e$4)))) 
 
                                                                  ******************)   
(****************************************************************************************)
(****************************************************************************************)
    