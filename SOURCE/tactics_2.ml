(* ========================================================================= *)
(*                                                                           *)
(*                           tactics_2.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: October 24, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "FREDKIN_GATE.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 
(****************************************************************************************)

let rec tab_red i mem_list = 
 let len = (int_of_string (List.nth mem_list 2)) in
  if (i < 2 * len) then
    (List.nth mem_list (3+i)) :: (tab_red (i+1) mem_list)
 else [];;

let rec rewrite_gates_tac l i (new_circuits) =
       let len = List.length l in
       let mem_list k = (List.nth (List.nth l i) k) in
       if (i < len)  then
         if ((mem_list 1) = "FLIP_GATE") then
           (flip_tac (mem_list 3) (mem_list 4)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "HADAMARD_GATE") then
           (hadamard_tac (mem_list 3) (mem_list 4)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "CZ_GATE") then
          (cz_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6)) THEN 
            (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "CNOT1_GATE") then
           (cnot1_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "CNOT2_GATE") then
           (cnot2_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "SWAP_GATE") then
           (swap_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "TS_GATE") then
           (ts_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6) (mem_list 7) (mem_list 8)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "TOFFOLI1_GATE") then
           (toffoli1_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6) (mem_list 7) (mem_list 8)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "TOFFOLI3_GATE") then
           (toffoli3_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6) (mem_list 7) (mem_list 8)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else if ((mem_list 1) = "FREDKIN1_GATE") then
           (fredkin1_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6) (mem_list 7) (mem_list 8)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
         else  if (List.mem_assoc (mem_list 1) new_circuits) then
         ((List.assoc (mem_list 1) new_circuits) (tab_red 0 (List.nth l i))) THEN  
         (rewrite_gates_tac l (i+1) new_circuits)
         else 
           (fredkin3_tac (mem_list 3) (mem_list 4) (mem_list 5) (mem_list 6) (mem_list 7) (mem_list 8)) THEN 
           (rewrite_gates_tac l (i+1) new_circuits)
        else REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[IMP_IMP];;

(****************************************************************************************)

rewrite_decompose_tac  52 [28;12;4;3;3;2] 0 0

rew_condition 52 [28;12;4;3;3;2] 0

condition_recompose 52 [28;12;4;3;3;2]
let lgenerat2 = generat2 52 (rev [28;12;4;3;3;2])

(mk_eq ((parse_term (String.concat ""  ("(if i <= " :: 
    (get_suc 52) :: " /\ SUC 0 <= i then " :: 
    (make_fst_cond [28;12;4;3;3;2] 0 0) @ (main_make_concl [28;12;4;3;3;2] 0 0) @ [" g i):A"]))), (main_make_cond 52 52))),
	
	
	(mk_eq ((parse_term (String.concat ""  ("(if i <= " :: 
    (get_suc 12) :: " /\ SUC 0 <= i then " :: 
    (make_fst_cond [4;3;3;2] 0 0) @ (main_make_concl [4;3;3;2] 0 0) @ [" g i):A"]))), (main_make_cond 12 12)))
    let lgenerat2 = generat2 12 (rev [4;3;3;2])

rew_condition 15 [3;4;3;3;2] 0

(ASM_SIMP_TAC ([ARITH_RULE `~(i <= j) ==> (((i:num) - j = 0) <=> (i = 0 + j))`;
    LAMBDA_BETA] @ (map (REWRITE_RULE [SUB_0]) 
    (map ARITH_RULE (rewrite_recompose 52 [28;12;4;3;3;2] 0 0)))))

   main_tab_gates [["0"; "CNOT2_GATE"; "2"; "a2"; "b5"; "a3"; "b6"; "ten"; "LH"; "LV";
     "pro"];
    ["2"; "SWAP_GATE"; "2"; "c4"; "d1"; "d2"; "c5"; "ten"; "LH"; "LV"; "pro"]] 4
[ quantum_sub_tac [["6"; "F_ADDER"; "4"; "a1"; "b1"; "c0"; "d0"; "d01"; "c1"; "f0"; "s1"]] 10 [("F_ADDER",full_adder_tac)];
    quantum_sub_tac [["6"; "SWAP_GATE"; "2"; "d01"; "c1"; "c11"; "d02"]] 10 [("F_ADDER",full_adder_tac)];
    quantum_sub_tac [["5"; "SWAP_GATE"; "2"; "d1"; "c11"; "c12"; "d11"]] 10 [("F_ADDER",full_adder_tac)];
    quantum_sub_tac [["3"; "F_ADDER"; "4"; "a2"; "b2"; "c12"; "d11"; "d12"; "c2"; "f1"; "s2"]] 10 [("F_ADDER",full_adder_tac)];
   [["3"; "SWAP_GATE"; "2"; "d12"; "c2"; "c21"; "d13"]];
   [["2"; "SWAP_GATE"; "2"; "d2"; "c21"; "c22"; "d21"]];
   [["0"; "F_ADDER"; "4"; "a3"; "b3"; "c22"; "d21"; "d22"; "c3"; "f2"; "s3"]]]
(quantum_tac (matrix_procedure [] ((gate_matrix "test11.txt" [] [("F_ADDER",4)] 0))  
(extract_port [] "(a3,0,b3,0,d2,0,a2,1,b2,1,d1,0,a1,1,b1,0,c0,0,d0,0)" 0 0) 4) 10 0 [("F_ADDER",full_adder_tac)]);;
	
let quantum_sub_tac l m new_circuits =   
    let ll = main_tab_gates [["6"; "F_ADDER"; "4"; "a1"; "b1"; "c0"; "d0"; "d01"; "c1"; "f0"; "s1"]] 10 in
    let len = List.length [6;4] in
    ASM_SIMP_TAC ([(main_comp_inputs [6;4] 10);tensor_nmlem1] @ 
    (one_less 10)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l [6;4]) THEN
    rewrite_decompose_tac  10 [6;4] 0 0 THEN
	rewrite_decompose 10 [6;4] 0 0
    rew_condition_tac  10 [6;4]  0 THEN
 m <= dimindex (:N)
g `10 <= dimindex (:N) ==>
((\y. tensor 4  ((lambda i. if i <= 4 /\ 1 <= i then (lambda k. f k)$(i + 6) else g i):bqs^N) y) = 
(\y. tensor 4  ((lambda i. if i <= 4 /\ 1 <= i then f (i + 6) else g i):bqs^N) y))`
IMP_REWRITE_TAC [LAMBDA_BETA;ARITH_RULE `(10 <= dimindex (:N) ==> (i <= 4 ==> i + 6 <= dimindex (:N)))` ;ARITH_RULE `1 <= i + 6`]
ASM_SIMP_TAC ([K_DEF;LAMBDA_BETA]@ map ARITH_RULE (rewrite_decompose 10 [6;4] 0 0))
let rec MAP_AND (l:thm list) (i:int) = 
    let len = List.length l in 
	if (i<len) then ((List.nth l i) /\ (MAP_AND l (i+1))) else ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F))`;;

time e((ASM_SIMP_TAC ([ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F))`;
    SIMP_RULE [ARITH_RULE ` 1<= i+6`] (SPEC_V ("i","i+6") LAMBDA_BETA)] @ map ARITH_RULE (rewrite_decompose 10 [6;4] 0 0))) THEN CONV_TAC NUM_REDUCE_CONV);;
ARITH_RULE `((10 <= dimindex (:N) ==> i <= 4) ==> i + 6 <= dimindex (:N))` /\ 1 <= i + 6`

let helpper = prove(`10 <= dimindex (:N) ==> i <= 4 ==> ((lambda) (g:num->bqs^N)$(i + 6) = (g:num->bqs^N) (i + 6))`, 
REPEAT (STRIP_TAC) THEN
MP_TAC (ARITH_RULE `(10 <= dimindex (:N) ==> i <= 4 ==> i + 6 <= dimindex (:N))`) THEN
ASM_SIMP_TAC ([SIMP_RULE [ARITH_RULE ` 1<= i+6`] (SPEC_V ("i","i+6")  (ISPECL [`g:num->bqs^N`] (GEN_ALL (LAMBDA_BETA))))]));; 
ISPECL [`g:num->bqs^N`] thm
	CPU time (user): 79.120972
tensor 10 (if i
g `10 <= dimindex (:N) /\ i <= 4	==> (lambda) (g:num->bqs^N)$(i+6) = (g:num->bqs^N) (i+6)`
	let hellper = prove(` 1 <= i /\ i <= dimindex (:N) ==>  (lambda j. g:nbqs^N)$i = g i`, 
	SIMP_TAC [LAMBDA_BETA; ARITH_RULE `(10 <= dimindex (:N) ==> i <= 4 ==> i + 6 <= dimindex (:N)) /\ 1 <= i + 6`]);;

	CPU time (user): 79.98884
time e((IMP_REWRITE_TAC ([ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F))`;
    LAMBDA_BETA] @ map ARITH_RULE (rewrite_decompose 10 [6;4] 0 0))) THEN CONV_TAC NUM_REDUCE_CONV);;
(SPEC_V ("i","i+6")	
let rec MAP_MP (l:tactic list) (i:int) = 
    let len = List.length l in 
	if (i<len) then ((List.nth l i) THEN (MAP_MP l (i+1))) else ALL_TAC
	(rewrite_decompose 17 [6;4;2;3;2] 0 0)
MAP_MP  MP_TAC (ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F)) /\ (10 <= dimindex (:N) ==> i <= 4 ==> i + 6 <= dimindex (:N)) /\
      `)] @ map ARITH_RULE (rewrite_decompose 10 [6;4] 0 0))) 0 THEN 
       ASM_REWRITE_TAC[SPEC_V ("i","i+6") LAMBDA_BETA;MESON[] ` (a ==> b ==> c) <=> (a /\ b ==> c)`]
	   
    ASM_SIMP_TAC (map GSYM (rewrite_l [6;4])) THEN
    STRIP_TAC THEN (rewrite_gates_tac [["6"; "F_ADDER"; "4"; "a1"; "b1"; "c0"; "d0"; "d01"; "c1"; "f0"; "s1"]] 0 [("F_ADDER",full_adder_tac)]) THEN
    SIMP_TAC[CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
    COMPLEX_ADD_LDISTRIB;
    COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
    SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] THEN
    SIMP_TAC ((GSYM CX_MUL) :: (rewr_dev 2 0)) THEN
    SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) =
    a % (\y. f1 y)  `;CFUN_ADD_LEMBDA;CFUN_SUB_LEMBDA] THEN
    (if len = 1 then ALL_TAC else
    IMP_REWRITE_TAC[GSYM (main_comp_inputs [6;4] 10);
    REWRITE_RULE[FUN_EQ_THM] tensor_mnlem;ARITH]) THEN 
    ONCE_SIMP_TAC (rewrite_l [10]) THEN 
    rewrite_recompose_tac  10 [6;4] 0 0 THEN
    SIMP_TAC[condition_recompose 10 [6;4]] THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l [10])) ;;
	
Cx (sqrt (&1 / &2)) %
     (cexp (--ii * Cx (pi / &4)) %
      (Cx (&1 / &4) %
       (cexp (ii * Cx (pi / &4)) %
        (Cx (&1 / &4) %
         (Cx (sqrt (&1 / &2)) %
          (\y. tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) y) +
          Cx (sqrt (&1 / &2)) %
          (\y. tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) y)))))) +
     Cx (sqrt (&1 / &2)) %
     (cexp (--ii * Cx (pi / &4)) %
      (Cx (&1 / &4) %
       (cexp (--ii * Cx (pi / &4)) %
        (Cx (&1 / &4) %
         (Cx (sqrt (&1 / &2)) %
          (\y. tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) y) -
          Cx (sqrt (&1 / &2)) %
          (\y. tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) y))))))
		  
(Cx (sqrt (&1 / &2)) *
      cexp (--ii * Cx (pi / &4)) *
      Cx (&1 / &4) *
      cexp (ii * Cx (pi / &4)) *
      Cx (&1 / &4)) %
     (Cx (sqrt (&1 / &2)) %
      (\y. tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) y) +
      Cx (sqrt (&1 / &2)) %
      (\y. tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) y)) +
     (Cx (sqrt (&1 / &2)) *
      cexp (--ii * Cx (pi / &4)) *
      Cx (&1 / &4) *
      cexp (--ii * Cx (pi / &4)) *
      Cx (&1 / &4)) %
     (Cx (sqrt (&1 / &2)) %
      (\y. tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) y) -
      Cx (sqrt (&1 / &2)) %
      (\y. tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) y)) =
     (Cx (&1 / &16) * Cx (&1 / sqrt (&2)) * cexp (ii * Cx (pi / &4))) %
     (\y. tensor 2 (lambda i. if i = 1 then LV t1 else LV c1) y) +
     (Cx (&1 / &16) * Cx (&1 / sqrt (&2)) * cexp (--(ii * Cx (pi / &4)))) %
     (\y. tensor 2 (lambda i. if i = 1 then LH t1 else LV c1) y)	
	 
let quantum_sub_tac l m new_circuits =   
    let ll = main_tab_gates l m in
    let len = List.length ll in
    ASM_SIMP_TAC ([(main_comp_inputs ll m);tensor_nmlem1] @ 
    (one_less m)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l ll) THEN
    rewrite_decompose_tac  m ll 0 0 THEN
    rew_condition_tac  m ll  0 THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l ll)) THEN
    STRIP_TAC THEN (rewrite_gates_tac l 0 new_circuits) THEN
    SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;
CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
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

let quantum_sub_tac12 l m new_circuits =   
    let ll = main_tab_gates l m in
    let len = List.length ll in
    ASM_SIMP_TAC ([(main_comp_inputs ll m);tensor_nmlem1] @ 
    (one_less m)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l ll) THEN
    rewrite_decompose_tac  m ll 0 0 THEN
    rew_condition_tac  m ll  0 THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l ll))
	
let quantum_sub_tac12 l m new_circuits =   
    let ll = main_tab_gates l m in
    let len = List.length ll in
    ASM_SIMP_TAC ([(main_comp_inputs ll m);tensor_nmlem1] @ 
    (one_less m)) THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_SIMP_TAC (rewrite_l ll) THEN
    rewrite_decompose_tac  m ll 0 0 THEN
    rew_condition_tac  m ll  0 THEN
    ASM_SIMP_TAC (map GSYM (rewrite_l ll)) THEN
    STRIP_TAC THEN (rewrite_gates_tac l 0 new_circuits) THEN
    SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;
CFUN_ADD_THM;CFUN_SUB_THM;COMPLEX_ADD_RDISTRIB;
    COMPLEX_ADD_LDISTRIB;
    COMPLEX_SUB_RDISTRIB;COMPLEX_SUB_LDISTRIB] THEN
    SIMP_TAC [GSYM COMPLEX_MUL_ASSOC] 


let pisum_thm k = prove( (parse_term (String.concat "" 
("Cx(y)*x+Cx(&("::(string_of_int (k))::")*y)*x=Cx(&("::(string_of_int (k+1))::[")*y)*x"]))),
SIMP_TAC[GSYM REAL_OF_NUM_ADD;REAL_ADD_RDISTRIB;CX_ADD;COMPLEX_ADD_RDISTRIB;
SIMP_RULE[ADD1] ((num_CONV o mk_small_numeral)(k+1)); REAL_MUL_LID;COMPLEX_ADD_AC] );;
		

let rec pisum n k = 
          if (k < n) then   (pisum_thm k) :: (pisum n (k+1))
		  else [(COMPLEX_FIELD (parse_term (String.concat "" ["x + x = Cx(&2) * x"])))];;

let pisum_thm2 k = SIMP_RULE [REAL_MUL_LID] (prove( (parse_term (String.concat "" 
("Cx(y)*x+ --(Cx(&("::(string_of_int (k))::")*y)*x)= --(Cx(&("::(string_of_int (k-1))::[")*y)*x)"]))),
SIMP_TAC[GSYM REAL_OF_NUM_ADD;REAL_ADD_RDISTRIB;CX_ADD;COMPLEX_ADD_RDISTRIB;
SIMP_RULE[ADD1] ((num_CONV o mk_small_numeral)(k)); REAL_MUL_LID;COMPLEX_ADD_AC;] 
THEN CONV_TAC COMPLEX_FIELD));;
		

let rec pisum2 n k = if (k < n) then   (pisum_thm2 k) :: (pisum2 n (k+1))
else [(COMPLEX_FIELD (parse_term (String.concat "" ["x + x = Cx(&2) * x"])))];;


let pisum_thm3 k = SIMP_RULE [REAL_MUL_LID] (prove( (parse_term (String.concat "" 
("(Cx(&("::(string_of_int (k))::")*y)*x) + --(Cx(y)*x) = (Cx(&("::(string_of_int (k-1))::[")*y)*x)"]))),
SIMP_TAC[GSYM REAL_OF_NUM_ADD;REAL_ADD_RDISTRIB;CX_ADD;COMPLEX_ADD_RDISTRIB;
SIMP_RULE[ADD1] ((num_CONV o mk_small_numeral)(k)); REAL_MUL_LID;COMPLEX_ADD_AC;] 
THEN CONV_TAC COMPLEX_FIELD));;
		

let rec pisum3 n k = if (k < n) then   (pisum_thm3 k) :: (pisum3 n (k+1))
else [(COMPLEX_FIELD (parse_term (String.concat "" ["x + x = Cx(&2) * x"])))];;


    
let rec quantum_tac L m i k new_circuits =
    let len = List.length L in
    if (i < len)  then 
      if (i=0) then
          REPEAT GEN_TAC THEN integer_equiv m THEN
          (quantum_sub_tac (List.nth L i) m new_circuits) THEN 
          (quantum_tac L m (i+1) (k + List.length (List.nth L i)) new_circuits)
       else
       (quantum_sub_tac (List.nth L i) m new_circuits) 
       THEN (quantum_tac L m (i+1) (k + List.length (List.nth L i)) new_circuits)
    else 
SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB; 
CFUN_ADD_AC;CFUN_SUB_AC;GSYM CFUN_ADD_RDISTRIB_NEW;CFUN_SMUL_LZERO] THEN 
SIMP_TAC((pisum3 k 2) @ (pisum2 k 2) @ (pisum k 1) @ [CEXP_NEG_RMUL;CEXP_NEG_LMUL;GSYM CEXP_ADD;
COMPLEX_MUL_AC;GSYM CX_ADD;GSYM CX_MUL;COMPLEX_ADD_AC;
COMPLEX_ADD_LINV;COMPLEX_ADD_RINV;COMPLEX_SUB_REFL;COMPLEX_MUL_LNEG;
COMPLEX_SUB_LDISTRIB;COMPLEX_SUB_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_ADD_RDISTRIB;
GSYM COMPLEX_NEG_ADD;COMPLEX_NEG_NEG;
COMPLEX_MUL_RNEG;MESON[CX_MUL; COMPLEX_MUL_ASSOC] 
` Cx((y1:real)) * Cx(y2) * (x2: complex) = Cx(y1 * y2) * x2`;
GSYM CX_SUB]) THEN SIMP_TAC[REAL_FIELD `(&6 * pi / & 4) =  &3 * pi / &2 /\ 
(&2 * pi / & 4) =  pi / &2 /\ (&4 * pi / & 4) =  pi` ] THEN 
SIMP_TAC[CEXP_II_PI2_CNJ;CEXP_II_PI2;CEXP_II_PI4;CEXP_II_PI4_CNJ;
CEXP_II_PI_CNJ;CEXP_II_PI;COMPLEX_FIELD `x * ii = ii * x`]	
THEN SIMP_TAC[thm4;GSYM CFUN_ADD_RDISTRIB;GSYM CFUN_SUB_RDISTRIB;CFUN_ADD_LID;
CFUN_ADD_RID;CFUN_SUB_LDISTRIB;CFUN_SUB_NEG;GSYM CFUN_SMUL_LNEG;
CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_ADD;GSYM CX_MUL; 
GSYM CX_SUB;CFUN_ADD_AC;CFUN_SUB_AC;REAL_ADD_AC;REAL_SUB_REFL;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;GSYM CFUN_ADD_RDISTRIB_NEW;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG] THEN SIMP_TAC[COMPLEX_MUL_AC;GSYM CX_ADD;GSYM CX_MUL;
COMPLEX_ADD_LINV;COMPLEX_ADD_RINV;COMPLEX_SUB_REFL;COMPLEX_MUL_LNEG;
COMPLEX_SUB_LDISTRIB;COMPLEX_SUB_RDISTRIB;
COMPLEX_ADD_LDISTRIB;COMPLEX_ADD_RDISTRIB;
GSYM COMPLEX_NEG_ADD;COMPLEX_NEG_NEG;
COMPLEX_MUL_RNEG] THEN SIMP_TAC[thm4;GSYM CX_ADD;GSYM CX_MUL;COMPLEX_MUL_RZERO; 
GSYM CX_SUB;REAL_ADD_AC;REAL_SUB_REFL;COMPLEX_MUL_LZERO;
REAL_NEG_NEG;GSYM CX_NEG;REAL_ADD_LINV;REAL_SUB_RZERO;REAL_ADD_RINV;
REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;
REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;REAL_MUL_LNEG;
CFUN_SMUL_LZERO;CFUN_ADD_LID;CFUN_ADD_RID;CFUN_SUB_RID] THEN
SIMP_TAC[REAL_POW_DIV;SQRT_DIV;SQRT_1;REAL_MUL_AC;
GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG;COMPLEX_MUL_RZERO;COMPLEX_MUL_LZERO;
CFUN_SMUL_LZERO;CFUN_ADD_LID;CFUN_ADD_RID;CFUN_SUB_RID] THEN 
SIMP_TAC[thm5;REAL_POW_DIV;SQRT_DIV;SQRT_1;
GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_POW_ONE;REAL_MUL_RNEG;
CFUN_SMUL_LZERO;REAL_MUL_RID;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;
REAL_MUL_LNEG;COMPLEX_MUL_RZERO;COMPLEX_MUL_LZERO;
CFUN_SMUL_LZERO;CFUN_ADD_LID;CFUN_ADD_RID;CFUN_SUB_RID] THEN
CONV_TAC REAL_RAT_REDUCE_CONV THEN 
CONV_TAC NUM_REDUCE_CONV THEN TRY(CFUN_ARITH_TAC);;
    
	
let thm4 =  prove( ` ii * x = x * ii /\
x * ii * y =  (x*y) * ii  /\ x * y * ii  = (x*y) * ii  /\
x * --ii * y =  (x*y) * --ii  /\ x * y * --ii  = (x*y) * --ii  /\
x * ii + y * ii = (x + y) * ii /\  x * ii + y * --ii = (x - y) * ii /\
x * --ii + y * ii = (y - x) * ii /\ x * --ii + y * --ii = (x + y) * --ii`,
SIMP_TAC[COMPLEX_MUL_AC;COMPLEX_MUL_LNEG;COMPLEX_MUL_RNEG;GSYM COMPLEX_POW_2;COMPLEX_POW_II_2;COMPLEX_MUL_LID] THEN 
CONV_TAC COMPLEX_FIELD);;

let thm5 =  prove( ` (&x / sqrt(&y)) * &z = &z * (&x / sqrt(&y)) /\ 
(&x / sqrt(&y)) * &z * (v:real) = &z * (&x / sqrt(&y)) * v /\
(&x / sqrt(&y)) * (&z / &t) = (&z / &t) * (&x / sqrt(&y)) /\
 (&x / sqrt(&y)) * (&z / &t) * v = (&z / &t) * (&x / sqrt(&y)) * v  `, 
CONV_TAC REAL_FIELD);;

let thm5 =  prove( `x = y ==> cexp (x) = cexp (y)`,SIMP_TAC[]);;



(****************************************************************************************)