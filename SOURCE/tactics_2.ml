(* ========================================================================= *)
(*                                                                           *)
(*                           tactics_2.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: December 31, 2017                                            *)
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
 

(****************************************************************************************)