(* ========================================================================= *)
(*                                                                           *)
(*                 tensor_product_projection.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "tensor_product.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 

let goal_num_cases = prove(
`!P. (!n. P n) <=> (P 0 /\ (!n. P (SUC n))) `,
MESON_TAC[num_CASES]);;

let COMPLEX_SUB_ONE_RDISTRIB = prove
 (`!x y z.   z - y * z = (Cx(&1) - y) * z `,
  SIMPLE_COMPLEX_ARITH_TAC);;
  
let COMPLEX_MUL_ONE_INV = prove
 (`!w z.  ~(w = Cx(&0)) ==> (Cx(&1) =  inv w * z  <=> w = z)`,
  CONV_TAC COMPLEX_FIELD);;
    
(*---------------------- Linear Projection-----------------------*)     
    
let proj_def = new_definition `!sm m x.
(proj (fock sm m)) x = (r_inprod (fock sm m) x) % (fock sm m)`;;


let RINPROD_RADD = prove( `!f g z.
 f IN sq_integrable /\ g IN sq_integrable /\ z IN sq_integrable
==> r_inprod z (f + g) = r_inprod z f + r_inprod z g`,
ONCE_SIMP_TAC[GSYM CNJ_INJ] THEN
SIMP_TAC[CNJ_ADD;RINPROD_CNJ;RINPROD_LADD;
SQ_INTEGRABLE_SUBSPACE;CFUN_SUBSPACE_ADD]);;
    
    
let RINPROD_LSMUL = prove( `!f g a.
f IN sq_integrable /\ g IN sq_integrable
 ==> r_inprod (a % f) g = (cnj a) * r_inprod f g `,
ONCE_SIMP_TAC[GSYM CNJ_INJ] THEN
SIMP_TAC[CNJ_CNJ;CNJ_MUL;RINPROD_CNJ;RINPROD_RSMUL;
SQ_INTEGRABLE_SUBSPACE;CFUN_SUBSPACE_SMUL]);;
    
let proj_linearity = prove(
 `! sm m.  is_sm6 sm ==>
 (!x y a. x IN sq_integrable /\ y IN sq_integrable ==>  
((proj (fock sm m))  (x + y)  =
        (proj (fock sm m)) x +
        (proj (fock sm m)) y
        /\ (proj (fock sm m)) (a % x) =
                   a % ((proj (fock sm m)) x)))`,
 SIMP_TAC [proj_def] THEN
SIMP_TAC[RINPROD_RADD;FOCK_IN_S;CFUN_ADD_RDISTRIB] THEN
SIMP_TAC[RINPROD_RSMUL;FOCK_IN_S;GSYM CFUN_SMUL_ASSOC]);;


let FOCK_PROJ_N = prove(`!sm n. is_sm6 sm 
 ==> (proj (fock sm n)) (fock sm n) = (fock sm n)`,
MESON_TAC[proj_def;FOCK_QST;is_qst;CFUN_SMUL_LID]);;

let FOCK_INPRO_N_M = prove (` is_sm6 sm /\ ~(n = m) ==> 
r_inprod (fock sm n) (fock sm m) = Cx(&0) ` ,
REPEAT STRIP_TAC THEN SUBGOAL_THEN 
`(are_orthogonal1 (sq_integrable,r_inprod) (fock sm n) (fock sm m)) ` 
ASSUME_TAC THENL [REPEAT (POP_ASSUM MP_TAC) THEN 
IMP_REWRITE_TAC[MESON[GSYM CX_INJ;REAL_OF_NUM_EQ] 
`(n = m)  <=> (Cx(&n) = Cx(&m))`] THEN 
ONCE_ASM_REWRITE_TAC[MESON[FOCK_EIGEN_PAIR] `is_sm6 sm  <=> 
 (is_sm6 sm /\ is_eigen_pair_unbounded (dh2 sm) (phn sm) (fock sm n,Cx (&n)) /\
 is_eigen_pair_unbounded (dh2 sm) (phn sm) (fock sm m,Cx (&m)))`] THEN
 IMP_REWRITE_TAC [FOCK_IN_S;N_SELF_ADJ;SM_SQ_INTEGRABLE_INNER_SPACE;
HERM_EGF_ORTHOGONAL];REPEAT (POP_ASSUM MP_TAC) THEN 
IMP_REWRITE_TAC[are_orthogonal;SM_SQ_INTEGRABLE_INNER_SPACE;FOCK_IN_S]]) ;;



(*---------------------- Tensor Product Projection-----------------------*)  



 let is_tensor_pro =  define` 
is_tensor_pro (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex))
 <=> (!(modes1:bqs^N) modes2 n.  
  is_linear_cop (m_modes_pro (tensor n (modes1))) /\
 (m_modes_pro (tensor n modes1)) (tensor n modes2) =
  (tensor n (lambda i. ((proj (modes1$i)) (modes2$i)))))`;;
  
  
  let PRO_TENSOR_CFUN = prove
(`!(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)) 
(modes1:bqs^N) modes2 n. is_tensor_pro m_modes_pro
 ==>  (m_modes_pro (tensor n modes1)) (tensor n modes2) =
  (tensor n ((lambda i. ((proj (modes1$i)) (modes2$i))):bqs^N))`,
   SIMP_TAC[is_tensor_pro]);; 
   
let PRO_TENSOR_LINEAR = prove(`
!(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)) 
  (modes:bqs^N) n. is_tensor_pro m_modes_pro  ==>  
is_linear_cop (m_modes_pro (tensor n (modes)))`,
   SIMP_TAC[is_tensor_pro]);;   

let tensor_proj_zero = prove( 
 `!k m1 m2 n sm modes. is_tensor_pro (m_modes_pro) 
 /\ modes1$k = (fock sm m1)  /\ (n+1) <= dimindex (:N)
/\  is_sm sm /\ modes2$k = (fock sm m2) 
/\ k <= (n+1) /\ 0 < k /\ ~(m1=m2)  ==>
(m_modes_pro (tensor (n+1) (modes1:bqs^N))) 
(tensor (n+1) (modes2:bqs^N)) = K (Cx (&0))`,
let lemma = MESON [LAMBDA_BETA;CONJ_ACI;ARITH_RULE 
` (n+1) <= dimindex (:N) /\ k <= (n+1) /\ 0 < k ==>
k <= dimindex (:N) /\ 1 <= k `] 
`((modes2:bqs^N)$k = (fock sm m2) /\
modes1$k = (fock sm m1) /\ (n+1) <= dimindex (:N) 
/\ k <= (n+1) /\ 0 < k  ==>
((lambda i. (proj (modes1$i)) (modes2$i)):bqs^N)$k 
= (proj (fock sm m1))  (fock sm m2))` in
(REPEAT GEN_TAC) THEN SIMP_TAC [PRO_TENSOR_CFUN] 
THEN REPEAT (STRIP_TAC) THEN 
SUBGOAL_THEN `((modes1:bqs^N)$k = (fock sm m1)  
/\ (n+1) <= dimindex (:N) /\  
is_sm sm /\ (modes2:bqs^N)$k = (fock sm m2) 
/\ k <= (n+1) /\ 0 < k /\ ~(m1=m2)) ==>
(((lambda i. (proj (modes1$i)) (modes2$i)):bqs^N)$k  
= cfun_zero )` ASSUME_TAC THENL [IMP_REWRITE_TAC[MESON 
[FOCK_INPRO_N_M; proj_def;CFUN_SMUL_LZERO] 
`(is_sm sm /\ ~(m1=m2) ==> 
 (proj (fock sm m1))  (fock sm m2) = cfun_zero )`;
 lemma;CONJ_ACI]; REPEAT (POP_ASSUM MP_TAC) 
THEN IMP_REWRITE_TAC[mode_zero_tensor]]);;
    
    
let theorem_n_equiv = prove(` (!n. P (n+1)) 
 <=> (!n. 1 <= n ==> P n)`,MESON_TAC[num_CASES;
 NOT_SUC;ARITH_RULE `(1 <= n) <=> ~(n = 0)`;GSYM ADD1]);;
     
     
let proj_tensor_m_n = prove(`!(n:num).  
1 <= n /\ m+n <= dimindex (:N) /\ is_tensor_pro (m_modes_pro)  ==>
(m_modes_pro (tensor (m+n) (modes1:bqs^N))) (tensor (m+n) (modes2:bqs^N))
=  (\y:real^N. (((m_modes_pro (tensor m modes1)) (tensor m modes2)) y) * 
(((m_modes_pro (tensor n ((lambda i. modes1$(i+m)):bqs^N))) 
(tensor n ((lambda i. modes2$(i+m)):bqs^N))) ((lambda i. y$(i+m)):real^N)))`,
let lemma = prove( `m + n <= dimindex (:N) ==> (( (if i <= n /\ 1 <= i then 
((lambda i. proj (modes1$i) (modes2$i)):bqs^N)$(i + m) else g i) = 
if i <= n /\ 1 <= i then proj (modes1$(i + m)) (modes2$(i + m)) else g i) /\
((if (i <= n /\ 1 <= i) then proj (((lambda i. modes1$(i + m)):bqs^N)$i) 
(((lambda i. modes2$(i + m)):bqs^N)$i) else g i) = if (i <= n /\ 1 <= i) 
then proj (modes1$(i + m)) (modes2$(i + m)) else g i))`  ,
ASM_MESON_TAC[LAMBDA_BETA;ARITH_RULE 
`(m + n <= dimindex (:N) /\ i <= n /\ 1 <= i) ==> 
(1 <= i /\ i <= dimindex (:N) /\ 1 <= (i + m) 
/\ i + m <= dimindex (:N)) `] ) in
IMP_REWRITE_TAC[PRO_TENSOR_CFUN;tensor_nmlem1;
MESON[ARITH_RULE `m + n <= dimindex (:N) <=> 
(m + n <= dimindex (:N) /\  n <= dimindex (:N))`] 
`1 <= n /\ m + n <= dimindex (:N) /\ 
is_tensor_pro m_modes_pro <=> (1 <= n /\ m + n <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\  n <= dimindex (:N))`] THEN 
ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN IMP_REWRITE_TAC [lemma]);;