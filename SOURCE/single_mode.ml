(* ========================================================================= *)
(*                                                                           *)
(*                        single_mode.ml                                   *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "square_integrable.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)  


let is_qst = new_definition
  `is_qst x <=>
   x IN sq_integrable /\ r_inprod x x = Cx(&1)`;;

   let IS_QST_IN_SQ = prove
(`!x. is_qst x ==> x IN sq_integrable`, SIMP_TAC[is_qst]);;

let IS_QST_UNITY = prove
(`!x. is_qst x ==> r_inprod x x = Cx(&1)`, SIMP_TAC[is_qst]);;

let get_qst =  new_definition
 `get_qst v = Cx(inv(cfun_norm r_inprod v)) % v`;; 

`!sm v. is_sm sm /\ v IN sq_integrable /\ ~(cfun_norm r_inprod v = &0) 
   ==> is_qst  (get_qst v)`,
 


new_type_abbrev("bqs",`:real->complex`);;
new_type_abbrev("qop",`:bqs->bqs`);;
new_type_abbrev("sm",`:qop#qop#real#bqs`);; 

let FORALL_SM_THM = prove
  (`!P. (!sm:sm. P sm) <=> !ad a f v. P (ad,a,f,v)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let w_sm = new_definition 
  `w ((ad,a,f,v):sm) = f`;;

let planck = new_specification ["planck"]
  (prove(`?x. &0 < x`, EXISTS_TAC `&1` THEN REAL_ARITH_TAC));;

let cr_sm = new_definition
  `cr ((ad,a,f,v):sm) = ad`;;

let anh_sm = new_definition
  `anh ((ad,a,f,v):sm) = a`;;
let vac_sm = new_definition
  `vac ((ad,a,f,v):sm) = v`;;
let h_sm = new_definition
  `h (sm:sm) = Cx(planck * w sm) %
          (cr sm  ** anh sm + Cx(inv(&2)) % I)`;;

let is_sm = new_definition 
  `is_sm (sm:sm) <=>
    &0 < w sm /\ 
    (!f. is_almost_zero f <=> f = cfun_zero)  /\
    is_hermitian (sq_integrable, r_inprod) (anh sm) (cr sm)
    /\ anh sm com cr sm = I /\ is_qst (vac sm)/\ 
      is_eigen_pair (h sm ) (vac sm,Cx(planck * (w sm)/ &2))`;;

let SM_SQ_INTEGRABLE_INNER_SPACE = prove
 (`!sm. is_sm sm ==> is_inner_space (sq_integrable, r_inprod)`,
  REWRITE_TAC[is_sm;is_inner_space] THEN
  REPEAT STRIP_TAC THEN 
  ASM_SIMP_TAC[RINPROD_LADD;RINPROD_RSMUL;RINPROD_RSMUL;RINPROD_CNJ;
  RINPROD_SELF_POS;SQ_INTEGRABLE_SUBSPACE;RINPROD_ZERO_EQ]
   );;
    
    
let SM_VAC_QST = prove
  (`!sm. is_sm sm ==> is_qst (vac sm)`, 
  SIMP_TAC[is_sm]);; 
  
let SM_VAC_H_PAIR = prove
  (`!sm. is_sm sm ==>
     is_eigen_pair (h sm) (vac sm,Cx(planck * (w sm) / &2))`, 
  SIMP_TAC[is_sm]);; 



let NORMED_IS_QST = prove
( `!sm v. is_sm sm /\ v IN sq_integrable /\ ~(cfun_norm r_inprod v = &0) 
   ==> is_qst  (get_qst v)`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
  REWRITE_TAC[get_qst;is_qst] THEN 
  IMP_REWRITE_TAC[INPROD_RSMUL;INPROD_LSMUL;INNER_SPACE_SMUL] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC;CNJ_CX;GSYM CX_MUL;GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN
  IMP_REWRITE_TAC[CFUN_NORM_POW2] THEN
  TARGET_REWRITE_TAC [MESON[REAL] `real z ==> x * z = x * Cx(Re z)`]
  REAL_OF_COMPLEX_RE THEN
  IMP_REWRITE_TAC[CFUN_NORM_INPROD_0;INPROD_SELF_REAL;REAL_OF_COMPLEX_RE;
  GSYM CX_MUL;REAL_MUL_LINV] THEN  MESON_TAC[]);;

let DETERMINISTIC_MEASURE_EIGEN_STATE = prove
  (`!op st v sm.
      is_sm sm /\ is_linear_cop op 
       /\ is_qst st /\ is_eigen_pair op (st,v)
        ==> expectation r_inprod st op = v`,
  SIMP_TAC[is_qst;is_eigen_pair;expectation] 
  THEN MESON_TAC[INPROD_RSMUL;COMPLEX_MUL_RID;SM_SQ_INTEGRABLE_INNER_SPACE]);;
  
let VAC_QST_PROP = REWRITE_RULE [is_qst] SM_VAC_QST;;

(****************************************************************************)
(* ANNIHILITION AND CREATION OPERATORS                                      *)
(****************************************************************************)



let A_HERM_A_COMMUTATOR = prove
  (`!sm. is_sm sm ==> (anh sm) com (cr sm) = I`,
    SIMP_TAC[is_sm]);;
 
let HERM_A_COMMUTATOR = prove
  (`!sm. is_sm sm ==> cr sm com anh sm= --I`,
  ONCE_REWRITE_TAC[COMMUTATOR_NEG] THEN MESON_TAC[A_HERM_A_COMMUTATOR]);;

let A_HERM_A = prove
  (`!sm. 
      is_sm sm ==> 
      is_hermitian (sq_integrable, r_inprod) (anh sm) (cr sm)`,
  SIMP_TAC[is_sm]);;
    
let HERM_A_A = ONCE_REWRITE_RULE [HERM_SYM] A_HERM_A;;
    
let A_HERM_A_CLOSURE = prove
  (`!sm.
       is_sm sm ==> is_closed_by sq_integrable (anh sm)/\
     is_closed_by sq_integrable (cr sm)`, 
        ASSUME_TAC SM_SQ_INTEGRABLE_INNER_SPACE THEN
    ASM_MESON_TAC[HERM_IS_CLOSED_BY_L;HERM_IS_CLOSED_BY_R;A_HERM_A]);;
     
let A_HERM_A_LINEAR = prove
  (`!sm.
       is_sm sm ==> 
           is_linear_cop (cr sm) /\ is_linear_cop (anh sm)`,
  ASSUME_TAC SM_SQ_INTEGRABLE_INNER_SPACE THEN
  ASM_MESON_TAC[HERM_LINCOP;A_HERM_A]);;

let HERM_A_ITSELF_L = prove
(`!sm x y. is_sm sm /\ x IN sq_integrable /\ y IN sq_integrable
      ==> r_inprod (cr sm x) y = r_inprod x (anh sm y)`,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC (GSYM HERM_ITSELF)
      THEN EXISTS_TAC `sq_integrable` THEN 
      ASM_SIMP_TAC[A_HERM_A;SM_SQ_INTEGRABLE_INNER_SPACE;ETA_AX]
          THEN REPEAT(POP_ASSUM MP_TAC) THEN 
           MESON_TAC [SM_SQ_INTEGRABLE_INNER_SPACE]);;
      

let HERM_A_ITSELF_R = prove
(`!sm x y. is_sm sm /\ x IN sq_integrable /\ y IN sq_integrable
      ==>  r_inprod x (cr sm y) = r_inprod (anh sm x) y`,
      REPEAT STRIP_TAC THEN MATCH_MP_TAC  HERM_ITSELF
      THEN EXISTS_TAC `sq_integrable` THEN 
      ASM_SIMP_TAC[HERM_A_A;SM_SQ_INTEGRABLE_INNER_SPACE;ETA_AX]
           THEN REPEAT(POP_ASSUM MP_TAC) THEN 
           MESON_TAC [SM_SQ_INTEGRABLE_INNER_SPACE]);;
      
let ANNIHL_En  = prove
  (`!sm.
    is_sm sm ==> 
    !f v. ~(anh sm f = cfun_zero) /\
        is_eigen_pair  (h sm) (f,v) ==>
          is_eigen_pair (h sm) (anh sm f,v - Cx(planck*w sm))`,
  REWRITE_TAC[is_eigen_pair] THEN SIMP_TAC[]
  THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[h_sm;GSYM (REWRITE_RULE[commutator;COP_EQ_LSUB_LSUB]
   A_HERM_A_COMMUTATOR);COP_MUL_LSMUL;
   GSYM COP_MUL_THM;LINCOP_MUL_DISTRIB_CLAUSES]
   THEN ASM_SIMP_TAC[COP_ARITH 
    `!op1 op2 op3. op1 - op2 + op3 = (op1 + op3) - op2 `;
    COP_MUL_LSMUL ;GSYM LINCOP_MUL_RMUL;GSYM COP_MUL_I_SYM;
    A_HERM_A_LINEAR;COP_MUL_ASSOC]
  THEN ASM_SIMP_TAC[A_HERM_A_LINEAR;GSYM LINCOP_MUL_DISTRIB_CLAUSES;
    GSYM LINCOP_MUL_RMUL;COP_SUB_LDISTRIB ;GSYM  h_sm]
  THEN ASM_SIMP_TAC[LINCOP_MUL_DISTRIB_CLAUSES;A_HERM_A_LINEAR;
    COP_SUB_THM;LINCOP_SMUL_CLAUSES;COP_I_ID;COP_MUL;LINCOP_SMUL;
    COP_SMUL;GSYM CFUN_SUB_RDISTRIB]);;





let CREAT_En  = prove
  (`!sm.
    is_sm sm ==>
      !f v. is_qst f /\ is_eigen_pair (h sm) (f,v) ==>
          is_eigen_pair (h sm) (cr sm f,v + Cx(planck*w sm))`,
    let flat = MESON[] `(p /\ q ==> Q) <=> (p==>q==> Q)` in
    let tem thm= GEN_ALL (IMP_TRANS (SPEC_ALL SM_SQ_INTEGRABLE_INNER_SPACE) 
   (REWRITE_RULE[flat] (ISPECL [`sq_integrable`;`r_inprod`;`x:real->complex`] thm))) in 
   SIMP_TAC[is_eigen_pair;is_qst]
   THEN REPEAT STRIP_TAC THENL[
    ASM_SIMP_TAC[h_sm;GSYM COP_MUL_THM;LINCOP_MUL_DISTRIB_CLAUSES;
     COP_MUL_LSMUL;GSYM LINCOP_MUL_RMUL;GSYM COP_MUL_I_SYM;
     A_HERM_A_LINEAR;COP_MUL_ASSOC]
   THEN ASM_SIMP_TAC[A_HERM_A_LINEAR;GSYM LINCOP_MUL_DISTRIB_CLAUSES;
     GSYM LINCOP_MUL_RMUL; COP_ADD_ASSOC;
     REWRITE_RULE[commutator;COP_EQ_LSUB] A_HERM_A_COMMUTATOR]
   THEN ONCE_REWRITE_TAC[COP_ADD_LDISTRIB]
   THEN ASM_SIMP_TAC[GSYM h_sm;COP_ADD;COP_MUL;COP_SMUL;I_DEF;
     LINCOP_SMUL_CLAUSES;COP_I_ID;GSYM CFUN_ADD_RDISTRIB;
    REWRITE_RULE[is_linear_cop] A_HERM_A_LINEAR;
     COMPLEX_ADD_SYM];ALL_TAC]
    THEN  POP_ASSUM MP_TAC THEN
       IMP_REWRITE_TAC[GSYM (tem INPROD_ZERO_EQ); 
    LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]  
    THEN ASM_SIMP_TAC[HERM_A_ITSELF_R;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]
    THEN REWRITE_TAC[ 
    COP_ARITH `!f. r_inprod (anh sm (cr sm f)) f = 
        r_inprod ((anh sm ** cr sm) f) f`]
    THEN ASM_SIMP_TAC[REWRITE_RULE[commutator;COP_EQ_LSUB]
     A_HERM_A_COMMUTATOR]
    THEN  ASM_SIMP_TAC[COP_ADD_THM;I_THM;COP_MUL]
    THEN  IMP_REWRITE_TAC[INPROD_ADD_RDIST;SM_SQ_INTEGRABLE_INNER_SPACE];
     THEN ASM_SIMP_TAC[SM_SQ_INTEGRABLE_INNER_SPACE;
      LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]
    THEN ASM_SIMP_TAC[HERM_A_ITSELF_L;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx(&1) + y = Cx(&0) <=> y =  -- Cx(&1)`]
    THEN STRIP_TAC  
    THEN  ASSUME_TAC (tem INPROD_SELF_POS)
    THEN  POP_ASSUM( MP_TAC o (SPEC_V ("x","anh sm f")))
    THEN ASM_SIMP_TAC[LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE
    ;REAL_OF_COMPLEX_CX;GSYM CX_NEG]
     THEN REAL_ARITH_TAC);;

(****************************************************************************)
(* PHOTON OPERATOR                                                          *)
(****************************************************************************)

let phn_sm = new_definition 
  `phn sm = cr sm ** anh sm`;;

let N_SELF_ADJ = prove
  (`!sm.
     is_sm sm ==> is_self_adjoint (sq_integrable,r_inprod) (phn sm)`,
  REWRITE_TAC[phn_sm;is_self_adjoint]
  THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MUL_HERM
  THEN ASM_MESON_TAC[A_HERM_A;HERM_SYM;SM_SQ_INTEGRABLE_INNER_SPACE]);;

let N_CLOSURE = prove
  (`!sm.
       is_sm sm ==> is_closed_by sq_integrable (phn sm)`, 
        ASSUME_TAC SM_SQ_INTEGRABLE_INNER_SPACE THEN
    ASM_MESON_TAC[SELF_ADJ_IS_CLOSED_BY;N_SELF_ADJ]);;
  
  
let N_LINEAR = prove
  (`!sm. is_sm sm ==> is_linear_cop (phn sm)`,
  MESON_TAC[SELF_ADJ_IS_LINCOP;N_SELF_ADJ;SM_SQ_INTEGRABLE_INNER_SPACE]);;

let H_PHOTON_N = prove
  (`!sm.
      is_sm sm ==>
        h sm= Cx(planck * w sm) % (phn sm + Cx(inv(&2)) % I)`,
   SIMP_TAC[phn_sm;h_sm]);;

let EG_FUN_H_N = prove
  (`!sm.
    is_sm sm ==>
      !t st v. is_eigen_pair (h sm) (st,v) <=> 
        is_eigen_pair (phn sm) (st,
          Cx(inv(planck * w sm)) * v - Cx(inv(&2)))`,
  SIMP_TAC[is_eigen_pair;H_PHOTON_N;ADD_LINCOP;
    N_LINEAR;SMUL_LINCOP;I_LINCOP]
  THEN REWRITE_TAC[COP_SMUL;COP_ADD;I_THM;CFUN_SUB_RDISTRIB;CX_INV;
    CFUN_EQ_RSUB;GSYM CFUN_SMUL_ASSOC]
  THEN REPEAT STRIP_TAC THEN MP_REWRITE_TAC[CFUN_EQ_SMUL_LCANCEL2]
  THEN REWRITE_TAC[REAL_ENTIRE;CX_INJ]
  THEN ASM_MESON_TAC[is_sm;planck;REAL_POS_NZ]);;

let EG_FUN_N_H = prove
  (`!sm.
    is_sm sm ==>
        !t st v. is_eigen_pair (phn sm) (st,v) <=>
          is_eigen_pair (h sm) (st,
            Cx(planck * w sm) * (v + Cx(inv(&2))))`,
  SIMP_TAC[EG_FUN_H_N;GSYM CX_MUL;
    COMPLEX_MUL_ASSOC]
  THEN REPEAT STRIP_TAC THEN MP_REWRITE_TAC [REAL_MUL_LINV]
  THEN GCONV_TAC COMPLEX_POLY_CONV
  THEN ASM_MESON_TAC[is_sm;planck;REAL_POS_NZ;REAL_ENTIRE]);;
  

let ANNIHL_PHOTON  = prove
  (`!sm.
     is_sm sm ==>
      !f v. ~(anh sm f = cfun_zero) /\ 
      is_eigen_pair (phn sm ) (f,v) ==>
          is_eigen_pair (phn sm ) (anh sm  f,v - Cx(&1))`,
 SIMP_TAC[EG_FUN_N_H;COMPLEX_ADD_LDISTRIB
 ;COMPLEX_SUB_LDISTRIB;COMPLEX_MUL_RID]
 THEN MESON_TAC[COMPLEX_FIELD `((a:complex)-b)+c = (a+c)-b`;ANNIHL_En]);;













let CREAT_PHOTON = prove
(`!sm.
    is_sm sm ==>
      !f v. is_qst f /\ is_eigen_pair (phn sm) (f,v) ==>
          is_eigen_pair (phn sm) (cr sm f,v + Cx(&1))`,
 SIMP_TAC[EG_FUN_N_H;COMPLEX_ADD_LDISTRIB;COMPLEX_MUL_RID]
 THEN MESON_TAC[COMPLEX_FIELD `((a:complex)+b)+c = (a+c)+b`; CREAT_En]);;

let VAC_ZERO_PHOTON = prove
 (`!sm.
     is_sm sm ==> is_eigen_pair (phn sm) (vac sm,Cx (&0))`,
    SIMP_TAC[EG_FUN_N_H;COMPLEX_ADD_LID;
    GSYM CX_MUL;real_div;REAL_MUL_ASSOC;is_sm] THEN MESON_TAC[]);;
        
let NORM_A_VAC = prove
(`!sm.  
    is_sm sm ==> r_inprod ((anh sm) (vac sm)) ((anh sm)  (vac sm)) = Cx(&0)`, 
  REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM HERM_ITSELF;  A_HERM_A_LINEAR;LINCOP_SMUL]THEN
  MAP_EVERY Pa.EXISTS_TAC ["cr sm ";"sq_integrable"]
  THEN ASM_SIMP_TAC[GSYM COP_MUL_THM;GSYM phn_sm] THEN
   IMP_REWRITE_TAC[GSYM expectation;DETERMINISTIC_MEASURE_EIGEN_STATE;N_LINEAR;
   SM_VAC_QST;SM_SQ_INTEGRABLE_INNER_SPACE; VAC_ZERO_PHOTON; HERM_A_A]
   THEN ASM_MESON_TAC[VAC_QST_PROP;
   LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]);;   
   
let A_VAC = prove
 (`!sm. 
     is_sm sm ==> (anh sm) (vac sm) = cfun_zero`,
     REPEAT STRIP_TAC THEN
      IMP_REWRITE_TAC[GSYM INPROD_ZERO_EQ] THEN
      MAP_EVERY Pa.EXISTS_TAC ["r_inprod";"sq_integrable"] THEN POP_ASSUM MP_TAC
      THEN IMP_REWRITE_TAC[VAC_QST_PROP;NORM_A_VAC;SM_SQ_INTEGRABLE_INNER_SPACE;
   LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]);;
     
(****************************************************************************)
(* Fock State                                                               *)
(****************************************************************************)

let fock = define
  `fock sm 0 =  vac sm /\
  fock  sm (SUC n) = 
  get_qst (cr sm (fock sm n))`;;
  
let FOCK_IN_S = prove
 (`!sm.
     is_sm sm ==>  !n. fock sm n IN sq_integrable`,
 REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
 THENL[IMP_REWRITE_TAC[fock;VAC_QST_PROP];
  IMP_REWRITE_TAC[fock;get_qst;INNER_SPACE_SMUL]]
  THEN EXISTS_TAC `r_inprod` THEN IMP_REWRITE_TAC[SM_SQ_INTEGRABLE_INNER_SPACE;
  IS_CLOSED_BY_THM;A_HERM_A_CLOSURE]);;
  
let HERM_FOCK_IN_S = prove
 (`!sm.
     is_sm sm ==>  !n. ((cr sm) (fock sm n)) IN sq_integrable`,
     MESON_TAC[IS_CLOSED_BY_THM;A_HERM_A_CLOSURE;FOCK_IN_S]);;
     
let N_FOCK_IN_S = prove
 (`!sm.
     is_sm sm ==>  !n. ((phn sm ) (fock sm n)) IN sq_integrable`,
     MESON_TAC[IS_CLOSED_BY_THM;N_CLOSURE;FOCK_IN_S]);; 


let FOCK_QST = prove
 (`!n sm. is_sm sm ==>  is_qst (fock sm n)`,
        let flat = MESON[] `(p /\ q ==> Q) <=> (p==>q==> Q)` in
    let tem thm= GEN_ALL (IMP_TRANS (SPEC_ALL SM_SQ_INTEGRABLE_INNER_SPACE) 
       (REWRITE_RULE[flat] (ISPECL [`sq_integrable`;`r_inprod`;`x:real->complex`] thm))) in
       INDUCT_TAC THEN REWRITE_TAC[fock] THENL[MESON_TAC[SM_VAC_QST];ALL_TAC] THEN 
        REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
       REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
      IMP_REWRITE_TAC[IS_CLOSED_BY_THM;A_HERM_A_CLOSURE;NORMED_IS_QST;
      FOCK_IN_S;CFUN_NORM_EQ_0]
       THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN
      IMP_REWRITE_TAC[GSYM (tem INPROD_ZERO_EQ); 
    LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE;IS_QST_IN_SQ]  
    THEN IMP_REWRITE_TAC[HERM_A_ITSELF_R;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE;IS_QST_IN_SQ]
    THEN REWRITE_TAC[ 
    COP_ARITH `!f. r_inprod (anh sm (cr sm f)) f = 
        r_inprod ((anh sm ** cr sm) f) f`]
    THEN ASM_SIMP_TAC[REWRITE_RULE[commutator;COP_EQ_LSUB]
     A_HERM_A_COMMUTATOR]
    THEN  ASM_SIMP_TAC[COP_ADD_THM;I_THM;COP_MUL]
    THEN  IMP_REWRITE_TAC[INPROD_ADD_RDIST;SM_SQ_INTEGRABLE_INNER_SPACE;
    IS_QST_IN_SQ;IS_QST_UNITY;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]
    THEN IMP_REWRITE_TAC[HERM_A_ITSELF_L;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE;IS_QST_IN_SQ]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx(&1) + y = Cx(&0) <=> y =  -- Cx(&1)`]
    THEN STRIP_TAC  
    THEN  ASSUME_TAC (tem INPROD_SELF_POS)
    THEN  POP_ASSUM( MP_TAC o (SPEC_V ("x","anh sm (fock sm n)")))
    THEN ASM_SIMP_TAC[LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE;IS_QST_IN_SQ;
    REAL_OF_COMPLEX_CX;GSYM CX_NEG]
     THEN REAL_ARITH_TAC);;
           

let FOCK_EIGEN_PAIR = prove
 (`!n sm. is_sm sm 
      ==> is_eigen_pair (phn sm) (fock sm n,Cx(&n))`,
    INDUCT_TAC  THEN SIMP_TAC[fock;VAC_ZERO_PHOTON] THEN
    REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
       REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
    IMP_REWRITE_TAC[get_qst;EIGEN_PAIR_SMUL;GSYM REAL_OF_NUM_SUC;CX_ADD;
     CREAT_PHOTON;FOCK_IN_S;CFUN_NORM_EQ_0;FOCK_QST]
    THEN IMP_REWRITE_TAC[cfun_norm;HERM_A_ITSELF_R;FOCK_IN_S]
    THEN REWRITE_TAC[COP_ARITH `!f. r_inprod (anh sm (cr sm f)) f = 
        r_inprod ((anh sm ** cr sm) f) f`]
    THEN ASM_SIMP_TAC[REWRITE_RULE[commutator;COP_EQ_LSUB]
     A_HERM_A_COMMUTATOR;COP_ADD_THM;I_THM;GSYM phn_sm] THEN
    IMP_REWRITE_TAC[INPROD_ADD_RDIST;FOCK_IN_S
    ;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE;FOCK_QST;IS_QST_UNITY]
    THEN STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[is_eigen_pair]) 
    THEN ASM_SIMP_TAC[N_LINEAR] THEN 
        IMP_REWRITE_TAC[INPROD_LSMUL;FOCK_IN_S;CNJ_CX;GSYM CX_ADD
    ;FOCK_QST;IS_QST_UNITY;COMPLEX_MUL_RID;REAL_OF_COMPLEX_CX;INNER_SPACE_SMUL]
    THEN REWRITE_TAC[CX_INJ;REAL_INV_EQ_0;GSYM REAL_LT_POW_2]
    THEN MESON_TAC[(GSYM SQRT_POW2);
    REAL_ARITH ` &0 <=(&1+ &n)`;REAL_ARITH ` &0 <(&1+ &n)`]);;
    
let FOCK_EIGEN_POW_N = prove
 (`!n sm. is_sm sm 
      ==> !m. is_eigen_pair (phn sm pow m) (fock sm n,Cx(&n) pow m)`,  
          REPEAT GEN_TAC THEN REWRITE_TAC[is_eigen_pair]  
      THEN STRIP_TAC THEN INDUCT_TAC 
      THENL[ASM_SIMP_TAC[cop_pow;complex_pow;I_THM;CFUN_SMUL_LID]
      THEN  ASM_SIMP_TAC[LET_RULE_L[is_eigen_pair] FOCK_EIGEN_PAIR;N_LINEAR];
     ASM_SIMP_TAC[cop_pow;complex_pow;COP_MUL;POW_LINCOP;N_LINEAR;LINCOP_SMUL;
     LET_RULE_L[is_eigen_pair]FOCK_EIGEN_PAIR;CFUN_SMUL_ASSOC;COMPLEX_MUL_SYM]]);;



let HERM_FOCK_NORM = prove
(`!sm n.
   is_sm sm ==> 
  cfun_norm r_inprod (cr sm (fock sm n)) = sqrt(&(n+1))`,
  REWRITE_TAC[cfun_norm] THEN REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM HERM_ITSELF; A_HERM_A_LINEAR;LINCOP_SMUL]THEN
  MAP_EVERY Pa.EXISTS_TAC ["anh sm";"sq_integrable"] THEN
  MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
       REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
  ASM_SIMP_TAC[GSYM COP_MUL_THM;LET_RULE_L[commutator;COP_EQ_LSUB] A_HERM_A_COMMUTATOR;
  GSYM phn_sm;COP_MUL_ASSOC] THEN
  IMP_REWRITE_TAC[INPROD_ADD_LDIST;COP_MUL_THM;COP_ADD_THM;I_THM] THEN
  ASM_SIMP_TAC[FOCK_QST;IS_QST_IN_SQ;IS_QST_UNITY;GSYM expectation;LET_RULE_L[is_closed_by] N_CLOSURE
  ;A_HERM_A;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE] THEN
  IMP_REWRITE_TAC[DETERMINISTIC_MEASURE_EIGEN_STATE] THEN STRIP_TAC
  THEN STRIP_TAC THEN Pa.EXISTS_TAC "Cx(&n)" THEN
  ASM_SIMP_TAC[FOCK_EIGEN_PAIR;FOCK_QST;N_LINEAR;
  REAL_OF_COMPLEX_CX;GSYM CX_ADD;REAL_OF_NUM_ADD;ADD_SYM]);;
  




let ANHH_FOCK = prove
(`!n sm. 
  is_sm sm ==> 
  (anh sm ) (fock sm (SUC n)) = Cx(sqrt(& (SUC n))) % fock sm n`,
  REWRITE_TAC[fock;get_qst;cfun_norm] THEN REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM HERM_ITSELF;A_HERM_A_LINEAR;LINCOP_SMUL]THEN
  MAP_EVERY Pa.EXISTS_TAC ["anh sm)";"sq_integrable"] THEN
  MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
       REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
  ASM_SIMP_TAC[GSYM COP_MUL_THM;LET_RULE_L[commutator;COP_EQ_LSUB] A_HERM_A_COMMUTATOR;
  GSYM phn_sm;COP_MUL_ASSOC] THEN
  IMP_REWRITE_TAC[INPROD_ADD_LDIST;COP_MUL_THM;COP_ADD_THM;I_THM] THEN
  ASM_SIMP_TAC[FOCK_QST;IS_QST_IN_SQ;IS_QST_UNITY;GSYM expectation;LET_RULE_L[is_closed_by] N_CLOSURE
  ;A_HERM_A;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]THEN
  IMP_REWRITE_TAC[DETERMINISTIC_MEASURE_EIGEN_STATE] THEN STRIP_TAC
  THEN STRIP_TAC THEN MAP_EVERY Pa.EXISTS_TAC ["Cx(&n)"] THEN
   ASM_SIMP_TAC[FOCK_EIGEN_PAIR;FOCK_QST;N_LINEAR;
   LET_RULE_L[is_eigen_pair] FOCK_EIGEN_PAIR;
   REAL_OF_COMPLEX_CX;GSYM CX_ADD;CFUN_SMUL_ASSOC; 
  CFUN_ARITH `(x:cfun) + a % x = (Cx(&1) + a) % x`;GSYM CX_MUL;
  REAL_ARITH `inv (x:real) * y = y /x`;REAL_DIV_SQRT; 
  REAL_ARITH `&0 <= &n + & 1`;GSYM REAL_OF_NUM_SUC; REAL_ADD_SYM]);;
  




let CREAT_FOCK = prove
(`!n sm. 
  is_sm sm ==> 
  cr sm (fock sm  n) = Cx(sqrt(& (SUC n))) % fock sm (SUC n)`,
  REWRITE_TAC[fock;get_qst;cfun_norm] THEN REPEAT STRIP_TAC THEN
  IMP_REWRITE_TAC[GSYM HERM_ITSELF] THEN 
  MAP_EVERY Pa.EXISTS_TAC ["anh sm";"sq_integrable"] THEN
  MP_TAC (SPEC_ALL (SM_SQ_INTEGRABLE_INNER_SPACE)) THEN
       REPEAT (POP_ASSUM MP_TAC) THEN  SIMP_TAC [] THEN
  ASM_SIMP_TAC[GSYM COP_MUL_THM;LET_RULE_L[commutator;COP_EQ_LSUB] A_HERM_A_COMMUTATOR;
  GSYM phn_sm] THEN IMP_REWRITE_TAC[INPROD_ADD_LDIST;COP_MUL_THM;COP_ADD_THM;I_THM]
  THEN ASM_SIMP_TAC[FOCK_QST;IS_QST_IN_SQ;IS_QST_UNITY;GSYM expectation;LET_RULE_L[is_closed_by] N_CLOSURE
  ;A_HERM_A;LET_RULE_L[is_closed_by] A_HERM_A_CLOSURE]
  THEN IMP_REWRITE_TAC[DETERMINISTIC_MEASURE_EIGEN_STATE] THEN STRIP_TAC
  THEN STRIP_TAC THEN MAP_EVERY Pa.EXISTS_TAC ["Cx(&n)"] THEN
  ASM_SIMP_TAC[FOCK_EIGEN_PAIR;FOCK_QST;N_LINEAR;
  REAL_OF_COMPLEX_CX;GSYM CX_ADD;CFUN_SMUL_ASSOC; 
  CFUN_ARITH `(x:cfun) + a % x = (Cx(&1) + a) % x`;GSYM CX_MUL;
  REAL_MUL_RINV;SQRT_EQ_0;REAL_ARITH `&0 <= &n + &1`;
  REAL_ARITH `~(&n + &1 = &0)`;GSYM REAL_OF_NUM_SUC; REAL_ADD_SYM;CFUN_SMUL_LID]);;
    
 let FOCK_HERM_VAC = prove
  (`!sm.
    is_sm sm ==>
    !m. fock sm m = inv(Cx(sqrt(& (FACT m)))) % (cr sm pow m) (vac sm) `,
    REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC
    THEN  REWRITE_TAC[fock;cop_pow;FACT;CFUN_SMUL_LID;I_THM;SQRT_1
    ;COMPLEX_INV_1] THEN
    IMP_REWRITE_TAC[get_qst;HERM_FOCK_NORM]
    THEN  ASM_SIMP_TAC[LINCOP_SMUL;A_HERM_A_LINEAR;CFUN_SMUL_ASSOC;CX_INV;
    COMPLEX_INV_MUL;CX_MUL;SQRT_MUL;REAL_POS;GSYM REAL_OF_NUM_MUL;ADD1;COP_MUL]);;