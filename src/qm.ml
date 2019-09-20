(* ========================================================================= *)
(*                                                                           *)
(*                        qm.ml                                                *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "make_tcad.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)  

let HERM_EGV_REAL = prove
  (`!s inprod op.
     is_inner_space (s,inprod) /\ is_symmetric (s,inprod) s op 
      ==> !x y. is_eigen_pair_unbounded s op (y,x) /\ y IN s ==> real x`,
  REWRITE_TAC[is_eigen_val;is_eigen_pair_unbounded;is_symmetric;is_hermitian_unbounded]
  THEN REPEAT STRIP_TAC 
  THEN Pa.SUBGOAL_TAC "lemma1"
    " inprod y (op y) = x * inprod y y"
    [ASM_MESON_TAC[INPROD_RSMUL;is_closed_by]]
  THEN Pa.SUBGOAL_TAC "lemma2"
    " inprod (op y) y = cnj x * inprod y y"
    [ASM_MESON_TAC[GSYM INPROD_CNJ;is_closed_by;INPROD_RSMUL;CNJ_MUL]]
  THEN Pa.SUBGOAL_TAC "lemma3"
    " x * inprod y y = cnj x * inprod y y"
    [ASM_MESON_TAC[]]
  THEN Pa.SUBGOAL_TAC "lemma5"
    "y IN  s ==> ~(inprod y y = Cx(&0))"
    [ASM_MESON_TAC[EQUV_ZERO;INPROD_NOT_ZERO]]
  THEN Pa.SUBGOAL_TAC "lemma6"
    " x = cnj x"
    [ASM_MESON_TAC[COMPLEX_EQ_MUL_RCANCEL]]
  THEN ASM_MESON_TAC[REAL_CNJ]);;
let COMPLEX_EQ_RCANCEL_IMP = 
  GEN_ALL (MATCH_MP (MESON [] `(p <=> r \/ q) ==> (p/\ ~r ==> q) `)
  (SPEC_ALL COMPLEX_EQ_MUL_RCANCEL));;
  
let HERM_EGF_ORTHOGONAL = prove
  (`!s inprod op.
     is_inner_space (s,inprod) /\ is_symmetric (s,inprod) s op ==>
     !x y nu mu.
       x IN s /\ y IN s /\ ~(nu = mu) /\ is_eigen_pair_unbounded s op (x,nu)
       /\ is_eigen_pair_unbounded s op (y,mu) ==>
         are_orthogonal1 (s,inprod) x y`,
  REWRITE_TAC[are_orthogonal] THEN REPEAT STRIP_TAC
  THEN MATCH_MP_TAC COMPLEX_EQ_RCANCEL_IMP
  THEN MAP_EVERY Pa.EXISTS_TAC ["cnj nu";"mu"]
  THEN CONJ_TAC 
  THENL [
    MP_REWRITE_TAC (map GSYM [INPROD_LSMUL;INPROD_RSMUL]) 
    THEN RULE_ASSUM_TAC(GSYM o REWRITE_RULE[is_eigen_pair_unbounded;is_hermitian_unbounded;is_symmetric])
    THEN ASM_SIMP_TAC[];
    ASM_MESON_TAC[REAL_CNJ;HERM_EGV_REAL]]);;