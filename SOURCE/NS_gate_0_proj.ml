(* ========================================================================= *)
(*                                                                           *)
(*                           NS_gate_0_proj.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                             *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "tactics_1.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------*) 

(****************************************************************************)
(* Some lemmas for the analysis of NS gate                                  *)
(****************************************************************************)


let POS_ASSOC = prove
 (`!(ten:cops^N->(A^N->complex)-> (A^N->complex)) 
 (op1:cops) (op2:cops) (modes:cfun^N) n m1 m2.
   is_tensor ten /\ ~(m1=m2)==> 
   ((pos ten op1 m1) ** (pos ten op2 m2)) (tensor n modes) = 
      ((pos ten op2 m2) ** (pos ten op1 m1)) (tensor n modes)`,
       SIMP_TAC[COP_TENSOR_ASSOC;pos;COP_MUL_THM;COP_LAMBDA_COMPS;
       COND_RATOR; o_DEF;I_THM;MESON[] `~(m1:num = m2) 
       ==> (if i=m1 then y else if i=m2 then x else z)
       = (if i=m2 then x else if i=m1 then y else z)`]);;

let POS_ASSOC_4_3 = prove
 (`!(ten:cops^N->(A^N->complex)-> (A^N->complex)) (op1:cops) 
 (op2:cops) (op3:cops) (op4:cops) (modes:cfun^N) n m1 m2 m3 m4.
   is_tensor ten /\ ~(m1=m2)==> 
((pos ten op1 m1) ** (pos ten op2 m2) ** 
(pos ten op3 m3) ** (pos ten op4 m4)) (tensor n modes) = 
((pos ten op2 m2) ** (pos ten op1 m1) ** 
(pos ten op3 m3) ** (pos ten op4 m4)) (tensor n modes)`,
SIMP_TAC [pos;COP_MUL_THM] THEN ONCE_SIMP_TAC [COP_TENSOR_CFUN] 
THEN ONCE_SIMP_TAC [COP_TENSOR_CFUN] THEN
       SIMP_TAC[COP_TENSOR_ASSOC;COP_LAMBDA_COMPS;
       COND_RATOR; o_DEF;I_THM;MESON[] `~(m1:num = m2) 
       ==> (if i=m1 then y else if i=m2 then x else z)
       = (if i=m2 then x else if i=m1 then y else z)`]);;

let POS_ASSOC_1_11 = prove
 (`!(ten:cops^N->(A^N->complex)-> (A^N->complex)) (op1:cops) 
 (op2:cops) (op3:cops) (op4:cops) (modes:cfun^N) n m1 m4.
   is_tensor ten ==> 
((pos ten op1 m1) ** (pos ten op2 m1) ** (pos ten op4 m4)) (tensor n modes) = 
((pos ten (op1 ** op2) m1) ** (pos ten op4 m4)) (tensor n modes)`,
SIMP_TAC [pos;COP_MUL_THM] THEN ONCE_SIMP_TAC [COP_TENSOR_CFUN] THEN
SIMP_TAC[COP_TENSOR_ASSOC;COP_LAMBDA_COMPS;GSYM COND_ABS;COP_MUL_THM;
BETA_THM;COND_RATOR; o_DEF;I_THM;LAMBDA_ETA;REWRITE_RULE[EQ_CLAUSES]
(SIMP_CONV[o_DEF;I_THM;COND_RATOR;COND_ABS;I_DEF] 
`(if i = m2 then op2 else I) o (if i = m2 then op3 else I) = 
(if i = m2 then op2 o op3 else I)`)]);;  

let POS_ASSOC_1_1 = prove
 (`!(ten:cops^N->(A^N->complex)-> (A^N->complex)) (op1:cops) 
 (op2:cops) (op3:cops) (op4:cops) (modes:cfun^N) n m1 m3 m4.
   is_tensor ten ==> 
((pos ten op1 m1) ** (pos ten op2 m1) ** 
(pos ten op3 m3) ** (pos ten op4 m4)) (tensor n modes) = 
((pos ten (op1 ** op2) m1) ** (pos ten op3 m3)  ** 
(pos ten op4 m4)) (tensor n modes)`,
SIMP_TAC [pos;COP_MUL_THM] THEN 
ONCE_SIMP_TAC [COP_TENSOR_CFUN] THEN
ONCE_SIMP_TAC [COP_TENSOR_CFUN] THEN
SIMP_TAC[COP_TENSOR_ASSOC;COP_LAMBDA_COMPS;
GSYM COND_ABS;COP_MUL_THM;BETA_THM;COND_RATOR; 
o_DEF;I_THM;LAMBDA_ETA;REWRITE_RULE[EQ_CLAUSES]
(SIMP_CONV[o_DEF;I_THM;COND_RATOR;COND_ABS;I_DEF] 
`(if i = m2 then op2 else I) o (if i = m2 then op3 else I) = 
(if i = m2 then op2 o op3 else I)`)]);;


let POS_ASSOC_3_2 = prove
 (`!(ten:cops^N->(A^N->complex)-> (A^N->complex)) (op1:cops) 
 (op2:cops) (op3:cops) (op4:cops) (modes:cfun^N) n m1 m2 m3 m4.
   is_tensor ten /\ ~(m2=m3)==> 
 ((pos ten op1 m1) ** (pos ten op2 m2) ** 
 (pos ten op3 m3) ** (pos ten op4 m4)) (tensor n modes) = 
((pos ten op1 m1) ** (pos ten op3 m3) ** 
(pos ten op2 m2) ** (pos ten op4 m4)) (tensor n modes)`,
SIMP_TAC [pos;COP_MUL_THM] THEN 
ONCE_SIMP_TAC [COP_TENSOR_CFUN] THEN
SIMP_TAC[COP_TENSOR_ASSOC;COP_LAMBDA_COMPS;
COND_RATOR; o_DEF;I_THM;MESON[] `~(m2:num = m3) 
==> (if i=m2 then y else if i=m3 then x else z)
= (if i=m3 then x else if i=m2 then y else z)`]);;


let COP_MUL_RDISTRIB =
COP_ARITH `!op1 op2 op3. (op1 ** op2) ** op3 = op1 ** op2 ** op3`;;


let NS_lem0 = GEN_ALL 
(SIMP_CONV [o_DEF;I_THM;COND_RAND;COND_RATOR;EQ_CLAUSES] 
`(if p then f1 else I) o (if p then f2 else I) =
 (\x. if p then f1 (f2 x) else x)`) ;; 
let NS_lem1 = GEN_ALL 
(SIMP_CONV[GSYM COND_ABS;I_THM; o_THM] 
`(if p then f1 o f2 else I) = 
(\x. if p then f1 (f2 x) else x)`);;

let NS_lem2 = MESON[GSYM NS_lem1;NS_lem0;EQ_TRANS] 
`(if p then f1 else I) o (if p then f2 else I) = 
(if p then f1 o f2 else I)`;;

let NS_lem = MESON[COP_ARITH `! op1 op2.  
(op1 ** op2) = op1 o op2`;NS_lem2] 
`(if p then f1 else I) ** (if p then f2 else I) = 
(if p then f1 ** f2 else I)`;;
 
 
(****************************************************************************)
(*                NS gate Structure                                         *)
(****************************************************************************)

let is_ns_gate = new_definition ` !a b c d 
(ten:qop^N->(real^N->complex)-> (real^N->complex)).
 is_ns_gate (a, b, c, d, ten)  <=> 
 is_beam_splitter (Cx(sqrt(&2 * sqrt(&2) - &2)),Cx(sqrt(&2) - &1),
 --Cx(sqrt(&2) - &1),Cx(sqrt(&2 * sqrt(&2) - &2))
,ten,b$2,2,a$1,1,d$1,1,c$2,2) /\
is_beam_splitter (Cx(sqrt(&1/(&4 - &2 * sqrt(&2)))),
Cx((sqrt(&2) - &1)/sqrt((&4 - &2 * sqrt(&2)))),
Cx((sqrt(&2) - &1)/sqrt((&4 - &2 * sqrt(&2)))),
--Cx(sqrt(&1/(&4 - &2 * sqrt(&2)))),ten,a$2,2,a$3,3,b$2,2,b$3,3) 
/\ is_beam_splitter (Cx(sqrt(&1/(&4 - &2 * sqrt(&2)))),
Cx((sqrt(&2) - &1)/sqrt((&4 - &2 * sqrt(&2)))),
Cx((sqrt(&2) - &1)/sqrt((&4 - &2 * sqrt(&2)))),
--Cx(sqrt(&1/(&4 - &2 * sqrt(&2)))),ten,c$2,2,b$3,3,d$2,2,d$3,3)`;;

(****************************************************************************)
(* All the possible outputs for an input of vacuum feds to NS              *)
(****************************************************************************)

let NS_0 =  prove( `!(a:sm^N) b c d 
(ten:qop^N->(real^N->complex)-> (real^N->complex)).
is_tensor ten /\ is_ns_gate (a, b, c, d, ten)  ==>
tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else  vac (a$3)):bqs^N) 
= (Cx(&1 / &2) % pos ten (cr (d$2)) 2 +  
Cx((sqrt(&2) - &2) * (sqrt(&2) - &1) / (&4 - &2 * sqrt (&2))) %
     pos ten (cr (d$3)) 3 
      + Cx (sqrt (&2 * sqrt (&2) - &2)/(sqrt (&4 - &2 * sqrt (&2)))) %
pos ten (cr (d$1)) 1 ) (tensor 3 (lambda j. vac (d$3)))`,
REWRITE_TAC[is_beam_splitter;pos;is_ns_gate] THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN MULTI_MODE_DECOMPOSE_TAC THEN MULTI_MODE_DECOMPOSE_TAC
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO] THEN
SIMP_TAC[GSYM ONE; GSYM TWO] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN 
ASM_SIMP_TAC[CNJ_CX;GSYM CX_NEG;COP_ADD_LDISTRIB;GSYM COP_MUL_THM] 
THEN ASM_SIMP_TAC[CNJ_MUL;COP_ADD_LDISTRIB;
COP_SMUL_ASSOC;COP_MUL_LSMUL;GSYM CX_MUL;
COP_TENSOR_LINEAR;SMUL_LINCOP;ADD_LINCOP;CNJ_CX;CNJ_II;GSYM CX_NEG] 
THEN REWRITE_TAC[REAL_MUL_RNEG;REAL_MUL_LNEG; 
REAL_NEG_NEG;CX_NEG;COMPLEX_MUL_ASSOC]
THEN IMP_REWRITE_TAC[GSYM SQRT_MUL] THEN 
REPEAT STRIP_TAC THEN (REAL_ARITH_TAC ORELSE ALL_TAC) THEN
REWRITE_TAC[real_div;GSYM REAL_MUL_ASSOC;REAL_MUL_RID;REAL_MUL_LID;
GSYM REAL_INV_MUL;REAL_OF_NUM_MUL;
 ARITH;REAL_FIELD`inv (&2) * &2 * x= x /\ 
 &2 * inv (&2) * x = x /\  &2 * inv (&6) = inv(&3) /\ 
 inv(&3) * &2 * inv (&3) = &2 * inv(&9)`;COP_ADD_ASSOC] THEN 
CFUN_FLATTEN_TAC THEN 
REWRITE_TAC[GSYM pos;GSYM COMPLEX_ADD_LDISTRIB; 
COMPLEX_FIELD `!(a:complex) b c. a*b+a*c+d = (a*b+a*c)+d `;
GSYM complex_sub;COMPLEX_SUB_REFL;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID]
THEN SIMP_TAC[SQRT_INV;REAL_FIELD `&9 = &3 pow 2 /\ 
&36 = &6 pow 2 /\ &18 = &9 * &2/\ &2 * inv(&6) = inv(&3)`;
POW_2_SQRT;REAL_POS;SQRT_MUL;GSYM CX_ADD;GSYM REAL_MUL_2]
THEN REWRITE_TAC [GSYM CX_SUB] THEN
SIMP_TAC [REAL_FIELD ` inv b  * (a:real) = a * inv  b /\ 
inv b * a * a * inv b - a * inv (b) * inv (b)= 
(a - &1) * a * (inv (b pow 2)) /\ 
a * inv b * a * inv b + inv b * a * inv b = 
((&1 + a)*a)*(inv  (b pow 2)) `] THEN
SIMP_TAC [MESON[REAL_FIELD `&4 - &2 * sqrt (&2)  > &0 
<=> sqrt (&2) < (&4)/(&2) `;ARITH;  
 MESON[SQRT_MONO_LT_EQ ; REAL_FIELD `(&2) <  (&16)/(&4)`] 
 `sqrt (&2) <  sqrt ((&16)/(&4)) `;
 MESON[SQRT_DIV ; REAL_FIELD ` &16 = &4 * &4 /\ 
 &4 = &2 * &2 `;GSYM REAL_POW_2;POW_2_SQRT;REAL_POS] `  
 sqrt ((&16)/(&4))  = &4 / &2`]  `&4 - &2 * sqrt (&2) > &0`;
 SQRT_POW_2;REAL_FIELD ` 
 &4 - &2 * sqrt (&2) > &0 ==>  &0 <= &4 - &2 * sqrt (&2) `] THEN
 SIMP_TAC [SQRT_POW_2; REAL_POS;GSYM REAL_POW_2;
 REAL_SUB_LDISTRIB;REAL_MUL_RID; 
 REAL_ARITH ` a + b - a  = (b:real) `; 
 REAL_ARITH ` a - &1 - &1 = (a:real)  - &2`]
 THEN SIMP_TAC[GSYM real_div;MESON[REAL_FIELD 
 `&0 < &2 -  sqrt (&2)  <=> sqrt (&2) < (&2) `;ARITH;  
 MESON[SQRT_MONO_LT_EQ;REAL_FIELD `(&2) <  (&4)`] `sqrt (&2) < sqrt (&4) `;
 MESON[SQRT_DIV;REAL_FIELD `&4 = &2 * &2`;GSYM REAL_POW_2;POW_2_SQRT;REAL_POS] 
 `sqrt (&4)  = &2`] ` &0 < &2 -  sqrt (&2)`; REAL_DIV_REFL;
 REAL_FIELD `&4 -  &2 * sqrt (&2) = &2 *(&2-  sqrt (&2))`; 
REAL_FIELD `x / (y * z) = ((&1)/y) * (x/z)`;REAL_MUL_RID;REAL_POS_NZ] 
THEN SIMP_TAC[real_div;REAL_MUL_LID]);;
 
(****************************************************************************)
(* Some lemmas to prove the projection of NS outputs for vaccum input       *)
(****************************************************************************)
 
 let lemma1 = prove( `is_sm sm ==> vac (sm) = fock sm 0 
 /\ cr (sm) (vac sm) = fock sm 1 
  /\  (inv (Cx (sqrt (&2))) % (cr (sm) **cr (sm))) (vac sm) = fock sm 2`,
 ASM_SIMP_TAC[LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
 THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO] THEN
SIMP_TAC[GSYM ONE; GSYM TWO] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID;I_THM]);;
 

 
 
 let lemma24 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)) x. 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
    m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
    else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)) (tensor 3
   ((lambda i. if i = 2 then cr (d$2) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0))     `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3 /\ ~(1 = 0)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","0")) 
 ((SPEC_V ("m1","1")) tensor_proj_zero))))))] THEN
    IMP_REWRITE_TAC[GSYM is_ns_gate; GSYM is_beam_splitter;
    ARITH_RULE `1 <= 1 /\ (3 <=  dimindex (:N) ==> 1 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN 
    ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
    `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`);
    is_ns_gate;lemma1;is_beam_splitter;COP_SMUL_THM;I_THM]);;           

    
    let lemma25 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)) x. 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
    m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
    else if i = 1 then fock (d$1) 2 else vac (d$3)):bqs^N)) (tensor 3
   ((lambda i. if i = 2 then cr (d$2) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0))     `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 1 /\ 1 <= 3 /\ ~(2 = 0)`]
   ((SPEC_V ("sm","d$1")) ((SPEC_V ("k","1")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","0")) 
    ((SPEC_V ("m1","2")) tensor_proj_zero))))))] THEN
    IMP_REWRITE_TAC[GSYM is_ns_gate; GSYM is_beam_splitter;
    ARITH_RULE `1 <= 1 /\ (3 <=  dimindex (:N) ==> 1 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN 
    ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
    `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`);
   is_ns_gate;lemma1;is_beam_splitter;COP_SMUL_THM;I_THM]);;    

let lemma22 = prove( `is_ns_gate (a, b, c, d, ten) ==>
proj (vac (d$1)) (vac (d$3)) = (vac (d$1)) /\ 
proj (fock (d$2) 1) (cr (d$2) (vac (d$3))) = (fock (d$2) 1)  /\ 
proj (vac (d$3)) (vac (d$3)) = (vac (d$3))`,
ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> 
(vac (d$3) = vac (d$2) /\ vac (d$3) = vac (d$1)))`);
is_ns_gate;lemma1;is_beam_splitter;FOCK_PROJ_N]);;


let lemma21 = prove( `!(a:sm^N) b c d
 (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)) x. 
   is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten) 
   /\ 3 <=  dimindex (:N) ==>          
    m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
    else if i = 1 then x else vac (d$3)):bqs^N)) (tensor 3
   ((lambda i. if i = 3 then cr (d$3) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0)) /\
  m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
    else if i = 1 then x else vac (d$3)):bqs^N)) (tensor 3
   ((lambda i. if i = 1 then cr (d$1) (vac (d$3)) else vac (d$3)):bqs^N)) = K (Cx (&0)) `, 
    IMP_REWRITE_TAC[is_ns_gate;is_beam_splitter;
    (REWRITE_RULE[ARITH_RULE ` 2 +1 = 3 /\ 0 < 2 /\ 2 <= 3 /\ ~(1 = 0)`]
   ((SPEC_V ("sm","d$2")) ((SPEC_V ("k","2")) ((SPEC_V ("n","2")) ((SPEC_V ("m2","0")) 
   ((SPEC_V ("m1","1")) tensor_proj_zero))))))] THEN
    IMP_REWRITE_TAC[GSYM is_ns_gate; GSYM is_beam_splitter;
    ARITH_RULE `1 <= 2 /\ (3 <=  dimindex (:N) ==> 2 <=  dimindex (:N))`;
    LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV THEN 
  ASM_MESON_TAC[(MESON[is_ns_gate;is_beam_splitter]  
  `(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$2))`);
   is_ns_gate;lemma1;is_beam_splitter;COP_SMUL_THM;I_THM]);;
 
 
 let lemma = prove(`
    is_ns_gate (a, b, c, d, ten) ==> 
 (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else  vac (d$3)):bqs^N))
 =  (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then vac (d$1) else  vac (d$3))):bqs^N)) `,
  IMP_REWRITE_TAC [COND_ID;GSYM (MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`)]);;
 
(****************************************************************************)
(* The projection of NS outputs for vacuum input on vacuum state            *)
(****************************************************************************)

let NS_0_PROJ_0 =  
    prove( `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten)
    /\ 3 <=  dimindex (:N) ==> (m_modes_pro (tensor 3 
    ((lambda i. if i = 2 then fock (d$2) 1 else  vac (d$3)):bqs^N)))
   (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else  vac (a$3)):bqs^N)) 
    = Cx(&1 / &2) %
tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else  vac (d$3)):bqs^N)`,
 IMP_REWRITE_TAC[GEN_ALL NS_0;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
 THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
  SIMP_TAC [COND_RATOR;I_THM] THEN
 CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR] THEN
IMP_REWRITE_TAC[lemma21;lemma;CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero]
THEN SIMP_TAC[PRO_TENSOR_CFUN ] THEN
SIMP_TAC[tensor;ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\  1 = SUC 0`] THEN
SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3`;
ARITH_RULE `3 <= dimindex (:N)  ==> (2 <= dimindex (:N) 
/\ 1 <= dimindex (:N)) `;LAMBDA_BETA] THEN
CONV_TAC NUM_REDUCE_CONV THEN IMP_REWRITE_TAC [lemma22] 
THEN IMP_REWRITE_TAC [(MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`)]);;


(****************************************************************************)
(* The projection of NS outputs for vacuum input on 2-qubit state            *)
(****************************************************************************)
  

let NS_0_PROJ_2 =  
    prove( `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten)
     /\ 3 <=  dimindex (:N) ==>
     (m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then fock (d$1) 2 else  vac (d$3))):bqs^N)))
     (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else  vac (a$3)):bqs^N)) 
     =  K (Cx (&0)) `,
 IMP_REWRITE_TAC[GEN_ALL NS_0;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
     THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
     SIMP_TAC [COND_RATOR;I_THM] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR] THEN
IMP_REWRITE_TAC[lemma21;lemma25;CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero]
THEN SIMP_TAC[PRO_TENSOR_CFUN ] THEN
SIMP_TAC[tensor;ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\  1 = SUC 0`] THEN
SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3`;
ARITH_RULE `3 <= dimindex (:N)  ==> (2 <= dimindex (:N) 
/\ 1 <= dimindex (:N)) `;LAMBDA_BETA] THEN
CONV_TAC NUM_REDUCE_CONV THEN IMP_REWRITE_TAC [lemma22] 
THEN IMP_REWRITE_TAC [(MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`)]);;

(****************************************************************************)
(* The projection of NS outputs for vacuum input on 1-qubit state            *)
(****************************************************************************)

let NS_0_PROJ_1 =  
    prove( `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 is_tensor_pro m_modes_pro /\ is_tensor ten /\ is_ns_gate (a, b, c, d, ten)
     /\ 3 <=  dimindex (:N) ==>
     (m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else 
  (if i = 1 then fock (d$1) 1 else  vac (d$3))):bqs^N)))
     (tensor 3 ((lambda i. if i = 2 then fock (a$2) 1 else  vac (a$3)):bqs^N)) 
     =  K (Cx (&0))`,
 IMP_REWRITE_TAC[GEN_ALL NS_0;COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;pos] 
     THEN ONCE_ASM_SIMP_TAC[COP_TENSOR_CFUN] THEN
ONCE_REWRITE_TAC[GSYM CFUN_LAMBDA_APP] THEN
     SIMP_TAC [COND_RATOR;I_THM] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[LINCOP_SUB;LINCOP_ADD;LINCOP_SMUL;PRO_TENSOR_LINEAR] THEN
IMP_REWRITE_TAC[lemma24;lemma21;CFUN_ZERO_CLAUSES;CFUN_ADD_LID;GSYM cfun_zero]
THEN SIMP_TAC[PRO_TENSOR_CFUN ] THEN
SIMP_TAC[tensor;ARITH_RULE `3 = SUC 2 /\ 2 = SUC 1 /\  1 = SUC 0`] THEN
SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2 /\ 1 <= 3`;
ARITH_RULE `3 <= dimindex (:N)  ==> (2 <= dimindex (:N) 
/\ 1 <= dimindex (:N)) `;LAMBDA_BETA] THEN
CONV_TAC NUM_REDUCE_CONV THEN IMP_REWRITE_TAC [lemma22] 
THEN IMP_REWRITE_TAC [(MESON[is_ns_gate;is_beam_splitter]  
`(is_ns_gate (a, b, c, d, ten) ==> vac (d$3) = vac (d$1))`)]);;










