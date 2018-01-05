(* ========================================================================= *)
(*                                                                           *)
(*                           CZ_GATE.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "NS_gate_2_proj.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 


(****************************************************************************)
(*                              CZ gate structure                           *)
(****************************************************************************)
             
let is_CZ_model = 
define `is_CZ_model ((a:sm^N), (b:sm^N), (c:sm^N), (j:sm^N),ten)  <=> 
 (?(d:sm^N) (q:sm^N) (l:sm^N) (k:sm^N) (m:sm^N) (p:sm^N).
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)) ,ten,a$1,1,a$4,4,b$1,1,b$4,4)/\
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)),ten,c$1,1,c$4,4,j$1,1,j$4,4) /\ 
vac (a$4) = vac (b$3) /\ is_ns_gate (b, l, k, c, ten) /\ 
is_ns_gate (d, m, p, q, ten) /\  vac (b$6) = vac (b$3)
/\  q$1 = c$4 /\ q$2 = c$5 /\ q$3 = c$6 /\ b$4 = d$1 /\ b$5 = d$2 
/\ b$6 = d$3 /\ vac (c$6) = vac (c$3) /\  vac (q$3) = vac (c$3) /\
vac (a$1) = vac (b$3)  /\ vac (j$4) = vac (c$3) 
/\ is_sm (a$3) /\ is_sm (a$2)) `;;

(****************************************************************************)
(*                   CZ outputs behavioral description                       *)
(****************************************************************************)

let CZ_OUTPUTS =  define `
CZ_OUTPUTS  ((y1:sm), (y2:sm), (a:sm^N), (c:sm^N), (j:sm^N), 
(LH:sm->(real->complex)), (LV:sm->(real->complex)))  <=> 
tensor 8 ((lambda i. if i = 2 then fock (c$2) 1
else if i = 5 then fock (c$5) 1 else if i = 7 then 
fock (a$2) 1 else if i = 8 then fock (a$3) 1 else vac (c$3)):bqs^N) =
tensor 2 ((lambda i. if i = 1 then LH (y1) else LH (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 1 then cr (j$1) (vac (c$3)) else if i = 4
then cr (j$4) (vac (c$3)) else if i = 2 then fock (c$2) 1
else if i = 5 then fock (c$5) 1 else if i = 7 then vac (a$2) 
else if i = 8  then vac (a$3) else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i.  if i = 1 then LV (y1) else LV (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 1 then fock (j$1) 1 else if i = 2
then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 
then vac (a$2) else if i = 8 then fock (a$3) 1  else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then LV (y1) else LH (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 4 then fock (j$4) 1 else if i = 2
then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 then 
fock (a$2) 1 else if i = 8 then vac (a$3) else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then LH (y1) else LV (y2)):bqs^N) /\ 

tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else if i = 5 then 
fock (c$5) 1 else if i = 7 then vac (a$2) else if i = 8 then 
fock (a$3) 1  else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then vac (y1) else LH (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 4 then fock (j$4) 1 else if i = 2
then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 then 
vac (a$2) else if i = 8 then vac (a$3)  else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then vac (y1) else LV (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else if i = 5 then 
fock (c$5) 1 else if i = 7 then fock (a$2) 1 else if i = 8 then 
vac (a$3)  else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then  LH (y1) else vac (y2)):bqs^N) /\

tensor 8 ((lambda i. if i = 1 then fock (j$1) 1 else if i = 2
then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 then 
vac (a$2) else if i = 8 then vac (a$3)  else vac (c$3)):bqs^N) = 
tensor 2 ((lambda i. if i = 1 then LV (y1) else  vac (y2)):bqs^N)`;;
 
(****************************************************************************)
(*                   CZ inputs behavioral description                       *)
(****************************************************************************) 

let CZ_INPUTS =  
define `CZ_INPUTS ((x1:sm), (x2:sm),(a:sm^N), (b:sm^N), (c:sm^N),
(LH:sm->(real->complex)), (LV:sm->(real->complex)),
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
(tensor 2 ((lambda i.  if i = 1 then LH (x1)  else LH (x2)):bqs^N)) =
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
 (if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 else 
(if i = 8 then fock (a$3) 1 else vac (c$3))))):bqs^N)))
 (tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 
else (if i = 5 then fock (b$5) 1 else (if i = 7 then fock (a$2) 1 
else (if i = 8 then fock (a$3) 1 else vac (b$3))))):bqs^N)) /\   

tensor 2 ((lambda i. if i = 1 then LV (x1)  else LV (x2)):bqs^N) = 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 
else if i = 5 then fock (c$5) 1 else
if i = 7 then vac (a$2) else if i = 8 then vac (a$3)  
else if i = 1 then fock (c$1) 2 else vac (c$3)):bqs^N))) +
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 
else if i = 5 then fock (c$5) 1 else
 if i = 7 then vac (a$2) else if i = 8  then vac (a$3) 
else if i = 4 then fock (c$4) 2 else vac (c$3)):bqs^N))) +
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 
else if i = 5 then fock (c$5) 1 else
  if i = 4 then fock (c$4) 1 else if i = 7 then vac (a$2) 
else if i = 8  then vac (a$3) else if i = 1 then fock (c$1) 1 
else vac (c$3)):bqs^N)))) (tensor 8 ((lambda i.  if i = 1 then 
fock (a$1) 1 else if i = 4 then fock (a$4) 1 else if i = 2 
then fock (b$2) 1  else if i = 7 then vac (a$2) else if i = 8  
then vac (a$3) else if i = 5 then fock (b$5) 1 else vac (b$3)):bqs^N)) /\

tensor 2 ((lambda i. if i = 1 then LV (x1) else LH (x2)):bqs^N) = 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  (if i = 1 then fock (c$1) 1 else (if i = 5 then fock (c$5) 1 else 
if i = 7 then vac (a$2) else if i = 8 then fock (a$3) 1  
else vac (c$3)))):bqs^N))) +
   (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
   (if i = 5 then fock (c$5) 1 else  (if i = 4 then fock (c$4) 1 else 
if i = 7 then vac (a$2) else if i = 8 then 
fock (a$3) 1  else vac (c$3)))):bqs^N))))
 (tensor 8 ((lambda i.  if i = 1 then fock (a$1) 1 
else (if i = 2 then fock (b$2) 1 
 else (if i = 5 then fock (b$5) 1 else if i = 7 then vac (a$2) 
else if i = 8 then fock (a$3) 1  else vac (b$3)))):bqs^N))  /\

tensor 2 ((lambda i. if i = 1 then LH (x1) else LV (x2)):bqs^N) = 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  if i = 1 then fock (c$1) 1 else  if i = 7 then fock (a$2) 1 else 
if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 
else vac (c$3)):bqs^N))) +
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
if i = 4 then fock (c$4) 1 else if i = 7 then fock (a$2) 1 
else if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 
else vac (c$3)):bqs^N))))
(tensor 8 ((lambda i.  if i = 4 then fock (a$4) 1 
else if i = 2 then fock (b$2) 1 
 else  if i = 7 then fock (a$2) 1 else if i = 8 then vac (a$3)
 else if i = 5 then fock (b$5) 1 else vac (b$3)):bqs^N)) /\
 
 tensor 2 ((lambda i. if i = 1 then vac (x1) else LH (x2)):bqs^N) = 
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
 (if i = 5 then fock (c$5) 1 else (if i = 7 then vac (a$2) else 
 (if i = 8 then fock (a$3) 1 else vac (c$3))))):bqs^N)))
 (tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 else 
 (if i = 5 then fock (b$5) 1 else (if i = 7 then vac (a$2) else 
 (if i = 8 then fock (a$3) 1 else vac (b$3))))):bqs^N)) /\
 
tensor 2 ((lambda i. if i = 1 then vac (x1) else LV (x2)):bqs^N) = 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  if i = 1 then fock (c$1) 1 else  if i = 7 then vac (a$2) else 
  if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 else 
  vac (c$3)):bqs^N))) + (m_modes_pro (tensor 8 ((lambda i. if i = 2 then 
  fock (c$2) 1 else if i = 4 then fock (c$4) 1 else if i = 7 then 
  vac (a$2) else if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 
  else vac (c$3)):bqs^N)))) (tensor 8 ((lambda i.  if i = 4 then 
  fock (a$4) 1 else if i = 2 then fock (b$2) 1 else  if i = 7 then 
  vac (a$2) else if i = 8 then vac (a$3) else if i = 5 then fock (b$5) 1 
  else vac (b$3)):bqs^N)) /\
  
tensor 2 ((lambda i. if i = 1 then LH (x1) else vac (x2)):bqs^N) = 
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
 (if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 else 
 (if i = 8 then vac (a$3) else vac (c$3))))):bqs^N)))
 (tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 else (if i = 5 then 
 fock (b$5) 1 else (if i = 7 then fock (a$2) 1 else (if i = 8 then 
 vac (a$3)  else vac (b$3))))):bqs^N)) /\
 
tensor 2 ((lambda i. if i = 1 then LV (x1) else vac (x2)):bqs^N) = 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  if i = 1 then fock (c$1) 1 else  if i = 7 then vac (a$2) else 
  if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 else 
  vac (c$3)):bqs^N))) + (m_modes_pro (tensor 8 ((lambda i. if i = 2 then 
  fock (c$2) 1 else if i = 4 then fock (c$4) 1 else if i = 7 then 
  vac (a$2) else if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 
  else vac (c$3)):bqs^N)))) (tensor 8 ((lambda i.  if i = 1 then 
  fock (a$1) 1 else if i = 2 then fock (b$2) 1 else  if i = 7 then 
  vac (a$2) else if i = 8 then vac (a$3) else if i = 5 then fock (b$5) 1 
  else vac (b$3)):bqs^N))`;;


(****************************************************************************)
(*                         CZ gate hol model                                *)
(****************************************************************************)
 
let CZ_GATE = define 
   `CZ_GATE ((x1:sm), (x2:sm), (y1:sm), (y2:sm),ten,
   (LH:sm->(real->complex)), (LV:sm->(real->complex)),
   (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)))  <=> 
   (?(a:sm^N) (b:sm^N) (c:sm^N) (j:sm^N).
   (is_CZ_model (a, b, c, j, ten) /\ CZ_INPUTS  (x1,x2,a, b, c,LH,LV, m_modes_pro) /\
    CZ_OUTPUTS  (y1,y2,a, c, j,LH,LV)))`;;

(****************************************************************************)
(* Some lemmas to prove the projection of CZ gate for all possible inputs   *)
(****************************************************************************)

let lemma_VV = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_sm (a$3) /\ is_sm (a$2) 
   /\ 2 <=  dimindex (:N) ==>
   m_modes_pro (tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else if i = 2 then fock (a$3) 1 else vac (c$3)):bqs^N))
   (tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else if i = 2 then fock (a$3) 1 else vac (b$3)):bqs^N)) =
   tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else  fock (a$3) 1):bqs^N)`,
   SIMP_TAC[PRO_TENSOR_CFUN ] THEN
   SIMP_TAC[tensor;ARITH_RULE ` 2 = SUC 1 /\  1 = SUC 0`] THEN
   SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
   IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`;
   ARITH_RULE `2 <= dimindex (:N)  ==>  
   1 <= dimindex (:N) `;LAMBDA_BETA] THEN
   CONV_TAC NUM_REDUCE_CONV 
   THEN IMP_REWRITE_TAC [lemma1;FOCK_PROJ_N]);;


let lemma_HH = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_sm (a$3) /\ is_sm (a$2) 
   /\ 2 <=  dimindex (:N) ==>
   m_modes_pro (tensor 2 ((lambda i. if i = 1 then vac (a$2)
   else if i = 2 then vac (a$3) else vac (c$3)):bqs^N))
   (tensor 2 ((lambda i. if i = 1 then vac (a$2)
   else if i = 2 then vac (a$3) else vac (b$3)):bqs^N)) =
   tensor 2 ((lambda i. if i = 1 then vac (a$2)
   else  vac (a$3)):bqs^N)`,
   SIMP_TAC[PRO_TENSOR_CFUN ] THEN
   SIMP_TAC[tensor;ARITH_RULE ` 2 = SUC 1 /\  1 = SUC 0`] THEN
   SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
   IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`;
   ARITH_RULE `2 <= dimindex (:N)  ==>  
   1 <= dimindex (:N) `;LAMBDA_BETA] THEN
   CONV_TAC NUM_REDUCE_CONV 
   THEN IMP_REWRITE_TAC [lemma1;FOCK_PROJ_N]);;


let lemma_HV = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_sm (a$3) /\ is_sm (a$2) 
   /\ 2 <=  dimindex (:N) ==>
   m_modes_pro (tensor 2 ((lambda i. if i = 1 then vac (a$2)
   else if i = 2 then fock (a$3) 1 else vac (c$3)):bqs^N))
   (tensor 2 ((lambda i. if i = 1 then vac (a$2)
    else if i = 2 then fock (a$3) 1 else vac (b$3)):bqs^N)) =
   tensor 2 ((lambda i. if i = 1 then vac (a$2)
   else  fock (a$3) 1):bqs^N)`,
   SIMP_TAC[PRO_TENSOR_CFUN ] THEN
   SIMP_TAC[tensor;ARITH_RULE ` 2 = SUC 1 /\  1 = SUC 0`] THEN
   SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
   IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`;
   ARITH_RULE `2 <= dimindex (:N)  ==>  
   1 <= dimindex (:N) `;LAMBDA_BETA] THEN
   CONV_TAC NUM_REDUCE_CONV 
   THEN IMP_REWRITE_TAC [lemma1;FOCK_PROJ_N]);;


let lemma_VH = prove(
 `!(a:sm^N) b c d (ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
   is_tensor_pro m_modes_pro /\ is_sm (a$3) /\ is_sm (a$2) 
   /\ 2 <=  dimindex (:N) ==>
   m_modes_pro (tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else if i = 2 then vac (a$3) else vac (c$3)):bqs^N))
    (tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else if i = 2 then vac (a$3) else vac (b$3)):bqs^N)) =
   tensor 2 ((lambda i. if i = 1 then fock (a$2) 1
   else  vac (a$3)):bqs^N)`,
   SIMP_TAC[PRO_TENSOR_CFUN ] THEN
   SIMP_TAC[tensor;ARITH_RULE ` 2 = SUC 1 /\  1 = SUC 0`] THEN
   SIMP_TAC[ARITH_RULE ` SUC 2 = 3 /\  SUC 1 = 2 /\   SUC 0 = 1`] THEN
   IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 2`;
   ARITH_RULE `2 <= dimindex (:N)  ==>  
   1 <= dimindex (:N) `;LAMBDA_BETA] THEN
   CONV_TAC NUM_REDUCE_CONV 
 THEN IMP_REWRITE_TAC [lemma1;FOCK_PROJ_N]);;





let CZ_lemma4 = prove(`!x
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
is_tensor_pro m_modes_pro /\ is_tensor ten /\ 8 <=  dimindex (:N)  ==>
tensor 8 ((lambda i. if i = 1 then inv (Cx (sqrt (&2))) % x 
else if i = 2 then x1 else if i = 5 then x2 else if i = 7 then 
x5 else if i = 8 then x6 else x4):bqs^N) = inv (Cx (sqrt (&2))) % 
(tensor 8 ((lambda i. if i = 1 then  x else ((lambda i. if i = 1 then 
inv (Cx (sqrt (&2))) % x else if i = 2 then x1 else if i = 5 then x2 
else if i = 7 then x5 else if i = 8 then x6 else x4):bqs^N)$i):bqs^N))`, 
IMP_REWRITE_TAC[(GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 7 +1 = 8 
/\ 0 < 1 /\ 1 <= 8`] (((SPEC_V ("n","7")) ((SPEC_V ("a","inv (Cx (sqrt (&2)))")) 
((SPEC_V ("k","1")) ( tensor_blin_smul))))))] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ (8 <=  dimindex (:N) ==> 
1 <=  dimindex (:N)) `;LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV);;    

let CZ_lemma3 = prove(`!x
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 is_tensor_pro m_modes_pro /\ is_tensor ten /\ 8 <=  dimindex (:N)  ==>
tensor 8 ((lambda i. if i = 4 then inv (Cx (sqrt (&2))) % x 
else if i = 2 then x1 else if i = 5 then x2 else if i = 7 then 
x5 else if i = 8 then x6 else x4):bqs^N) = inv (Cx (sqrt (&2))) % 
(tensor 8 ((lambda i. if i = 4 then  x else ((lambda i. if i = 4 then 
inv (Cx (sqrt (&2))) % x else if i = 2 then x1 else if i = 5 then x2 
else if i = 7 then x5 else if i = 8 then x6 else x4):bqs^N)$i):bqs^N))`, 
IMP_REWRITE_TAC[ (GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE ` 7 +1 = 8 
/\ 0 < 4 /\ 4 <= 8`] (((SPEC_V ("n","7")) ((SPEC_V ("a","inv (Cx (sqrt (&2)))")) 
((SPEC_V ("k","4")) ( tensor_blin_smul))))))] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 4  /\ (8 <=  dimindex (:N) ==> 
4 <=  dimindex (:N)) `;LAMBDA_BETA] THEN CONV_TAC NUM_REDUCE_CONV);;  

let CZ_lemma1 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
  is_tensor_pro m_modes_pro /\ is_tensor ten  /\ 6 <=  dimindex (:N) /\  
is_beam_splitter (Cx (sqrt (&1 / &2)), Cx (sqrt (&1 / &2)), 
Cx (sqrt (&1 / &2)), --Cx (sqrt (&1 / &2)),ten,a$1,1,a$4,4,b$1,1,d$1,4) ==>
 tensor 6 ((lambda i. if i = 4 then cr (d$1) (cr (d$1) (vac (d$1)))
    else if i = 2 then fock (b$2) 1
    else if i = 5 then fock (d$2) 1 else vac (b$3)):bqs^N) = Cx (sqrt (&2)) % 
    (tensor 6 ((lambda i. if i = 4 then  fock (d$1) 2
     else ((lambda i. if i = 4 then cr (d$1) (cr (d$1) (vac (d$1)))
    else if i = 2 then fock (b$2) 1
    else if i = 5 then fock (d$2) 1 else vac (b$3)):bqs^N)$i):bqs^N))`, 
IMP_REWRITE_TAC[(GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE 
` 5 +1 = 6 /\ 0 < 4 /\ 4 <= 6`] (((SPEC_V ("n","5")) 
((SPEC_V ("a","Cx (sqrt (&2))")) 
((SPEC_V ("k","4")) ( tensor_blin_smul))))))] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 4 /\ (6 <=  dimindex (:N) ==> 
4 <=  dimindex (:N)) `;LAMBDA_BETA] THEN 
CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&2)) = Cx(&0))`] 
`(Cx (sqrt (&2)) * inv (Cx (sqrt (&2)))) = Cx(&1)`)]
`(cr (d$1) ** cr (d$1)) (vac (d$1)) =
Cx (sqrt (&2)) % ( inv (Cx (sqrt (&2))) % 
((cr (d$1) ** cr (d$1)) (vac (d$1))))`)] THEN
SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter]  THEN
COP_ARITH_TAC) ;;
  
  
   let CZ_lemma2 = prove(`!(a:sm^N) b c d
(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
 (m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
is_tensor_pro m_modes_pro /\ is_tensor ten  /\ 6 <=  dimindex (:N) /\  
is_beam_splitter (Cx (sqrt (&1 / &2)), Cx (sqrt (&1 / &2)), 
Cx (sqrt (&1 / &2)), --Cx (sqrt (&1 / &2)),ten,a$1,1,a$4,4,b$1,1,d$1,4) ==>
   tensor 6 ((lambda i. if i = 1 then cr (b$1) (cr (b$1) (vac (b$1)))
  else if i = 2 then fock (b$2) 1 else if i = 5 then 
   fock (d$2) 1 else vac (b$3)):bqs^N) = Cx (sqrt (&2)) % 
    (tensor 6 ((lambda i. if i = 1 then  fock (b$1) 2
     else ((lambda i. if i = 1 then cr (b$1) (cr (b$1) (vac (b$1)))
  else if i = 2 then fock (b$2) 1 else if i = 5 then 
  fock (d$2) 1 else vac (b$3)):bqs^N)$i):bqs^N))`, 
IMP_REWRITE_TAC[(GSYM o GEN_ALL)(REWRITE_RULE[ARITH_RULE 
` 5 +1 = 6 /\ 0 < 1 /\ 1 <= 6`] (((SPEC_V ("n","5")) 
((SPEC_V ("a","Cx (sqrt (&2))")) 
((SPEC_V ("k","1")) ( tensor_blin_smul))))))] THEN
IMP_REWRITE_TAC[ARITH_RULE `1 <= 1 /\ (6 <=  dimindex (:N) ==> 
1 <=  dimindex (:N)) `;LAMBDA_BETA] THEN 
CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[GSYM COP_MUL_THM]
THEN ONCE_REWRITE_TAC [(MESON[GSYM CFUN_SMUL_LID;
GSYM CFUN_SMUL_ASSOC;GSYM (MESON[COMPLEX_MUL_RINV;
MESON[REAL_OF_NUM_EQ;CX_INJ;SQRT_EQ_0;ARITH]`~(Cx (sqrt (&2)) = Cx(&0))`] 
`(Cx (sqrt (&2)) * inv (Cx (sqrt (&2)))) = Cx(&1)`)] `(cr (b$1) ** 
cr (b$1)) (vac (b$1)) = Cx (sqrt (&2)) % ( inv (Cx (sqrt (&2))) % 
((cr (b$1) ** cr (b$1)) (vac (b$1))))`)] THEN 
SIMP_TAC[GSYM lemma1;is_ns_gate;is_beam_splitter]  THEN
 COP_ARITH_TAC) ;;   


(****************************************************************************)
(*      The projection of CZ outputs for two vacuum inputs                  *)
(****************************************************************************)



let CZ_00 =prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) 
==>  (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
(if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 else 
(if i = 8 then fock (a$3) 1 else vac (c$3))))):bqs^N)))
(tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 else 
(if i = 5 then fock (b$5) 1 else (if i = 7 then fock (a$2) 1 else 
(if i = 8 then fock (a$3) 1 else vac (b$3))))):bqs^N)) =
(Cx (&1 / &4)) % tensor 8 (lambda i. if i = 2 then fock (c$2) 1
else if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 
else (if i = 8 then fock (a$3) 1 else vac (c$3))))`,
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;is_CZ_model] THEN REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\  1 <= 2  `;proj_tensor_m_n;
ARITH_RULE `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  6 <= dimindex (:N)))`] 
THEN ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE `i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] 
THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\  1 <= 3  `;proj_tensor_m_n;
ARITH_RULE `(6 <= dimindex (:N) ==>  3 <= dimindex (:N)) `] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3+3 <= dimindex (:N) 
<=> (6 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN    
SIMP_TAC [MESON[ARITH] `(if i = 2 then x
    else if i = 5 then y else z) = (if(i<=3) then (if i = 2
    then x else z) else (if i = 5 then y else z))`] THEN    
ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (if i = 2 then x else z)
    else (if i = 5 then y else z)) = 
    (if i <= 3 then (\j. if j = 2 then x else z) i
    else (\j. if j = 5 then y else z) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
    ((6 <= dimindex (:N)) ==>(i <= 3 ==> i + 3 <= dimindex (:N)) )`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 5) <=> (i=2))`]
`(if i + 3 <= 3 then if i + 3 = 2 then x else z else if i + 3 = 5 then 
y else z) = if i = 2 then y else z`] THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
IMP_REWRITE_TAC[NS_0_PROJ_0;REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[]
`vac (d$3) = vac (b$3) /\ q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  
q$2 = c$5 ==> m_modes_pro (tensor 3 ((lambda i. if i = 2 then 
fock (c$5) 1 else vac (c$3)):bqs^N)) (tensor 3 ((lambda i. 
if i = 2 then fock (d$2) 1 else vac (b$3)):bqs^N)) =  
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 
else vac (q$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then 
fock (d$2) 1 else vac (d$3)):bqs^N))`)] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3 <= dimindex (:N) 
<=> (3 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 6) /\ 
( 1 <= i + 2) /\ ( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>
(i <= 2 ==> (i + 6 <= dimindex (:N))))`] THEN REWRITE_TAC[ARITH_RULE 
`(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F)) /\ 
(((i:num) + j <= k) <=> (if (j <= k) then i <= k - j else F))`] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN 
IMP_REWRITE_TAC[lemma_VV] THEN REWRITE_TAC [CFUN_ARITH 
`!f1:A^N->complex a1 a2. ( ((a1 % f1) x) * (a2 % f2) y) * f3 z  = 
(a1*a2) * (f1 x * f2 y) * f3 z `] THEN REWRITE_TAC [CFUN_ARITH 
`!f1:A^N->complex a1 a2.  ((a1 % f1) y) * (a2 % f2) (lambda i. y$(i+k)) = 
(a1*a2) * f1 y * f2 (lambda i. y$(i+k)) `] THEN SIMP_TAC [CFUN_ARITH 
`!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `] THEN
ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN
ASM_SIMP_TAC[ARITH_RULE ` ((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA] 
THEN SIMP_TAC[ARITH_RULE ` (i - 3 = 1  <=> i = 4) /\ 
(i - 3 = 2  <=> i = 5) /\ (i - 6 = 1  <=> i = 7) /\
(i - 3 = 3 <=> i = 6)`] THEN ASM_SIMP_TAC [ARITH_RULE `  
    i <= 3 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==> 
( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`] `(if (i <= 8 /\ 1 <= i) then 
if i <= 6 then if i <= 3 then if i = 2 then x1 else x2 else if i = 5 then 
x3 else x2  else if i = 7 then x4 else x5 else x6) = (if (i <= 8 /\ 1 <= i) then 
if i = 2 then x1 else if i = 5 then x3 else if i = 7 then x4 else if i = 8 then
x5 else x2 else x6) /\ (if (i <= 8 /\ 1 <= i) then if i <= 3 then if i = 2 then 
x1 else x2 else if i = 5 then x3 else if i = 7 then x4 else if i = 8 then 
x5 else x2 else x6) = (if (i <= 8 /\ 1 <= i) then if i = 2 then x1 else 
if i = 5 then x3 else if i = 7 then x4 else if i = 8 then x5 else 
x2 else x6)`] THEN SIMP_TAC[GSYM CX_MUL;REAL_FIELD 
` &1 / &2 * &1 / &2 = &1 / &4 `;ETA_AX]);;



let CZ_GATE_00 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LH (cz1) else LH (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 LH (cz3) else  LH (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
IMP_REWRITE_TAC[CZ_INPUTS;CZ_00;CZ_OUTPUTS]);;

(****************************************************************************)
(*   The projection of CZ outputs for two 1-qubit fock state inputs          *)
(****************************************************************************)



let CZ_11 = prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) ==> 
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
if i = 5 then fock (c$5) 1 else if i = 7 then vac (a$2) else 
if i = 8 then vac (a$3)  else if i = 1 then fock (c$1) 2 else 
vac (c$3)):bqs^N))) + (m_modes_pro (tensor 8 ((lambda i. if i = 2 then 
fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 then vac (a$2) else 
if i = 8  then vac (a$3) else if i = 4 then fock (c$4) 2 else vac (c$3)):bqs^N))) +
(m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else if i = 5 then 
fock (c$5) 1 else if i = 4 then fock (c$4) 1 else if i = 7 then vac (a$2) else 
if i = 8  then vac (a$3) else if i = 1 then fock (c$1) 1 else vac (c$3)):bqs^N))))
(tensor 8 ((lambda i.  if i = 1 then fock (a$1) 1 else if i = 4 then 
fock (a$4) 1 else if i = 2 then fock (b$2) 1 else if i = 7 then vac (a$2) else 
if i = 8  then vac (a$3) else if i = 5 then fock (b$5) 1 else vac (b$3)):bqs^N)) =  
Cx (--(&1 / &4)) % tensor 8 (lambda i. if i = 1 then cr (j$1) (vac (c$3)) else 
if i = 4 then cr (j$4) (vac (c$3)) else if i = 2 then fock (c$2) 1
else if i = 5 then fock (c$5) 1 else if i = 7 then vac (a$2) else if i = 8 
then vac (a$3) else vac (c$3))`,         
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
is_CZ_model] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
SIMP_TAC[COP_ADD_THM] THEN SIMP_TAC[is_beam_splitter;
LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC] THEN SIMP_TAC[GSYM is_beam_splitter] 
THEN SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO] THEN SIMP_TAC[GSYM ONE; GSYM TWO] 
THEN SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = 
(if p then x else I y)`] THEN  ONCE_REWRITE_TAC[MESON[] 
`(if p then f1 x else f2 y) = (if p then f1  else f2 ) (if p then  x else  y)`]
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] 
`((x = 1) ==> f x = q) ==> (if (x = 1) then q else f x) = f x `;
ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
ONCE_SIMP_TAC[MESON[ARITH] `(if (i=2) then q1 else (if (i=4) then q2 else q3)) =
(if (i=4) then q2 else (if (i=2) then q1 else q3))`;ARITH] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = (if p then x else I y)`] 
THEN ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = (if p then f1  else f2 ) 
(if p then  x else  y)`] THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[MESON[keylem] `((x = 4) ==> f x = q) ==> (if (x = 4) then q else f x) = f x `
;ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;GSYM pos] THEN SIMP_TAC[COP_SMUL_THM;COP_ADD_THM;
CNJ_CX;GSYM is_beam_splitter;pos;COP_TENSOR_CFUN; GSYM(MESON[] 
`(if p then f1 x else f2 x) = (if p then f1  else f2 ) x`);GSYM CFUN_LAMBDA_APP]          
THEN ASM_SIMP_TAC[ADD_LINCOP; MUL_LINCOP;SUB_LINCOP;COP_TENSOR_LINEAR;
SMUL_LINCOP;ETA_AX;ABS_SIMP;MESON[is_linear_cop] 
`!a x op. is_linear_cop op ==> op (a % x + b % y) = a % op x + b % op y`]
THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[COND_RATOR;I_THM] THEN
SIMP_TAC[COP_TENSOR_CFUN;COND_RATOR;I_THM;ARITH;GSYM CFUN_LAMBDA_APP]
THEN SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_MUL] THEN
ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\  1 <= 2 `;
proj_tensor_m_n;ARITH_RULE `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN 
ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN ASM_SIMP_TAC [ARITH_RULE `  
i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN  
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV 
[(SPEC_V ("j","j")) (MESON[COP_SMUL_LID] 
`(cr (j$1) = (Cx(&1) % cr (j$1))) /\ (cr (j$4) = (Cx(&1) % cr (j$4))) `)])))
THEN IMP_REWRITE_TAC[MESON[is_beam_splitter;lemma1;COP_SMUL_THM] `
(is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2))
,ten,c$1,1,c$4,4,j$1,1,j$4,4)/\ (is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),ten,a$1,1,a$4,4,b$1,1,b$4,4)) /\ 
vac (a$1) = vac (b$3) /\  b$4 = d$1 /\ vac (j$4) = vac (c$3)) ==> 
(cr (b$1) (vac (b$3)) = fock (b$1) 1  /\ cr (d$1) (vac (b$3)) = 
 fock (d$1) 1 /\ cr (c$4) (vac (c$3)) =  fock (c$4) 1 /\ cr (c$1) (vac (c$3)) =  
 fock (c$1) 1 /\ cr (b$1) (cr (b$1) (vac (b$3))) = cr (b$1) (cr (b$1) (vac (b$1)))
 /\ cr (d$1) (cr (d$1) (vac (b$3))) = cr (d$1) (cr (d$1) (vac (d$1))) 
 /\ inv (Cx (sqrt (&2))) % (cr (c$1) ** cr (c$1)) (vac (c$3)) = fock (c$1) 2
 /\ inv (Cx (sqrt (&2))) % (cr (c$4) ** cr (c$4)) (vac (c$3)) = fock (c$4) 2)`] 
 THEN IMP_REWRITE_TAC[CZ_lemma1;CZ_lemma2]  THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `]  
THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d]  
THEN ASM_SIMP_TAC[ARITH_RULE ` (i <= 6 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N)) `;LAMBDA_BETA]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]  THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 6) /\ ( 1 <= i + 2) /\ 
( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>(i <= 2 ==> 
(i + 6 <= dimindex (:N)))) `] THEN REWRITE_TAC[ ARITH_RULE 
`(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) /\ 
(((i:num) + j <= k) <=> (if (j <= k) then  i <= k - j else F)) ` ] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d]
THEN ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\  1 <= 3  `;proj_tensor_m_n]
THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x else (if i = 2 then y
else if i = 5 then z1 else z2)) = (if(i<=3) then (if i = 1 then x else (if i = 2
then y else z2)) else (if i = 5 then z1 else z2))) /\ ((if i = 2 then x 
else (if i = 5 then x1 else if i = 1 then x2 else x4)) = 
(if(i<=3) then (if i = 1 then x2 else if i = 2 then x else x4) else ( 
if i = 5 then x1 else x4))) /\ ((if i = 2 then x else (if i = 5 then x1
else if i = 4 then x2 else x4)) = (if(i<=3) then (if i = 2 then x else x4) 
else (if i = 4 then x2 else if i = 5 then x1 else x4))) /\
((if i = 2 then x else (if i = 5 then x1 else if i = 4 then x2 else 
if i = 1 then x3 else x4)) = (if(i<=3) then (if i = 1 then x3 else (if i = 2
then x else x4)) else (if i = 4 then x2 else if i = 5 then x1 else x4))) /\
((if i = 4 then x2 else if i = 1 then x3 else if i = 2 then x else 
(if i = 5 then x1 else x4)) = (if(i<=3) then (if i = 1 then x3 else (if i = 2
then x else x4)) else (if i = 4 then x2 else if i = 5 then x1 else x4))) /\
((if i = 1 then x3 else if i = 4 then x2 else if i = 2 then x else 
(if i = 5 then x1 else x4)) = (if(i<=3) then (if i = 1 then x3 else (if i = 2
then x else x4)) else (if i = 4 then x2 else if i = 5 then x1 else x4))) /\ 
((if i = 4 then x1 else (if i = 2 then x2 else if i = 5 then x3 else x4)) = 
(if(i<=3) then (if i = 2 then x2 else x4) else (if i = 4 then x1 else 
(if i = 5 then x3 else x4))))`] THEN CONV_TAC NUM_REDUCE_CONV   
THEN ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (q i)  else (p i)) = 
(if i <= 3 then (\j. q j) i else (\j. p j) i)`]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] 
THEN IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `]
THEN ONCE_SIMP_TAC[(ISPECL [`3`] tensor_1mlem1d)]
THEN ASM_SIMP_TAC [ARITH_RULE ` 3 + 3 = 6`]
THEN ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
((8 <= dimindex (:N)) ==>(i <= 3 ==> i + 3 <= dimindex (:N)) )`]
THEN SIMP_TAC[ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 1) <=> F) 
/\ ((i + 3 = 5) <=> (i=2)) /\ ((i + 3 = 4) <=> (i=1))`] THEN
IMP_REWRITE_TAC[lemma_HH; ARITH_RULE `8 <= dimindex (:N) 
    ==>   2 <= dimindex (:N)`] THEN
 IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_1mlem1d)]
THEN SIMP_TAC[MESON[ARITH]`
(if i = 0 then x  else if i = 2 then y else x) = (if i = 2 then y else x) /\
(if i = 0 then x else if i = 1 then y else if i = 2 then z else x) =
(if i = 2 then z else if i = 1 then y else x) /\
(if i = 0 then x else if i = 2 then y else if i = 1 then z else x) =
(if i = 2 then y else if i = 1 then z else x) /\
(if i = 1 then y else if i = 2 then z else x) = 
(if i = 2 then z else if i = 1 then y else x)`] THEN        
IMP_REWRITE_TAC[NS_2_PROJ_0;NS_2_PROJ_1;NS_2_PROJ_2;NS_0_PROJ_0;
NS_0_PROJ_2;NS_0_PROJ_1;NS_1_PROJ_1;NS_1_PROJ_2;NS_1_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[] `q$1 = c$4 /\ 
vac (d$3) = vac (b$3) /\ q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
 m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (c$5) 1 else vac (c$3)))
 (tensor 3 (lambda i. if i = 2 then fock (d$2) 1 else vac (b$3))) = 
 m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (q$2) 1 else vac (q$3)))
  (tensor 3 (lambda i. if i = 2 then fock (d$2) 1 else vac (d$3))) /\
m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (c$5) 1
   else if i = 1 then fock (c$4) 2 else vac (c$3)))
   (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
   else if i = 1 then fock (d$1) 2 else vac (b$3))) = 
 m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (q$2) 1
    else if i = 1 then fock (q$1) 2 else vac (q$3)))
   (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
   else if i = 1 then fock (d$1) 2 else vac (d$3))) /\ 
m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (c$5) 1
   else if i = 1 then fock (c$4) 1 else vac (c$3)))
   (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
   else if i = 1 then fock (d$1) 1 else vac (b$3))) = 
 m_modes_pro (tensor 3 (lambda i. if i = 2 then fock (q$2) 1
   else if i = 1 then fock (q$1) 1 else vac (q$3)))
   (tensor 3 (lambda i. if i = 2 then fock (d$2) 1
   else if i = 1 then fock (d$1) 1 else vac (d$3)))`)] THEN      
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;
CFUN_SMUL_RZERO;CFUN_ADD_RID;CFUN_ADD_LID]  THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;cfun_zero;GSYM K_DEF;
CFUN_SMUL_RZERO;CFUN_ADD_RID;CFUN_ADD_LID] THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;
CFUN_SMUL_RZERO;CFUN_ADD_RID;CFUN_ADD_LID] THEN
SIMP_TAC [CFUN_SMUL] THEN REWRITE_TAC [CFUN_ARITH 
`!f1:A^N->complex a1 a2.  ((a1 * f1 y) * a2 * f2 x) * f3 z  = 
(a1*a2) * ((f1 y * f2 x) * f3 z) /\ (a3 * (a1 * f1 y) * a2 * f2 x) * f3 z  = 
(a1*a2*a3) * ((f1 y * f2 x) * f3 z)`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)  `]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN 
ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN 
ASM_SIMP_TAC[ARITH_RULE ` ((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] 
THEN SIMP_TAC[ARITH_RULE 
` (i - 3 = 1  <=> i = 4) /\  (i - 6 = 1  <=> i = 7) /\
(i - 3 = 2  <=> i = 5) /\ (i - 3 = 3 <=> i = 6)`] THEN
IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ 
(i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (p3 <= 3) /\ (3 < p2)) ==> (if (i <= 3) 
 then if (i = p1) then q1 else (if i = p3 then q4 else q2) 
 else if (i = p2) then q3 else q2) =
(if (i = p1) then q1 else if (i = p3) then q4 else 
(if (i = p2) then q3 else q2)) `;ARITH]
THEN IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ (i = p2)) = F) 
/\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (3 < p3) /\ (3 < p2)) ==> (if (i <= 3) then if (i = p1) 
 then q1 else q2  else if (i = p2) then q3  else (if i = p3 then q4 else q2))
 = (if (i = p1) then q1 else (if (i = p2) then q3 else if (i = p3) 
then q4 else q2)) `;ARITH] THEN IMP_REWRITE_TAC[MESON[ARITH_RULE 
`((p1 <= 3) /\ (3 < p2)) ==> (((~(i <= 3) /\ (i = p1)) = F ) /\ 
(((i <= 3) /\ (i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F))`] 
 `((p1 <= 3) /\ (p3 <= 3) /\ (3 < p4) /\ (3 < p2)) ==> (if (i <= 3) 
 then if (i = p1) then q1 else (if i = p3 then q2 else q3)  
 else if (i = p2) then q4  else (if i = p4 then q5 else q3)) =
(if (i = p1) then q1 else if (i = p3) then q2 else (if (i = p2) 
then q4 else if (i = p4) then q5 else q3)) `;ARITH] THEN
 ONCE_ASM_SIMP_TAC[tensor_1mlem1d]  THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==> 
( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`]
`(if i <= 8 /\ 1 <= i then if i <= 6 then 
if i = 1 then x1 else if i = 2  then x2
 else if i = 5  then x3 else x4 else if i = 7 then x5 else 
 x6 else x7) = (if i <= 8 /\ 1 <= i then if i = 1 then x1 else 
 if i = 2 then x2 else if i = 5  then x3  else if i = 7 then x5 
 else if i = 8 then x6 else x4 else x7) /\
(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 1 then x1 else 
if i = 2  then x2 else if i = 4  then x8 else if i = 5  then 
x3 else x4 else if i = 7 then x5 else x6 else x7) = 
(if i <= 8 /\ 1 <= i then if i = 1 then x1 else if i = 4 then x8 else if i = 2  
then x2 else if i = 5  then x3  else if i = 7 then x5 else 
if i = 8 then x6 else x4 else x7) /\
(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 2  then x2
 else if i = 4 then x1 else if i = 5  then x3 else x4 else 
 if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 4 then x1 else if i = 2  then x2
 else if i = 5  then x3  else if i = 7 then x5 else if i = 8 then 
 x6 else x4 else x7)`] THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]
THEN SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;CFUN_SMUL_ASSOC;GSYM CX_MUL;
CFUN_ADD_LID;GSYM CX_NEG;CNJ_CX;GSYM CX_ADD] THEN
SIMP_TAC [GSYM lemma1;is_beam_splitter] THEN
SIMP_TAC [GSYM is_beam_splitter;COP_MUL_THM;COP_SMUL_THM] THEN   
IMP_REWRITE_TAC[CZ_lemma4; CZ_lemma3] THEN
ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN  
ASM_SIMP_TAC[ARITH_RULE ` (i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N)) `;LAMBDA_BETA] THEN
ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = 
(if p then x else I y)`] THEN ONCE_REWRITE_TAC[MESON[] 
`(if p then f1 x else f2 y) = (if p then f1  else f2 ) (if p then  x else  y)`]
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[ARITH;
COND_ID;MESON[keylem] `((x = 1) ==> f x = q) ==> 
(if (x = 1) then q else f x) = f x `] THEN IMP_REWRITE_TAC[ARITH;
COND_ID;keylem;GSYM COP_TENSOR_CFUN] THEN ONCE_REWRITE_TAC[MESON[I_THM] 
`(if p then (x:bqs) else y) = (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN 
ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] 
`((x = 4) ==> f x = q) ==> (if (x = 4) then q else f x) = f x `;
ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN SIMP_TAC[GSYM is_beam_splitter;
GSYM pos] THEN SIMP_TAC[CFUN_SMUL_ASSOC;CFUN_SMUL_DIS;
GSYM CX_NEG;COP_ADD_THM;CNJ_CX;GSYM is_beam_splitter;COP_SMUL_THM;
pos;COP_TENSOR_CFUN;GSYM CFUN_LAMBDA_APP] THEN 
ASM_SIMP_TAC[ADD_LINCOP; MUL_LINCOP;SUB_LINCOP;COP_TENSOR_LINEAR;
SMUL_LINCOP;ETA_AX;ABS_SIMP;MESON[is_linear_cop] 
`!a x op. is_linear_cop op ==> op (a % x + b % y) = a % op x + b % op y`]
THEN SIMP_TAC[COND_RATOR;I_THM;ARITH] THEN
SIMP_TAC[COP_TENSOR_CFUN;COND_RATOR;I_THM;ARITH;GSYM CFUN_LAMBDA_APP]
THEN SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_MUL]    
THEN SIMP_TAC [MESON[ARITH] `((if i = 4 then x1 else if i = 1 then x2 
else if i = 2 then x3 else (if i = 5 then x4 else x5)) = 
(if i = 1 then x2 else if i = 4 then x1 
else if i = 2 then x3 else (if i = 5 then x4 else x5)) /\
(if i = 2 then x2 else if i = 1 then x1 
else if i = 4 then x4 else (if i = 5 then x5 else x6)) = 
(if i = 1 then x1 else if i = 4 then x4 
else if i = 2 then x2 else (if i = 5 then x5 else x6)) )`] THEN
SIMP_TAC [MESON[ARITH] `((if i = 1 then x1 else if i = 4 then x2 
else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then x7 
else if i = 8 then x8 else x1) = (if i = 4 then x2 
else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then x7 
else if i = 8 then x8 else x1) )`] THEN 
SIMP_TAC [CFUN_ADD_SYM;CFUN_ADD_ASSOC;GSYM CFUN_ADD_RDISTRIB;CFUN_SMUL_LID;
  CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun). 
  b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a /\ 
 f + b%a + c%a +d = f + (b+c) % a +d`;GSYM CX_ADD;CFUN_ADD_AC] THEN  
SIMP_TAC[GSYM CX_MUL; GSYM CX_ADD; GSYM CX_SUB;GSYM CX_INV;
CFUN_ADD_AC;SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;
REAL_MUL_SYM;GSYM real_sub;GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;
REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;GSYM CX_ADD;
REAL_FIELD `&1 / &8 + &1 / &8 = &1 / &4 /\ &1 / &2 * &1 / &2 pow 2 = &1 / &8 
/\ &1 / &2 * &1 / &8  = &1 / &16 /\ --(&1 / &16) + -- (&1 / &16) 
-  &1 / &16 - &1 / &16 = -- (&1 / &4)`;REAL_MUL_RID;GSYM CFUN_ADD_RDISTRIB;
CFUN_ADD_LID;REAL_FIELD `inv (sqrt (&2)) = &1 / sqrt (&2) `;
REAL_ADD_LINV;REAL_MUL_LZERO;REAL_DIV_RMUL;REAL_MUL_RZERO;REAL_ADD_LID;
REAL_ADD_RID;REAL_SUB_RZERO;REAL_SUB_REFL;REAL_NEG_NEG;REAL_MUL_LNEG;
MESON[GSYM SQRT_INJ;REAL_DIV_RMUL;REAL_FIELD `~(&2 = &0)` ;SQRT_0]  
`((&1 / sqrt (&2)) * sqrt (&2) = &1) `]);;



let CZ_GATE_11 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LV (cz1) else LV (cz2)):bqs^N)) =
(Cx (--(&1 / &4))) % (tensor 2 ((lambda i.  if i = 1 then 
LV (cz3) else LV (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[CZ_INPUTS;CZ_11;CZ_OUTPUTS]);;
(****************************************************************************)
(* The projection of CZ outputs for one 1-qubit fock and one vacuum state inputs *)
(****************************************************************************)


let CZ_01 = prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) ==>  
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
if i = 1 then fock (c$1) 1 else  if i = 7 then fock (a$2) 1 else 
if i = 8 then vac (a$3) else if i = 5 then fock (c$5) 1 else 
vac (c$3)):bqs^N))) + (m_modes_pro (tensor 8 ((lambda i. if i = 2 then 
fock (c$2) 1 else if i = 4 then fock (c$4) 1 else if i = 7 then 
fock (a$2) 1 else if i = 8 then vac (a$3) else if i = 5 then 
fock (c$5) 1 else vac (c$3)):bqs^N)))) (tensor 8 ((lambda i.  if i = 4 then 
fock (a$4) 1 else if i = 2 then fock (b$2) 1 else  if i = 7 then fock (a$2) 1 
else if i = 8 then vac (a$3) else if i = 5 then fock (b$5) 1 else 
vac (b$3)):bqs^N)) = Cx (&1 / &4) % tensor 8 ((lambda i. if i = 4 then 
fock (j$4) 1 else if i = 2 then fock (c$2) 1 else if i = 5 then fock (c$5) 1 
else if i = 7 then fock (a$2) 1 else if i = 8 then vac (a$3) else vac (c$3)):bqs^N)`,
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;is_CZ_model] THEN REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 SIMP_TAC[is_beam_splitter;
LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC] THEN 
SIMP_TAC[GSYM is_beam_splitter] THEN SIMP_TAC[cop_pow;
COP_MUL_RID;ONE;FACT;TWO] THEN SIMP_TAC[GSYM ONE; GSYM TWO] THEN
SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = 
(if p then x else I y)`] THEN ONCE_REWRITE_TAC[MESON[] 
`(if p then f1 x else f2 y) = (if p then f1  else f2 ) (if p then  x else  y)`]
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] 
`((x = 4) ==> f x = q) ==> (if (x = 4) then q else f x) = f x `;ARITH;COND_ID] 
THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN
SIMP_TAC[GSYM is_beam_splitter;GSYM pos] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN 
ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD] THEN
ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\  1 <= 2  `;proj_tensor_m_n;ARITH_RULE 
    `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
    <=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE `  
    i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN  
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
CONV_TAC (RAND_CONV(RAND_CONV(ONCE_REWRITE_CONV 
[(SPEC_V ("j","j")) (MESON[COP_SMUL_LID] 
`cr (j$4) = (Cx(&1) % cr (j$4))`)])))
THEN IMP_REWRITE_TAC[MESON[is_beam_splitter;lemma1] `
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)),ten,c$1,1,c$4,4,j$1,1,j$4,4) /\ 
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)),ten,a$1,1,a$4,4,b$1,1,b$4,4) /\ 
vac (a$1) = vac (b$3) /\  b$4 = d$1/\ vac (j$4) = vac (c$3) ==> 
(cr (c$1) (vac (c$3)) =  fock (c$1) 1 /\ cr (c$4) (vac (c$3)) =  fock (c$4) 1 /\ 
cr (b$1) (vac (b$3)) = fock (b$1) 1  /\ cr (d$1) (vac (b$3)) =  fock (d$1) 1)`]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `( 1 <= i + 6) /\ ( 1 <= i + 2) /\ 
(1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 6 <= dimindex (:N))))`] 
THEN REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> 
(if (j <= k) then  i = k - j else F)) /\ (((i:num) + j <= k) <=> 
(if (j <= k) then  i <= k - j else F)) ` ] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d]
THEN ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\  1 <= 3`;proj_tensor_m_n] 
THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x else (if i = 2 then y
else if i = 5 then z1 else z2)) = (if(i<=3) then (if i = 1 
then x else (if i = 2 then y else z2)) else 
(if i = 5 then z1 else z2))) /\ ((if i = 2 then x else (if i = 1 then y
else if i = 5 then z1 else z2)) = 
(if(i<=3) then (if i = 1 then y else (if i = 2
then x else z2)) else (if i = 5 then z1 else z2)))
/\ ((if i = 4 then x1 else (if i = 2 then x2
else if i = 5 then x3 else x4)) = (if(i<=3) then (if i = 2 then x2 else x4)
else (if i = 4 then x1 else (if i = 5 then x3 else x4)))) /\ ((if i = 2 then x 
else if i = 5 then z1 else (if i = 4 then y else z2)) = 
(if(i<=3) then (if i = 2 then x else z2) else (if i = 5 then z1 else (if i = 4
then y else z2)))) /\ ((if i = 2 then x 
else if i = 4 then z1 else (if i = 5 then y else z2)) = 
(if(i<=3) then (if i = 2 then x else z2) else (if i = 4 then z1 else (if i = 5
then y else z2))))`] THEN ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (q i)
else (p i)) = (if i <= 3 then (\j. q j) i else (\j. p j) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE ` 3 + 3 = 6`] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
((6 <= dimindex (:N)) ==>(i <= 3 ==> i + 3 <= dimindex (:N)) )`] 
THEN SIMP_TAC[ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 1) <=> F) /\ 
((i + 3 = 5) <=> (i=2)) /\ ((i + 3 = 4) <=> (i=1))`] THEN
ONCE_SIMP_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN
IMP_REWRITE_TAC[CONV_RULE(SIMP_CONV[GSYM lemma1]) lemma_VH; 
ARITH_RULE `8 <= dimindex (:N) ==>   2 <= dimindex (:N)`] THEN
SIMP_TAC[MESON[ARITH]`
(if i = 0 then x  else if i = 2 then y else x) = 
(if i = 2 then y else x) /\
(if i = 0 then x else if i = 1 then y else if i = 2 then z else x) =
(if i = 2 then z else if i = 1 then y else x) /\
(if i = 0 then x else if i = 2 then y else if i = 1 then z else x) =
(if i = 2 then y else if i = 1 then z else x) /\
(if i = 1 then y else if i = 2 then z else x) = 
(if i = 2 then z else if i = 1 then y else x)`] THEN
IMP_REWRITE_TAC[NS_0_PROJ_0;NS_0_PROJ_1;NS_1_PROJ_1;NS_1_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[] `q$1 = c$4 /\ 
vac (d$3) = vac (b$3) /\ q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
(m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 
else vac (c$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then 
fock (d$2) 1 else vac (b$3)):bqs^N)) = m_modes_pro (tensor 3 ((lambda i.
 if i = 2 then fock (q$2) 1 else vac (q$3)):bqs^N)) (tensor 3 ((lambda i. 
 if i = 2 then fock (d$2) 1 else vac (d$3)):bqs^N)) /\
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1
else if i = 1 then fock (c$4) 1 else vac (c$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (b$3)):bqs^N)) =
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1
else if i = 1 then fock (q$1) 1 else vac (q$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)))`)]THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;
CFUN_SMUL_RZERO;CFUN_ADD_RID;CFUN_ADD_LID] THEN
REWRITE_TAC [CFUN_ARITH 
`!f1:A^N->complex a1 a2. ((a1 % f1) y * (a2 % f2) x) * f3 z = 
(a1*a2) * ((f1 y * f2 x) * f3 z) `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`] 
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d]         
THEN ASM_SIMP_TAC[ARITH_RULE `((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) 
/\ (~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;
LAMBDA_BETA] THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN 
SIMP_TAC[ARITH_RULE `(i - 3 = 1 <=> i = 4) /\ (i - 6 = 1 <=> i = 7) /\
(i - 3 = 2  <=> i = 5) /\ (i - 3 = 3 <=> i = 6)`] THEN
IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ (i = p2)) = F) 
/\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (3 < p3) /\ (3 < p2)) ==> 
 (if (i <= 3) then if (i = p1) 
 then q1 else q2  else if (i = p2) then q3  
 else (if i = p3 then q4 else q2)) =
(if (i = p1) then q1 else (if (i = p2) then q3 else if (i = p3) 
then q4 else q2)) `;ARITH] THEN 
IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ 
(i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (p3 <= 3) /\ (3 < p2)) ==> (if (i <= 3) 
 then if (i = p1) then q1 else (if i = p3 then 
q4 else q2)  else if (i = p2) then q3 else q2) =
(if (i = p1) then q1 else if (i = p3) then q4 
else (if (i = p2) then q3 else q2)) `;ARITH] THEN
ONCE_ASM_SIMP_TAC[tensor_1mlem1d]   THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==> 
( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`]
`(if i <= 8 /\ 1 <= i then if i <= 6 then 
if i = 1 then x1 else if i = 2  then x2
 else if i = 5  then x3 else x4 else if i = 7 
then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 1 then x1 
else if i = 2   then x2
 else if i = 5  then x3  else if i = 7 then x5 
else if i = 8 then x6 else x4 else x7) /\
(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 2  then x2
 else if i = 4 then x1 else if i = 5  then 
x3 else x4 else if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 4 then 
x1 else if i = 2   then x2
 else if i = 5  then x3  else if i = 7 then 
x5 else if i = 8 then x6 else x4 else x7)`]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]
THEN SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;
CFUN_SMUL_ASSOC;GSYM CX_MUL;
CFUN_ADD_LID;GSYM CX_NEG;CNJ_CX;GSYM CX_ADD] THEN
SIMP_TAC [GSYM lemma1;is_beam_splitter] THEN
SIMP_TAC [GSYM is_beam_splitter;COP_MUL_THM;
COP_SMUL_THM;ETA_AX] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = 
(if p then x else I y)`] THEN 
   ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`]
  THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
 SIMP_TAC[MESON[keylem] `((x = 4) ==> f x = q) ==>
 (if (x = 4) then q else f x) = f x `;ARITH;COND_ID] THEN
IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN
SIMP_TAC[GSYM is_beam_splitter] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;COP_TENSOR_CFUN] THEN
 SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
GSYM CX_MUL;GSYM CX_NEG;CNJ_CX] THEN
SIMP_TAC [MESON[ARITH] `((if i = 4 then x1 else if i = 1 then x2 
else if i = 2 then x3 else if i = 5 then x4 else if i = 7 
then x7 else if i = 8 then x8 else x2) = (if i = 4 then x1 
    else if i = 2 then x3 else if i = 5 then x4 
else if i = 7 then x7 else if i = 8 then x8 else x2) )`] THEN
SIMP_TAC [MESON[ARITH] `((if i = 2 then x2 else if i = 4 then x1 
else (if i = 5 then x5 else x6)) = ( if i = 4 then x1 
else if i = 2 then x2 else (if i = 5 then x5 else x6)) )`] THEN
SIMP_TAC [CFUN_ADD_SYM;CFUN_ADD_ASSOC;GSYM CFUN_ADD_RDISTRIB;
REAL_NEG_NEG;CFUN_SMUL_LID;
 CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun). 
b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a /\ 
f + b%a + c%a +d = f + (b+c) % a +d`;GSYM CX_ADD;CFUN_ADD_AC]  THEN
SIMP_TAC[SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;
SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;
REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_FIELD ` &1 / &8 - -- (&1 / &8) = &1 / &4 
/\ &1 / &2 * &1 / &2 pow 2 = &1 / &8 `;
CFUN_ADD_LID;REAL_SUB_REFL;CFUN_ADD_RID]);;


let CZ_GATE_01 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LH (cz1) else LV (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 LH (cz3) else LV (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[CZ_INPUTS;CZ_01;CZ_OUTPUTS]);;
(****************************************************************************)
(* The projection of CZ outputs for one vacuum state and one 1-qubit fock inputs *)
(****************************************************************************)



let CZ_10 = prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) ==>  
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  (if i = 1 then fock (c$1) 1 else (if i = 5 then fock (c$5) 1 else 
if i = 7 then vac (a$2) else if i = 8 then fock (a$3) 1  else 
vac (c$3)))):bqs^N))) + (m_modes_pro (tensor 8 ((lambda i. 
if i = 2 then fock (c$2) 1 else (if i = 5 then fock (c$5) 1 else  
(if i = 4 then fock (c$4) 1 else if i = 7 then vac (a$2) else 
if i = 8 then fock (a$3) 1  else vac (c$3)))):bqs^N))))
(tensor 8 ((lambda i.  if i = 1 then fock (a$1) 1 else 
(if i = 2 then fock (b$2) 1 else (if i = 5 then fock (b$5) 1 else 
if i = 7 then vac (a$2) else if i = 8 then fock (a$3) 1  else 
vac (b$3)))):bqs^N)) = Cx (&1 / &4) % tensor 8 ((lambda i. 
if i = 1 then fock (j$1) 1 else if i = 2 then fock (c$2) 1 else 
if i = 5 then fock (c$5) 1 else if i = 7 then vac (a$2) else 
if i = 8 then fock (a$3) 1  else vac (c$3)):bqs^N)`,
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;
RIGHT_AND_FORALL_THM;is_CZ_model] THEN
REPEAT GEN_TAC THEN
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
SIMP_TAC[is_beam_splitter;LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN SIMP_TAC[GSYM is_beam_splitter] THEN
SIMP_TAC[cop_pow;COP_MUL_RID;ONE;FACT;TWO] THEN
SIMP_TAC[GSYM ONE; GSYM TWO] THEN
 SIMP_TAC[ MULT_CLAUSES;SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = 
(if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`]
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[MESON[keylem] `((x = 1) ==> f x = q) ==> 
(if (x = 1) then q else f x) = f x `;ARITH;COND_ID] THEN
IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN
SIMP_TAC[GSYM is_beam_splitter;GSYM pos] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN 
ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD] THEN
ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\  1 <= 2  `;
proj_tensor_m_n;ARITH_RULE `(8 <= dimindex (:N) ==> 
 2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE `  
i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN  
    ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN
CONV_TAC (RAND_CONV(RAND_CONV(ONCE_REWRITE_CONV 
[(SPEC_V ("j","j")) (MESON[COP_SMUL_LID] 
`cr (j$1) = (Cx(&1) % cr (j$1))`)])))
THEN IMP_REWRITE_TAC[MESON[is_beam_splitter;lemma1] `
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),ten,c$1,1,c$4,4,j$1,1,j$4,4) /\ 
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)),ten,a$1,1,a$4,4,b$1,1,b$4,4) /\
vac (a$1) = vac (b$3) /\  b$4 = d$1/\ vac (j$4) = vac (c$3) ==> 
(cr (c$1) (vac (c$3)) =  fock (c$1) 1 
/\ cr (c$4) (vac (c$3)) =  fock (c$4) 1 /\
cr (b$1) (vac (b$3)) = fock (b$1) 1  
/\ cr (d$1) (vac (b$3)) =  fock (d$1) 1)`]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 6) 
/\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 6 <= dimindex (:N)))) `] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) 
<=> (if (j <= k) then  i = k - j else F))  /\ 
(((i:num) + j <= k) <=> (if (j <= k) then  i <= k - j else F)) ` ] THEN
CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\  1 <= 3  `;proj_tensor_m_n]
THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x 
    else (if i = 2 then y
    else if i = 5 then z1 else z2)) = 
    (if(i<=3) then (if i = 1 then x else (if i = 2
    then y else z2)) else (if i = 5 then z1 else z2)))
    /\ ((if i = 2 then x 
    else (if i = 1 then y
    else if i = 5 then z1 else z2)) = 
    (if(i<=3) then (if i = 1 then y else (if i = 2
    then x else z2)) else (if i = 5 then z1 else z2)))
    /\ ((if i = 4 then x1 else (if i = 2 then x2
    else if i = 5 then x3 else x4)) = 
    (if(i<=3) then (if i = 2 then x2 else x4)
    else (if i = 4 then x1 else 
    (if i = 5 then x3 else x4))))
    /\ ((if i = 2 then x 
    else if i = 5 then z1 else (if i = 4 then y else z2)) = 
    (if(i<=3) then (if i = 2 then x else z2) 
    else (if i = 5 then z1 else (if i = 4
    then y else z2))))`] THEN
ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (q i)
    else (p i)) = 
    (if i <= 3 then (\j. q j) i
    else (\j. p j) i)`] THEN
    IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
    ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
    ASM_SIMP_TAC [ARITH_RULE ` 3 + 3 = 6`] THEN
    ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
    ((6 <= dimindex (:N)) ==>
    (i <= 3 ==> i + 3 <= dimindex (:N)) )`] THEN
    SIMP_TAC[ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 1) <=> F) 
   /\ ((i + 3 = 5) <=> (i=2)) /\ 
    ((i + 3 = 4) <=> (i=1))`] THEN
ONCE_SIMP_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN
IMP_REWRITE_TAC[CONV_RULE(SIMP_CONV[GSYM lemma1]) lemma_HV;
 ARITH_RULE `8 <= dimindex (:N) 
==>   2 <= dimindex (:N)`] THEN
SIMP_TAC[MESON[ARITH]`
(if i = 0 then x  else if i = 2 then y else x) = 
(if i = 2 then y else x) /\
(if i = 0 then x else if i = 1 then y else 
if i = 2 then z else x) =
(if i = 2 then z else if i = 1 then y else x) /\
(if i = 0 then x else if i = 2 then y else 
if i = 1 then z else x) =
(if i = 2 then y else if i = 1 then z else x) /\
(if i = 1 then y else if i = 2 then z else x) = 
(if i = 2 then z else if i = 1 then y else x)`] THEN
IMP_REWRITE_TAC[NS_0_PROJ_0;NS_0_PROJ_1;NS_1_PROJ_1;
NS_1_PROJ_0;REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[]
`q$1 = c$4 /\ vac (d$3) = vac (b$3) /\ q$3 = c$6 
/\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
(m_modes_pro (tensor 3 ((lambda i. if i = 2 
then fock (c$5) 1 else vac (c$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 
else vac (b$3)):bqs^N))   
=  m_modes_pro (tensor 3 ((lambda i. if i = 2 
then fock (q$2) 1 else vac (q$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 
else vac (d$3)):bqs^N)) /\
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1
else if i = 1 then fock (c$4) 1 else vac (c$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (b$3)):bqs^N)) =
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1
else if i = 1 then fock (q$1) 1 else vac (q$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)))`)]THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;
CFUN_SMUL_RZERO;CFUN_ADD_RID;CFUN_ADD_LID] THEN
REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2.  
((a1 % f1) y * (a2 % f2) x) * f3 z = 
(a1*a2) * ((f1 y * f2 x) * f3 z) `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex.
(\y. a * f1 y) = a % (\y. f1 y)  `] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV
THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN 
ASM_SIMP_TAC[ARITH_RULE ` ((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) 
/\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ 
(~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]
THEN SIMP_TAC[ARITH_RULE ` (i - 3 = 1  <=> i = 4) 
/\  (i - 6 = 1  <=> i = 7) /\
(i - 3 = 2  <=> i = 5) /\ 
(i - 3 = 3 <=> i = 6)`] THEN
IMP_REWRITE_TAC[MESON[ARITH_RULE 
`((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ (i = p2)) = F) 
/\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (3 < p3) /\ (3 < p2)) 
==> (if (i <= 3) then if (i = p1) 
 then q1 else q2  else if (i = p2) then q3 
 else (if i = p3 then q4 else q2)) =
(if (i = p1) then q1 else (if (i = p2) 
then q3 else if (i = p3) 
then q4 else q2)) `;ARITH] THEN 
IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ 
(i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F)) ` ] 
 `((p1 <= 3) /\ (p3 <= 3) /\ (3 < p2)) ==> (if (i <= 3) 
 then if (i = p1) then q1 else (if i = p3 then q4 else q2)
  else if (i = p2) then q3 else q2) =
(if (i = p1) then q1 else if (i = p3) then q4 else
 (if (i = p2) then q3 else q2)) `;ARITH] THEN
ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==>
 ( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`]
`(if i <= 8 /\ 1 <= i then if i <= 6 then 
if i = 1 then x1 else if i = 2  then x2
 else if i = 5  then x3 else x4 else if i = 7 
then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 1 then x1 
else if i = 2  then x2
 else if i = 5  then x3  else if i = 7 then x5 
else if i = 8 then x6 else x4 else x7) /\
(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 2  then x2
 else if i = 4 then x1 else if i = 5  then x3 else x4 
else if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 4 then x1 else if i = 2 then x2
 else if i = 5  then x3  else if i = 7 then x5 else 
if i = 8 then x6 else x4 else x7)`]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d]
THEN SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;
CFUN_SMUL_ASSOC;GSYM CX_MUL;
CFUN_ADD_LID;GSYM CX_NEG;CNJ_CX;GSYM CX_ADD] THEN
SIMP_TAC [GSYM lemma1;is_beam_splitter] THEN
SIMP_TAC [GSYM is_beam_splitter;COP_MUL_THM;
COP_SMUL_THM;ETA_AX] THEN
ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) =
(if p then x else I y)`] THEN 
 ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) =
 (if p then f1  else f2 ) (if p then  x else  y)`]
        THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
SIMP_TAC[MESON[keylem] `((x = 1) ==> f x = q) ==> 
(if (x = 1) then q else f x) = f x `;ARITH;COND_ID] THEN
IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN
SIMP_TAC[GSYM is_beam_splitter] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;
COP_ADD_THM;CNJ_CX;COP_SMUL_THM;COP_TENSOR_CFUN] THEN
 SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;
GSYM CX_MUL;GSYM CX_NEG;CNJ_CX] THEN
SIMP_TAC [MESON[ARITH] `((if i = 1 then x1 else if i = 4 then x2 
else if i = 2 then x3 else if i = 5 then x4 else 
if i = 7 then x7 else if i = 8 then x8 else x2) = 
(if i = 1 then x1 else if i = 2 then x3 else if i = 5 
then x4 else if i = 7 then x7 else if i = 8 then x8 else x2)  )`] THEN
SIMP_TAC [MESON[ARITH] `((if i = 2 then x2 else if i = 1 then x1 
else (if i = 5 then x5 else x6)) = ( if i = 1 then x1 
else if i = 2 then x2 else (if i = 5 then x5 else x6)) )`] THEN
SIMP_TAC [CFUN_ADD_SYM;CFUN_ADD_ASSOC;GSYM CFUN_ADD_RDISTRIB;
CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun). 
b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a /\ 
f + b%a + c%a +d = f + (b+c) % a +d`;GSYM CX_ADD;CFUN_ADD_AC]  THEN
SIMP_TAC[SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;
REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;
REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_FIELD ` &1 / &8 + &1 / &8 = &1 / &4 /\
 &1 / &2 * &1 / &2 pow 2 = &1 / &8 `;
CFUN_ADD_LID;REAL_SUB_REFL;CFUN_SMUL_LID] );;


 let CZ_GATE_10 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LV (cz1) else LH (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 LV (cz3) else  LH (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[CZ_INPUTS;CZ_10;CZ_OUTPUTS]);;

(****************************************************************************)
(* The projection of CZ outputs for one vacuum state and another quantum state *)
(*      where there is no photon in both the polarization modes             *)
(****************************************************************************)


let CZ_0vac = prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
  8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
 is_CZ_model (a, b, c, j,ten) ==>  
   (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
   (if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 else 
   (if i = 8 then vac (a$3) else vac (c$3))))):bqs^N)))
   (tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 else (if i = 5 then 
   fock (b$5) 1 else (if i = 7 then fock (a$2) 1 else (if i = 8 then vac (a$3) 
   else vac (b$3))))):bqs^N)) = (Cx (&1 / &4)) % tensor 8 (lambda i. if i = 2 then 
   fock (c$2) 1 else if i = 5 then fock (c$5) 1 else (if i = 7 then fock (a$2) 1 
   else (if i = 8 then vac (a$3) else vac (c$3))))`,    
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
is_CZ_model] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\  1 <= 2  `;proj_tensor_m_n;
ARITH_RULE `(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] 
THEN ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE `i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] 
THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN ASM_SIMP_TAC [ARITH_RULE 
`6 = 3 + 3 /\  1 <= 3  `;proj_tensor_m_n;ARITH_RULE 
`(6 <= dimindex (:N) ==>  3 <= dimindex (:N)) `] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3+3 <= dimindex (:N) 
<=> (6 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN    
SIMP_TAC [MESON[ARITH] `(if i = 2 then x
    else if i = 5 then y else z) = (if(i<=3) then (if i = 2
    then x else z) else (if i = 5 then y else z))`] THEN    
ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (if i = 2 then x else z)
    else (if i = 5 then y else z)) = 
    (if i <= 3 then (\j. if j = 2 then x else z) i
    else (\j. if j = 5 then y else z) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
((6 <= dimindex (:N)) ==>(i <= 3 ==> i + 3 <= dimindex (:N)) )`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE `(( i + 3 <= 3)  <=> (i = 0)) /\ 
((i + 3 = 2) <=> F) /\ ((i + 3 = 5) <=> (i=2))`] 
`(if i + 3 <= 3 then if i + 3 = 2 then x else z
 else if i + 3 = 5 then y else z) = if i = 2 then y else z`] THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN IMP_REWRITE_TAC[NS_0_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[] `vac (d$3) = vac (b$3) /\ 
q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 else 
vac (c$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 
else vac (b$3)):bqs^N)) =  m_modes_pro (tensor 3 ((lambda i. if i = 2 then 
fock (q$2) 1 else vac (q$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then 
fock (d$2) 1 else vac (d$3)):bqs^N))`)] THEN CONV_TAC NUM_REDUCE_CONV 
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3 <= dimindex (:N) 
<=> (3 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `( 1 <= i + 6) /\ ( 1 <= i + 2) /\ 
( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==> 
(i <= 2 ==> (i + 6 <= dimindex (:N))))`] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> 
(if (j <= k) then  i = k - j else F)) /\ 
(((i:num) + j <= k) <=> (if (j <= k) then  i <= k - j else F))`] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN 
IMP_REWRITE_TAC[ lemma_VH] THEN REWRITE_TAC [CFUN_ARITH 
`!f1:A^N->complex a1 a2. ( ((a1 % f1) x) * (a2 % f2) y) * f3 z  = 
    (a1*a2) * (f1 x * f2 y) * f3 z `] THEN        
REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2.  
((a1 % f1) y) * (a2 % f2) (lambda i. y$(i+k)) = 
(a1*a2) * f1 y * f2 (lambda i. y$(i+k)) `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`] 
THEN ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN
ASM_SIMP_TAC[ARITH_RULE ` ((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA] THEN
SIMP_TAC[ARITH_RULE ` (i - 3 = 1  <=> i = 4) /\ (i - 3 = 2  <=> i = 5) /\ 
(i - 6 = 1  <=> i = 7) /\ (i - 3 = 3 <=> i = 6)`] THEN
ASM_SIMP_TAC [ARITH_RULE ` i <= 3 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==> ( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`] 
`(if (i <= 8 /\ 1 <= i) then if i <= 6 then if i <= 3 then if i = 2 then x1 else x2
else if i = 5 then x3 else x2  else if i = 7 then x4 else x5 else x6) =
(if (i <= 8 /\ 1 <= i) then if i = 2 then x1 else if i = 5 then x3 
else if i = 7 then x4 else if i = 8 then x5 else x2 else x6) /\
(if (i <= 8 /\ 1 <= i) then if i <= 3 then if i = 2 then x1 else x2 else if i = 5
then x3 else if i = 7 then x4 else if i = 8 then x5 else x2 else x6) =
(if (i <= 8 /\ 1 <= i) then if i = 2 then x1 else if i = 5 then x3 else 
if i = 7 then x4 else if i = 8 then x5 else x2 else x6)`] THEN 
SIMP_TAC[GSYM CX_MUL;REAL_FIELD ` &1 / &2 * &1 / &2 = &1 / &4 `;ETA_AX]);;


let CZ_GATE_0vac =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LH (cz1) else vac (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 LH (cz3) else  vac (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
THEN IMP_REWRITE_TAC[CZ_INPUTS;CZ_0vac;CZ_OUTPUTS]);;

(****************************************************************************)
(* The projection of CZ outputs for one quantum state where there is no     *)
(*             photon and in the other input is vacuum state                *)
(****************************************************************************)

let CZ_vac0 =  prove( 
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
  8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
  is_CZ_model (a, b, c, j,ten) 
  ==>  (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
    (if i = 5 then fock (c$5) 1 else (if i = 7 then vac (a$2) else 
    (if i = 8 then fock (a$3) 1 else vac (c$3))))):bqs^N)))
    (tensor 8 ((lambda i.  if i = 2 then fock (b$2) 1 else (if i = 5 then 
    fock (b$5) 1 else (if i = 7 then vac (a$2) else (if i = 8 then fock (a$3) 1 
    else vac (b$3))))):bqs^N)) = (Cx (&1 / &4)) % tensor 8 (lambda i. if i = 2 then 
    fock (c$2) 1 else if i = 5 then fock (c$5) 1 else (if i = 7 then vac (a$2) else 
    (if i = 8 then fock (a$3) 1 else vac (c$3))))`, 
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
is_CZ_model] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\ 1 <= 2`;proj_tensor_m_n;ARITH_RULE 
`(8 <= dimindex (:N) ==>  2 <= dimindex (:N)) `] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] 
THEN ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE `i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`]
THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN ASM_SIMP_TAC [ARITH_RULE 
`6 = 3 + 3 /\  1 <= 3  `;proj_tensor_m_n;ARITH_RULE 
`(6 <= dimindex (:N) ==>  3 <= dimindex (:N)) `] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3+3 <= dimindex (:N) 
<=> (6 <= dimindex (:N) /\  3 <= dimindex (:N))) `] THEN    
SIMP_TAC [MESON[ARITH] `(if i = 2 then x
    else if i = 5 then y else z) = (if(i<=3) then (if i = 2
    then x else z) else (if i = 5 then y else z))`] THEN    
ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (if i = 2 then x else z)
    else (if i = 5 then y else z)) = 
    (if i <= 3 then (\j. if j = 2 then x else z) i
    else (\j. if j = 5 then y else z) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 3) /\ 
((6 <= dimindex (:N)) ==>(i <= 3 ==> i + 3 <= dimindex (:N)) )`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE `(( i + 3 <= 3)  <=> 
   (i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 5) <=> (i=2))`]
    `(if i + 3 <= 3 then if i + 3 = 2 then x else z
    else if i + 3 = 5 then y else z) = if i = 2 then y else z`] THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN IMP_REWRITE_TAC[NS_0_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[] `vac (d$3) = vac (b$3) /\ 
q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
    m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 
    else vac (c$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then 
    fock (d$2) 1 else vac (b$3)):bqs^N)) =  
    m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 else 
    vac (q$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 
    else vac (d$3)):bqs^N))`)] THEN CONV_TAC NUM_REDUCE_CONV THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(3 <= dimindex (:N) 
<=> (3 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 6) /\ ( 1 <= i + 2) /\ 
( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 6 <= dimindex (:N))))`] 
THEN REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  
i = k - j else F)) /\ (((i:num) + j <= k) <=> (if (j <= k) then  
i <= k - j else F)) ` ] THEN CONV_TAC NUM_REDUCE_CONV THEN
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN IMP_REWRITE_TAC[ lemma_HV] THEN
REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2. 
( ((a1 % f1) x) * (a2 % f2) y) * f3 z = (a1*a2) * (f1 x * f2 y) * f3 z`] THEN         
REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2.  
((a1 % f1) y) * (a2 % f2) (lambda i. y$(i+k)) = 
 (a1*a2) * f1 y * f2 (lambda i. y$(i+k)) `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`]
THEN ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN
ASM_SIMP_TAC[ARITH_RULE ` ((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA] THEN
SIMP_TAC[ARITH_RULE ` (i - 3 = 1  <=> i = 4) /\  (i - 3 = 2  <=> i = 5) /\ 
(i - 6 = 1  <=> i = 7) /\ (i - 3 = 3 <=> i = 6)`] THEN
ASM_SIMP_TAC [ARITH_RULE `i <= 3 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN
SIMP_TAC[MESON[ARITH;ARITH_RULE ` i <= 8 ==> ( ~(i <= 6) ==> (~ (i = 7)  <=> (i = 8)))`] 
`(if (i <= 8 /\ 1 <= i) then if i <= 6 then if i <= 3 then if i = 2 then x1 else x2
else if i = 5 then x3 else x2  else if i = 7 then x4 else x5 else x6) =
(if (i <= 8 /\ 1 <= i) then if i = 2 then x1 else if i = 5 then x3 
else if i = 7 then x4 else if i = 8 then x5 else x2 else x6) /\
(if (i <= 8 /\ 1 <= i) then if i <= 3 then if i = 2 then x1 else x2 else if i = 5
then x3 else if i = 7 then x4 else if i = 8 then x5 else x2 else x6) =
(if (i <= 8 /\ 1 <= i) then if i = 2 then x1 else if i = 5 then x3 else 
if i = 7 then x4 else if i = 8 then x5 else x2 else x6)`] THEN 
SIMP_TAC[GSYM CX_MUL;REAL_FIELD ` &1 / &2 * &1 / &2 = &1 / &4 `;ETA_AX]);;


 let CZ_GATE_vac0 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then vac (cz1) else LH (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 vac (cz3) else  LH (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
THEN IMP_REWRITE_TAC[CZ_INPUTS;CZ_vac0;CZ_OUTPUTS]);;
(****************************************************************************)
(* The projection of CZ outputs for one quantum state where there is no     *)
(*         photon and in the other input is one photon fock state           *)
(****************************************************************************)


let CZ_vac1 = prove(
`!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
 8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) ==>  
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  if i = 1 then fock (c$1) 1 else  if i = 7 then vac (a$2) else if i = 8 then 
vac (a$3) else if i = 5 then fock (c$5) 1 else vac (c$3)):bqs^N))) +
 (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
if i = 4 then fock (c$4) 1 else if i = 7 then vac (a$2) else if i = 8 then  
vac (a$3) else if i = 5 then fock (c$5) 1 else vac (c$3)):bqs^N))))
(tensor 8 ((lambda i.  if i = 4 then fock (a$4) 1 else if i = 2 then 
fock (b$2) 1 else  if i = 7 then vac (a$2) else if i = 8 then vac (a$3) 
else if i = 5 then fock (b$5) 1 else vac (b$3)):bqs^N)) =
Cx (&1 / &4) % tensor 8 ((lambda i. if i = 4 then fock (j$4) 1 else if i = 2
then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else if i = 7 then 
vac (a$2) else if i = 8 then vac (a$3) else vac (c$3)):bqs^N)`,
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
is_CZ_model] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
SIMP_TAC[is_beam_splitter;LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN SIMP_TAC[GSYM is_beam_splitter] THEN SIMP_TAC[cop_pow;COP_MUL_RID;
ONE;FACT;TWO] THEN SIMP_TAC[GSYM ONE; GSYM TWO] THEN SIMP_TAC[MULT_CLAUSES;
SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN ONCE_REWRITE_TAC[MESON[I_THM] 
`(if p then (x:bqs) else y) = (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN 
ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] 
`((x = 4) ==> f x = q) ==> (if (x = 4) then q else f x) = f x `;ARITH;COND_ID] 
THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN SIMP_TAC[is_beam_splitter;pos] 
THEN SIMP_TAC[GSYM is_beam_splitter;GSYM pos] THEN 
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;COP_ADD_THM;CNJ_CX;
COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN ASM_SIMP_TAC[PRO_TENSOR_LINEAR;
LINCOP_SMUL;LINCOP_ADD] THEN ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\ 1 <= 2`;
proj_tensor_m_n;ARITH_RULE `(8 <= dimindex (:N) ==> 2 <= dimindex (:N))`] 
THEN CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN   
ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN ASM_SIMP_TAC [ARITH_RULE 
`i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN 
ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN CONV_TAC (RAND_CONV(RAND_CONV
(ONCE_REWRITE_CONV [(SPEC_V ("j","j")) (MESON[COP_SMUL_LID] 
`cr (j$4) = (Cx(&1) % cr (j$4))`)]))) THEN IMP_REWRITE_TAC[MESON[is_beam_splitter;
lemma1] `is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),
--Cx(sqrt(&1/ &2)),ten,c$1,1,c$4,4,j$1,1,j$4,4) /\ is_beam_splitter (Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),ten,a$1,1,a$4,4,b$1,1,b$4,4) /\ 
vac (a$1) = vac (b$3) /\  b$4 = d$1/\ vac (j$4) = vac (c$3) ==> 
(cr (c$1) (vac (c$3)) =  fock (c$1) 1 /\ cr (c$4) (vac (c$3)) =  fock (c$4) 1
/\ cr (b$1) (vac (b$3)) = fock (b$1) 1  /\ cr (d$1) (vac (b$3)) =  fock (d$1) 1)`]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN    
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE ` ( 1 <= i + 6) /\ ( 1 <= i + 2) /\ 
( 1 <= i + 1) /\ ((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 6 <= dimindex (:N))))`]
THEN REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  
i = k - j else F)) /\ (((i:num) + j <= k) <=> (if (j <= k) then i <= k - j else F))`] 
THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN 
ASM_SIMP_TAC[PRO_TENSOR_LINEAR;LINCOP_SMUL;LINCOP_ADD] THEN 
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  
3 <= dimindex (:N))) `] THEN ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\  
1 <= 3  `;proj_tensor_m_n] THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x 
else (if i = 2 then y else if i = 5 then z1 else z2)) =  (if(i<=3) then 
(if i = 1 then x else (if i = 2 then y else z2)) else (if i = 5 then 
z1 else z2))) /\ ((if i = 2 then x else (if i = 1 then y else if i = 5 then 
z1 else z2)) = (if(i<=3) then (if i = 1 then y else (if i = 2 then x else z2)) 
else (if i = 5 then z1 else z2))) /\ ((if i = 4 then x1 else (if i = 2 then x2
else if i = 5 then x3 else x4)) = (if(i<=3) then (if i = 2 then x2 else x4)
else (if i = 4 then x1 else (if i = 5 then x3 else x4)))) /\ ((if i = 2 then x 
else if i = 5 then z1 else (if i = 4 then y else z2)) = (if(i<=3) then 
(if i = 2 then x else z2) else (if i = 5 then z1 else (if i = 4 then y else z2)))) 
/\ ((if i = 2 then x else if i = 4 then z1 else (if i = 5 then y else z2)) = 
(if(i<=3) then (if i = 2 then x else z2) else (if i = 4 then z1 else (if i = 5
then y else z2))))`] THEN ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (q i)
else (p i)) = (if i <= 3 then (\j. q j) i else (\j. p j) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE ` 3 + 3 = 6`] THEN ASM_SIMP_TAC [LAMBDA_BETA;
ARITH_RULE ` ( 1 <= i + 3) /\ ((6 <= dimindex (:N)) ==>(i <= 3 ==> 
i + 3 <= dimindex (:N)) )`] THEN SIMP_TAC[ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 1) <=> F) 
/\ ((i + 3 = 5) <=> (i=2)) /\ ((i + 3 = 4) <=> (i=1))`] THEN
ONCE_SIMP_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN
IMP_REWRITE_TAC[CONV_RULE(SIMP_CONV[GSYM lemma1]) lemma_HH; ARITH_RULE 
`8 <= dimindex (:N) ==>   2 <= dimindex (:N)`] THEN SIMP_TAC[MESON[ARITH]`
(if i = 0 then x  else if i = 2 then y else x) = (if i = 2 then y else x) /\
(if i = 0 then x else if i = 1 then y else if i = 2 then z else x) =
(if i = 2 then z else if i = 1 then y else x) /\
(if i = 0 then x else if i = 2 then y else if i = 1 then z else x) =
(if i = 2 then y else if i = 1 then z else x) /\
(if i = 1 then y else if i = 2 then z else x) = 
(if i = 2 then z else if i = 1 then y else x)`] THEN
IMP_REWRITE_TAC[NS_0_PROJ_0;NS_0_PROJ_1;NS_1_PROJ_1;NS_1_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[] `q$1 = c$4 /\ vac (d$3) = vac (b$3) /\ 
q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
(m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 else vac (c$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else vac (b$3)):bqs^N)) = 
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 else vac (q$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else vac (d$3)):bqs^N)) /\
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 else if i = 1 then 
fock (c$4) 1 else vac (c$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then 
fock (d$2) 1 else if i = 1 then fock (d$1) 1 else vac (b$3)):bqs^N)) =
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 else if i = 1 then 
fock (q$1) 1 else vac (q$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)))`)]THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;CFUN_SMUL_RZERO;
CFUN_ADD_RID;CFUN_ADD_LID] THEN REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2.  
((a1 % f1) y * (a2 % f2) x) * f3 z = (a1*a2) * ((f1 y * f2 x) * f3 z)`] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\ 
6 <= dimindex (:N)))`] THEN ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] 
THEN IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN
CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d]         
THEN ASM_SIMP_TAC[ARITH_RULE `((i <= 8 /\ 8 <= dimindex (:N)) ==>  
(i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\ i - 6 <= dimindex(:N))) /\ 
(~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;LAMBDA_BETA]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN SIMP_TAC[ARITH_RULE 
` (i - 3 = 1  <=> i = 4) /\  (i - 6 = 1  <=> i = 7) /\
(i - 3 = 2  <=> i = 5) /\ (i - 3 = 3 <=> i = 6)`] THEN
IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ (3 < p2)) ==> 
(((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ (i = p2)) = F) 
/\ (((i = p2) /\ (i = p1)) = F)) ` ] `((p1 <= 3) /\ (3 < p3) /\ (3 < p2)) ==> 
(if (i <= 3) then if (i = p1) then q1 else q2  else if (i = p2) then q3  else 
(if i = p3 then q4 else q2)) = (if (i = p1) then q1 else (if (i = p2) then q3 
else if (i = p3) then q4 else q2))`;ARITH] THEN IMP_REWRITE_TAC[MESON[ARITH_RULE 
`((p1 <= 3) /\ (3 < p2)) ==> (((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ 
(i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F))`] `((p1 <= 3) /\ (p3 <= 3) /\ 
(3 < p2)) ==> (if (i <= 3) then if (i = p1) then q1 else (if i = p3 then q4 else q2)  
else if (i = p2) then q3 else q2) = (if (i = p1) then q1 else if (i = p3) then 
q4 else (if (i = p2) then q3 else q2)) `;ARITH] THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d]
THEN SIMP_TAC[MESON[ARITH;ARITH_RULE `i <= 8 ==> ( ~(i <= 6) ==> (~(i = 7) <=> (i = 8)))`]
`(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 1 then x1 else if i = 2  then x2
 else if i = 5  then x3 else x4 else if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 1 then x1 else if i = 2   then x2
 else if i = 5  then x3  else if i = 7 then x5 else if i = 8 then x6 else x4
 else x7) /\ (if i <= 8 /\ 1 <= i then if i <= 6 then if i = 2  then x2
 else if i = 4 then x1 else if i = 5  then x3 else x4 else if i = 7 then x5 
 else x6 else x7) = (if i <= 8 /\ 1 <= i then if i = 4 then x1 else if i = 2 then x2
 else if i = 5  then x3  else if i = 7 then x5 else if i = 8 then x6 else x4 else x7)`]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;
CFUN_SMUL_ASSOC;GSYM CX_MUL; CFUN_ADD_LID;GSYM CX_NEG;CNJ_CX;GSYM CX_ADD] THEN
SIMP_TAC [GSYM lemma1;is_beam_splitter] THEN SIMP_TAC [GSYM is_beam_splitter;
COP_MUL_THM;COP_SMUL_THM;ETA_AX] THEN ONCE_REWRITE_TAC[MESON[I_THM] 
`(if p then (x:bqs) else y) = (if p then x else I y)`] THEN ONCE_REWRITE_TAC[MESON[]
`(if p then f1 x else f2 y) = (if p then f1  else f2 ) (if p then  x else  y)`]
THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] `((x = 4) ==> f x = q) ==> 
(if (x = 4) then q else f x) = f x`;ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] 
THEN SIMP_TAC[is_beam_splitter;pos] THEN SIMP_TAC[GSYM is_beam_splitter] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH; COP_ADD_THM;CNJ_CX;
COP_SMUL_THM;COP_TENSOR_CFUN] THEN SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_MUL;
GSYM CX_NEG;CNJ_CX] THEN SIMP_TAC [MESON[ARITH] `((if i = 4 then x1 else if i = 1 then x2 
else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then x7 else if i = 8 then x8 else x2) = 
(if i = 4 then x1 else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then x7 else 
if i = 8 then x8 else x2))`] THEN SIMP_TAC [MESON[ARITH] `((if i = 2 then x2 else if i = 4 then 
x1 else (if i = 5 then x5 else x6)) = ( if i = 4 then x1 else if i = 2 then x2 else 
(if i = 5 then x5 else x6)))`] THEN SIMP_TAC [CFUN_ADD_SYM;CFUN_ADD_ASSOC;GSYM CFUN_ADD_RDISTRIB;
REAL_NEG_NEG;CFUN_SMUL_LID; CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun). 
b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a /\ 
f + b%a + c%a +d = f + (b+c) % a +d`;GSYM CX_ADD;CFUN_ADD_AC]  THEN
SIMP_TAC[SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_FIELD ` &1 / &8 - -- (&1 / &8) = &1 / &4 /\ &1 / &2 * &1 / &2 pow 2 = &1 / &8 `;
CFUN_ADD_LID;REAL_SUB_REFL;CFUN_ADD_RID]);;


 let CZ_GATE_vac1 =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then vac (cz1) else LV (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
 vac (cz3) else  LV (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[CZ_INPUTS;CZ_vac1;CZ_OUTPUTS]);;

(****************************************************************************)
(* The projection of CZ outputs for one input is one photon fock state and   *)
(* in the other input there is no photon in both the polarization modes      *)
(****************************************************************************)

let CZ_1vac = prove( `!(a:sm^N) (b:sm^N) c (j:sm^N) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
is_CZ_model (a, b, c, j,ten) ==>  
((m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
  if i = 1 then fock (c$1) 1 else if i = 7 then vac (a$2) else if i = 8 then 
  vac (a$3)  else if i = 5 then fock (c$5) 1 else vac (c$3)):bqs^N))) +
   (m_modes_pro (tensor 8 ((lambda i. if i = 2 then fock (c$2) 1 else 
   if i = 4 then fock (c$4) 1 else if i = 7 then vac (a$2) else if i = 8 then 
   vac (a$3)  else if i = 5 then fock (c$5) 1 else vac (c$3)):bqs^N))))
 (tensor 8 ((lambda i.  if i = 1 then fock (a$1) 1 else if i = 2 then fock (b$2) 1 
 else if i = 7 then vac (a$2) else if i = 8 then vac (a$3)  else if i = 5 then 
 fock (b$5) 1 else vac (b$3)):bqs^N)) = Cx (&1 / &4) % tensor 8 ((lambda i. if i = 1 
 then fock (j$1) 1 else if i = 2 then fock (c$2) 1 else if i = 5 then fock (c$5) 1 else 
 if i = 7 then vac (a$2) else if i = 8 then vac (a$3)  else vac (c$3)):bqs^N)`,
REWRITE_TAC[LEFT_IMP_FORALL_THM;LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;
is_CZ_model] THEN REPEAT GEN_TAC THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
SIMP_TAC[is_beam_splitter;LET_RULE_L[GSYM COP_SMUL_THM] FOCK_HERM_VAC]
THEN SIMP_TAC[GSYM is_beam_splitter] THEN SIMP_TAC[cop_pow;COP_MUL_RID;
ONE;FACT;TWO] THEN SIMP_TAC[GSYM ONE;GSYM TWO] THEN SIMP_TAC[MULT_CLAUSES;
SQRT_1;COMPLEX_INV_1;COP_SMUL_LID] THEN ONCE_REWRITE_TAC[MESON[I_THM] 
`(if p then (x:bqs) else y) = (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = 
(if p then f1  else f2 ) (if p then  x else  y)`] THEN 
ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN SIMP_TAC[MESON[keylem] 
`((x = 1) ==> f x = q) ==> (if (x = 1) then q else f x) = f x`;
ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN SIMP_TAC[GSYM is_beam_splitter;GSYM pos] 
THEN SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH;COP_ADD_THM;CNJ_CX;
COP_SMUL_THM;pos;COP_TENSOR_CFUN] THEN ASM_SIMP_TAC[PRO_TENSOR_LINEAR;
LINCOP_SMUL;LINCOP_ADD] THEN ASM_SIMP_TAC [ARITH_RULE `8 = 6 + 2 /\ 1 <= 2`;
proj_tensor_m_n;ARITH_RULE `(8 <= dimindex (:N) ==>  2 <= dimindex (:N))`] 
THEN CONV_TAC NUM_REDUCE_CONV THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\ 6 <= dimindex (:N)))`] THEN 
ONCE_SIMP_TAC[(ISPECL [`6`] tensor_mlem1d)] THEN ASM_SIMP_TAC [ARITH_RULE `  
i <= 6 ==>( ((i = 7) = F) /\ ((i = 8) = F))`] THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] 
THEN CONV_TAC (RAND_CONV(RAND_CONV(ONCE_REWRITE_CONV [(SPEC_V ("j","j")) 
(MESON[COP_SMUL_LID] `cr (j$1) = (Cx(&1) % cr (j$1))`)]))) THEN 
IMP_REWRITE_TAC[MESON[is_beam_splitter;lemma1] `is_beam_splitter (Cx(sqrt(&1/ &2)),
Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2)),ten,c$1,1,c$4,4,j$1,1,j$4,4) /\ 
is_beam_splitter (Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),Cx(sqrt(&1/ &2)),--Cx(sqrt(&1/ &2))
,ten,a$1,1,a$4,4,b$1,1,b$4,4) /\ vac (a$1) = vac (b$3) /\  b$4 = d$1 /\ 
vac (j$4) = vac (c$3) ==> (cr (c$1) (vac (c$3)) =  fock (c$1) 1 /\ 
cr (c$4) (vac (c$3)) =  fock (c$4) 1 /\ cr (b$1) (vac (b$3)) = fock (b$1) 1 /\ 
cr (d$1) (vac (b$3)) =  fock (d$1) 1)`]THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE 
`(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\  2 <= dimindex (:N))) `] THEN   
ONCE_SIMP_TAC[(ISPECL [`2`] tensor_mlem1d)] THEN ASM_SIMP_TAC [LAMBDA_BETA;
ARITH_RULE ` ( 1 <= i + 6) /\ ( 1 <= i + 2) /\ ( 1 <= i + 1) /\ 
((8 <= dimindex (:N)) ==>(i <= 2 ==> (i + 6 <= dimindex (:N))))`] THEN
REWRITE_TAC[ ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then  i = k - j else F)) 
/\ (((i:num) + j <= k) <=> (if (j <= k) then  i <= k - j else F))`] THEN
CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[GSYM tensor_mlem1d] THEN 
ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) <=> (8 <= dimindex (:N) /\ 
3 <= dimindex (:N))) `] THEN ASM_SIMP_TAC [ARITH_RULE `6 = 3 + 3 /\ 1 <= 3`;
proj_tensor_m_n] THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x 
else (if i = 2 then y else if i = 5 then z1 else z2)) = (if(i<=3) then 
(if i = 1 then x else (if i = 2 then y else z2)) else (if i = 5 then z1 else z2)))
/\ ((if i = 2 then x else (if i = 1 then y else if i = 5 then z1 else z2)) = 
(if(i<=3) then (if i = 1 then y else (if i = 2 then x else z2)) else 
(if i = 5 then z1 else z2))) /\ ((if i = 4 then x1 else (if i = 2 then x2
else if i = 5 then x3 else x4)) = (if(i<=3) then (if i = 2 then x2 else x4)
else (if i = 4 then x1 else (if i = 5 then x3 else x4)))) /\ ((if i = 2 then x 
else if i = 5 then z1 else (if i = 4 then y else z2)) = (if(i<=3) then 
(if i = 2 then x else z2) else (if i = 5 then z1 else (if i = 4 then y else z2)))) 
/\ ((if i = 2 then x else if i = 4 then z1 else (if i = 5 then y else z2)) = 
(if(i<=3) then (if i = 2 then x else z2) else (if i = 4 then z1 else (if i = 5
then y else z2))))`] THEN ONCE_REWRITE_TAC[MESON[] `(if i <= 3 then (q i)
else (p i)) = (if i <= 3 then (\j. q j) i else (\j. p j) i)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] THEN 
ONCE_SIMP_TAC[(ISPECL [`3`] tensor_mlem1d)] THEN
ASM_SIMP_TAC [ARITH_RULE ` 3 + 3 = 6`] THEN ASM_SIMP_TAC [LAMBDA_BETA;
ARITH_RULE ` ( 1 <= i + 3) /\ ((6 <= dimindex (:N)) ==>(i <= 3 ==> 
i + 3 <= dimindex (:N)) )`] THEN SIMP_TAC[ARITH_RULE `(( i + 3 <= 3)  <=> 
(i = 0)) /\ ((i + 3 = 2) <=> F) /\ ((i + 3 = 1) <=> F) /\ ((i + 3 = 5) <=> 
(i=2)) /\ ((i + 3 = 4) <=> (i=1))`] THEN ONCE_SIMP_TAC[GSYM (ISPECL [`3`] tensor_mlem1d)] 
THEN IMP_REWRITE_TAC[CONV_RULE(SIMP_CONV[GSYM lemma1]) lemma_HH; 
ARITH_RULE `8 <= dimindex (:N) ==> 2 <= dimindex (:N)`] THEN SIMP_TAC[MESON[ARITH]`
(if i = 0 then x  else if i = 2 then y else x) = (if i = 2 then y else x) /\
(if i = 0 then x else if i = 1 then y else if i = 2 then z else x) =
(if i = 2 then z else if i = 1 then y else x) /\
(if i = 0 then x else if i = 2 then y else if i = 1 then z else x) =
(if i = 2 then y else if i = 1 then z else x) /\
(if i = 1 then y else if i = 2 then z else x) = 
(if i = 2 then z else if i = 1 then y else x)`] THEN
IMP_REWRITE_TAC[NS_0_PROJ_0;NS_0_PROJ_1;NS_1_PROJ_1;NS_1_PROJ_0;
REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[]`q$1 = c$4 /\ vac (d$3) = vac (b$3) /\ 
q$3 = c$6 /\ vac (c$6) = vac (c$3) /\  q$2 = c$5 ==>
(m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 else vac (c$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else vac (b$3)):bqs^N)) =  
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 else vac (q$3)):bqs^N))
(tensor 3 ((lambda i. if i = 2 then fock (d$2) 1 else vac (d$3)):bqs^N)) /\
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (c$5) 1 else if i = 1 then 
fock (c$4) 1 else vac (c$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (b$3)):bqs^N)) =
m_modes_pro (tensor 3 ((lambda i. if i = 2 then fock (q$2) 1 else if i = 1 then 
fock (q$1) 1 else vac (q$3)):bqs^N)) (tensor 3 ((lambda i. if i = 2 then fock (d$2) 1
else if i = 1 then fock (d$1) 1 else vac (d$3)):bqs^N)))`)] THEN
SIMP_TAC [K_THM;COMPLEX_MUL_LZERO;GSYM cfun_zero;GSYM K_DEF;CFUN_SMUL_RZERO;
CFUN_ADD_RID;CFUN_ADD_LID] THEN REWRITE_TAC [CFUN_ARITH `!f1:A^N->complex a1 a2.  
((a1 % f1) y * (a2 % f2) x) * f3 z = (a1*a2) * ((f1 y * f2 x) * f3 z) `] THEN
SIMP_TAC [CFUN_ARITH `!f1:A^N->complex. (\y. a * f1 y) = a % (\y. f1 y)`]
THEN ONCE_ASM_REWRITE_TAC[ARITH_RULE `(8 <= dimindex (:N) 
<=> (8 <= dimindex (:N) /\  6 <= dimindex (:N))) `] THEN
ASM_SIMP_TAC [ARITH_RULE ` 6 = 3 + 3 /\ 8 = 6 + 2`] THEN 
IMP_REWRITE_TAC [REWRITE_RULE[FUN_EQ_THM] tensor_mnlem] THEN CONV_TAC NUM_REDUCE_CONV
THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d] THEN ASM_SIMP_TAC[ARITH_RULE 
`((i <= 8 /\ 8 <= dimindex (:N)) ==>  (i <= dimindex (:N) /\ i - 3 <= dimindex(:N) /\
i - 6 <= dimindex(:N))) /\ (~(i <= 3) ==> (1 <= i - 3)) /\ (~(i <= 6) ==> (1 <= i - 6))`;
LAMBDA_BETA] THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN SIMP_TAC[ARITH_RULE 
`(i - 3 = 1  <=> i = 4) /\  (i - 6 = 1  <=> i = 7) /\ (i - 3 = 2  <=> i = 5) /\ 
(i - 3 = 3 <=> i = 6)`] THEN IMP_REWRITE_TAC[MESON[ARITH_RULE `((p1 <= 3) /\ 
(3 < p2)) ==> (((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ (i = p2)) = F) 
/\ (((i = p2) /\ (i = p1)) = F))`] `((p1 <= 3) /\ (3 < p3) /\ (3 < p2)) ==> 
(if (i <= 3) then if (i = p1) then q1 else q2  else if (i = p2) then q3 else 
(if i = p3 then q4 else q2)) = (if (i = p1) then q1 else (if (i = p2) then q3 
else if (i = p3) then q4 else q2))`;ARITH] THEN IMP_REWRITE_TAC[MESON[ARITH_RULE 
`((p1 <= 3) /\ (3 < p2)) ==> (((~(i <= 3) /\ (i = p1)) = F ) /\ (((i <= 3) /\ 
(i = p2)) = F) /\ (((i = p2) /\ (i = p1)) = F))`] `((p1 <= 3) /\ (p3 <= 3) /\ 
(3 < p2)) ==> (if (i <= 3) then if (i = p1) then q1 else (if i = p3 then q4 else q2)  
else if (i = p2) then q3 else q2) = (if (i = p1) then q1 else if (i = p3) then q4 
else (if (i = p2) then q3 else q2))`;ARITH] THEN ONCE_ASM_SIMP_TAC[tensor_1mlem1d]  
THEN SIMP_TAC[MESON[ARITH;ARITH_RULE `i <= 8 ==> (~(i <= 6) ==> (~(i = 7) <=> (i = 8)))`]
`(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 1 then x1 else if i = 2  then x2
 else if i = 5  then x3 else x4 else if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 1 then x1 else if i = 2   then x2
 else if i = 5  then x3  else if i = 7 then x5 else if i = 8 then x6 else x4 else x7) /\
(if i <= 8 /\ 1 <= i then if i <= 6 then if i = 2  then x2
 else if i = 4 then x1 else if i = 5  then x3 else x4 else if i = 7 then x5 else x6 else x7)
= (if i <= 8 /\ 1 <= i then if i = 4 then x1 else if i = 2   then x2
 else if i = 5  then x3  else if i = 7 then x5 else if i = 8 then x6 else x4 else x7)`]
THEN ASM_SIMP_TAC[GSYM tensor_1mlem1d] THEN SIMP_TAC[GSYM CFUN_ADD_RDISTRIB;
CFUN_SMUL_ASSOC;GSYM CX_MUL; CFUN_ADD_LID;GSYM CX_NEG;CNJ_CX;GSYM CX_ADD] THEN
SIMP_TAC [GSYM lemma1;is_beam_splitter] THEN SIMP_TAC [GSYM is_beam_splitter;
COP_MUL_THM;COP_SMUL_THM;ETA_AX] THEN ONCE_REWRITE_TAC[MESON[I_THM] 
`(if p then (x:bqs) else y) = (if p then x else I y)`] THEN 
ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) =
(if p then f1  else f2 ) (if p then  x else  y)`] THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] 
THEN SIMP_TAC[MESON[keylem] `((x = 1) ==> f x = q) ==> (if (x = 1) then q else f x) = f x`;
ARITH;COND_ID] THEN IMP_REWRITE_TAC[GSYM COP_TENSOR_CFUN] THEN
SIMP_TAC[is_beam_splitter;pos] THEN SIMP_TAC[GSYM is_beam_splitter] THEN
SIMP_TAC[GSYM CFUN_LAMBDA_APP;COND_RATOR;I_THM;ARITH; COP_ADD_THM;CNJ_CX;COP_SMUL_THM;
COP_TENSOR_CFUN] THEN SIMP_TAC[CFUN_ADD_LDISTRIB;CFUN_SMUL_DISTRIB;GSYM CX_MUL;
GSYM CX_NEG;CNJ_CX] THEN SIMP_TAC [MESON[ARITH] `((if i = 1 then x1 else if i = 4 then x2 
else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then x7 else if i = 8 then x8 
else x2) = (if i = 1 then x1 else if i = 2 then x3 else if i = 5 then x4 else if i = 7 then 
x7 else if i = 8 then x8 else x2))`] THEN SIMP_TAC [MESON[ARITH] `((if i = 2 then x2 else 
if i = 1 then x1 else (if i = 5 then x5 else x6)) = ( if i = 1 then x1 else if i = 2 then x2 
else (if i = 5 then x5 else x6)))`] THEN SIMP_TAC [CFUN_ADD_SYM;CFUN_ADD_ASSOC;
GSYM CFUN_ADD_RDISTRIB; CFUN_ARITH`!(a:cfun) (b:complex) (c:complex) (d:cfun) (f:cfun). 
b%a + c%a +d = (b+c) % a +d  /\ f + b%a + c%a = f + (b+c) % a /\ 
f + b%a + c%a +d = f + (b+c) % a +d`;GSYM CX_ADD;CFUN_ADD_AC]  THEN
SIMP_TAC[SQRT_DIV;SQRT_1;GSYM REAL_POW_2;REAL_POS;SQRT_POW_2;REAL_MUL_SYM;GSYM real_sub;
GSYM REAL_MUL_ASSOC;REAL_MUL_AC;REAL_POW_DIV;REAL_POW_ONE;REAL_MUL_RNEG;CFUN_SMUL_LZERO;
REAL_FIELD ` &1 / &8 + &1 / &8 = &1 / &4 /\ &1 / &2 * &1 / &2 pow 2 = &1 / &8 `;
CFUN_ADD_LID;REAL_SUB_REFL;CFUN_SMUL_LID] );;


 let CZ_GATE_1vac =prove(
`!(cz1:sm) (cz2:sm) cz3 (cz4:sm) (ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)). 
8 <= dimindex (:N) /\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
CZ_GATE (cz1, cz2, cz3, cz4,ten,LH,LV,m_modes_pro) 
==> (tensor 2 ((lambda i.  if i = 1 then LV (cz1) else vac (cz2)):bqs^N)) =
(Cx (&1 / &4)) % (tensor 2 ((lambda i.  if i = 1 then 
LV (cz3) else vac (cz4)):bqs^N))`,
REPEAT GEN_TAC THEN  REWRITE_TAC[CFUN_SMUL_LID;LEFT_IMP_FORALL_THM;
LEFT_AND_FORALL_THM;RIGHT_AND_FORALL_THM;CZ_GATE] THEN 
REWRITE_TAC[LEFT_AND_EXISTS_THM;RIGHT_AND_EXISTS_THM] THEN
REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN 
 IMP_REWRITE_TAC[CZ_INPUTS;CZ_1vac;CZ_OUTPUTS]);;


let cz_tac cz1 cz2 cz3 cz4 = 
 SUBGOAL_TAC "cz_1vac" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_1vac)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_1vac] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_0vac" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_0vac)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_0vac] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_vac1" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_vac1)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_vac1] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_vac0" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_vac0)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_vac0] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_00" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_00))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_00] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_10" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_10))))))) 
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_10] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_01" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_01)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_01] THEN CFUN_ARITH_TAC] THEN
 SUBGOAL_TAC "cz_11" (concl (UNDISCH_ALL (spec_thm_tac (SPEC_V ("cz1",cz1) 
 (SPEC_V("cz2",cz2) (SPEC_V ("cz3",cz3) (SPEC_V("cz4",cz4) CZ_GATE_11)))))))
[IMP_REWRITE_TAC [spec_thm_tac CZ_GATE_11] THEN CFUN_ARITH_TAC] THEN
ASM_SIMP_TAC [] THEN SIMP_TAC [CFUN_SMUL_LID] THEN 
REMOVE_THEN "cz_0vac" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_1vac" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_vac0" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_vac1" (fun thm-> ALL_TAC) THEN 
REMOVE_THEN "cz_00" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_01" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_10" (fun thm-> ALL_TAC)THEN
REMOVE_THEN "cz_11" (fun thm-> ALL_TAC);;