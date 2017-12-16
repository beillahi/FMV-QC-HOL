(* ========================================================================= *)
(*                                                                           *)
(*                        tensor_product.ml                                   *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: February 19, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "multi_mode.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)  
  
let tensor_kmlem = prove(  `!(m:num) k.  m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if i <= k then modes1$i else modes2$i):bqs^N)
 = tensor m ((lambda i. if i <= m then modes1$i else modes2$i):bqs^N)`,
INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 
let tensor_1kmlem = prove( `!(m:num) k. 
 m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if (i <= k /\ 1 <= i) 
 then modes1$i else modes2$i):bqs^N)
 = tensor m ((lambda i. if (i <= m /\ 1 <= i) 
 then modes1$i else modes2$i):bqs^N)`,
 INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 
 
let tensor_1mlem = prove(  `!(m:num).  m <= dimindex (:N)
 ==> tensor m modes1 =
tensor m ((lambda i. if (i <= m /\ 1 <= i) 
then modes1$i else modes2$i):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_1kmlem;tensor;
ARITH_RULE `SUC m <= dimindex (:N)  ==>  
m <= dimindex (:N) /\ m <= SUC m `] THEN 
SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;




let tensor_mlem = prove( `!(m:num).  m <= dimindex (:N)
 ==> tensor m modes1 =
     tensor m ((lambda i. if i <= m then modes1$i else modes2$i):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_kmlem;tensor;ARITH_RULE `SUC m <= dimindex (:N) 
 ==>  m <= dimindex (:N) /\ m <= SUC m `]
THEN SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;



let tensor_nmlem1 = prove(`!(n:num).  1 <= n /\ n <= dimindex (:N) ==>
 (tensor (m+n) (modes:bqs^N)) = (\y:real^N. ((tensor m modes) y) * 
 ((tensor n ((lambda i. (modes:bqs^N)$(i+m)):bqs^N)) ((lambda i. y$(i+m)):real^N)))`,
INDUCT_TAC THEN SIMP_TAC [ADD_CLAUSES;tensor;K_DEF;COMPLEX_MUL_RID;ETA_AX]
THEN ASM_SIMP_TAC [GSYM (REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[CART_EQ; LAMBDA_BETA;ARITH_RULE `(n+1)+m = n+m+1 
/\ (m+n)+1= n+m+1` ;ADD1]
 `!y n m.  1 <= SUC n /\ SUC n <= dimindex (:N) ==>  
   ((lambda i. (y:real^N)$(i+m)):real^N)$(n+1) = (y)$(SUC (m+n)) `))]
THEN ASM_CASES_TAC `1 <= n`
THEN POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC [ARITH_RULE `1 <= SUC n <=> 0 <= n `;
 MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`;
ARITH_RULE `1 <= n /\ 0 <= n /\ SUC n <= dimindex (:N) 
<=> 1 <= n /\ SUC n <= dimindex (:N) `;
  ARITH_RULE `SUC n <= dimindex (:N) ==>  n <= dimindex (:N)`]
THEN SIMP_TAC[ADD1;LAMBDA_BETA;ARITH_RULE `1 <= n+1`;ADD_CLAUSES] 
THEN SIMP_TAC [COMPLEX_FIELD `((a)*b)*c = a*(b*c)`;ADD_AC] THEN
SIMP_TAC [tensor;ADD1]  THEN 
ASM_SIMP_TAC [ARITH_RULE `1 <= n+1 <=> 0 <= n `;
 MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`;
ARITH_RULE `~(1 <= n) /\ 0 <= n  /\  n+1 <= dimindex (:N)
<=> n = 0 /\ 1 <= dimindex (:N)`] THEN
SIMP_TAC [tensor] THEN
 SIMP_TAC [K_DEF] THEN
ASM_SIMP_TAC [ADD_CLAUSES;ADD1;COMPLEX_MUL_LID;LAMBDA_BETA; 
ARITH_RULE ` (1 <= 1)`;ADD_AC]);;





let tensor_nmlem = prove( `!(n:num).  n <= dimindex (:N) ==>
 (tensor (m+n) (modes:bqs^N)) = (\y:real^N. ((tensor m modes) y) * 
 ((tensor n ((lambda i. (modes:bqs^N)$(i+m)):bqs^N)) ((lambda i. y$(i+m)):real^N)))`,
 GEN_TAC THEN ASM_CASES_TAC ` 1 <= n` THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC [tensor_nmlem1;MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
SIMP_TAC [tensor;K_DEF;ARITH_RULE ` ~(1 <= n)  <=> n = 0 `;
MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`]
THEN SIMP_TAC[ARITH_RULE `((m + 0) = m) `;ETA_AX;COMPLEX_MUL_RID]);;





let tensor_kmlem1 = prove(  `!(m:num) k l.  m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if i <= k then modes1$i else modes2$(i - l)):bqs^N)
 = tensor m ((lambda i. if i <= m then modes1$i else modes2$(i - l)):bqs^N)`,
INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 
 
let tensor_1kmlem1 = prove(  `!(m:num) k l.  
m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if (i <= k /\ 1 <= i) 
 then modes1$i else modes2$(i - l)):bqs^N)
 = tensor m ((lambda i. if (i <= m /\ 1 <= i) 
 then modes1$i else modes2$(i - l)):bqs^N)`,
INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 
 
 let tensor_1mlem1 = prove( `!(m:num) l.  m <= dimindex (:N)
 ==> tensor m modes1 =
tensor m ((lambda i. if (i <= m /\ 1 <= i) 
then modes1$i else modes2$(i-l)):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_1kmlem1;tensor;ARITH_RULE 
`SUC m <= dimindex (:N)  ==>  m <= dimindex (:N) /\ m <= SUC m `]
THEN SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;



let tensor_mlem1 = prove( `!(m:num) l.  m <= dimindex (:N)
 ==> tensor m modes1 =
tensor m ((lambda i. if i <= m then modes1$i else modes2$(i-l)):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_kmlem1;tensor;ARITH_RULE 
`SUC m <= dimindex (:N)  ==>  m <= dimindex (:N) /\ m <= SUC m `]
THEN SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;




let tensor_kmlemd1 = prove(  `!(m:num) k l. 
 m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if i <= k then (f i) else (g i)):bqs^N)
 = tensor m ((lambda i. if i <= m then (f i) else (g i)):bqs^N)`,
INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 

let tensor_1kmlemd1 = prove(  `!(m:num) k l.  
m <= dimindex (:N) /\ m <= k
 ==> tensor m ((lambda i. if (i <= k /\ 1 <= i) 
then (f i) else (g i)):bqs^N)
 = tensor m ((lambda i. if (i <= m /\ 1 <= i) 
then (f i) else (g i)):bqs^N)`,
INDUCT_TAC THEN
SIMP_TAC [tensor] THEN
SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC m <=  a  ==>  m <=  a `] THEN
ASM_SIMP_TAC [LAMBDA_BETA;ARITH_RULE `SUC m <=  dimindex (:N) 
 ==>  m <=  dimindex (:N)  /\ 1 <= SUC m /\ m <= SUC m`] THEN
 ARITH_TAC);;
 
 
 
 
 let tensor_1mlem1d = prove( `!(m:num).  m <= dimindex (:N)
 ==> tensor m (lambda i. (f i)) =
tensor m ((lambda i. if (i <= m /\ 1 <= i) then (f i) else (g i)):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_1kmlemd1;tensor;ARITH_RULE 
`SUC m <= dimindex (:N)  ==>  m <= dimindex (:N) /\ m <= SUC m `]
THEN SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;
 
 
 
 
let tensor_mlem1d = prove( `!(m:num).  m <= dimindex (:N)
 ==> tensor m (lambda i. (f i)) =
tensor m ((lambda i. if i <= m then (f i) else (g i)):bqs^N)`,
INDUCT_TAC THEN SIMP_TAC [tensor] THEN
ASM_SIMP_TAC [tensor_kmlemd1;tensor;ARITH_RULE 
`SUC m <= dimindex (:N)  ==>  m <= dimindex (:N) /\ m <= SUC m `]
THEN SIMP_TAC [LAMBDA_BETA; ARITH_RULE ` 1 <= SUC n `] 
THEN ARITH_TAC);;





let tensor_mnlem1 = prove(`!(n:num). 
1 <= n /\ n+m <= dimindex (:N) ==>
(\y:real^N. ((tensor m modes1) y) * 
((tensor n (modes2:bqs^N)) ((lambda i. y$(i+m)):real^N)))
= tensor (m+n) ((lambda i. if (i<=m) 
then modes1$i else modes2$(i-m)):bqs^N) `,
INDUCT_TAC THEN SIMP_TAC [tensor;K_DEF;ARITH] THEN
SIMP_TAC [tensor] THEN IMP_REWRITE_TAC [LAMBDA_BETA;
ARITH_RULE `SUC n + m <= dimindex (:N) ==> SUC n <= dimindex (:N)`] 
THEN ASM_CASES_TAC `1 <= n` THEN POP_ASSUM MP_TAC THEN
SIMP_TAC [ARITH_RULE `((1 <= n /\ 1 <= SUC n /\ 
SUC n + m <= dimindex (:N)) <=> (1 <= n /\ SUC n + m <= dimindex (:N)))`;
 MESON[] `(p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
SIMP_TAC [COMPLEX_FIELD ` a * b *c = (a*b)*c`] THEN
ONCE_SIMP_TAC [MESON[BETA_THM] `tensor m (modes1:bqs^N) y * 
tensor n (modes2:bqs^N) (lambda i. y$(i + m)) =
(\y:real^N. tensor m (modes1:bqs^N) y * 
tensor n (modes2:bqs^N) (lambda i. y$(i + m))) (y:real^N) `] THEN
ASM_SIMP_TAC [ARITH_RULE `SUC n + m <= dimindex (:N) ==> 
n + m <= dimindex (:N)`;MESON[] ` (\y. tensor m modes1 y * 
tensor n modes2 (lambda i. y$(i + m))) =
tensor (m + n) (lambda i. if i <= m then modes1$i else modes2$(i-m)) 
==> (\y. tensor m modes1 y * tensor n modes2 (lambda i. y$(i + m))) y =
tensor (m + n) (lambda i. if i <= m then modes1$i else modes2$(i-m)) y`] 
THEN SIMP_TAC [ARITH_RULE ` m + SUC n = SUC (n+m) /\  
SUC n + m = SUC (n+m)`;tensor] THEN SIMP_TAC [LAMBDA_BETA;ARITH_RULE 
` 1 <=  SUC (n + m)`] THEN SIMP_TAC [ ARITH_RULE `(n + m = m + n) /\ 
(SUC (n + m) <= m <=> F) /\ (SUC (n + m) - m = SUC n)`] THEN
SIMP_TAC [ARITH_RULE `((~(1 <= n) /\ 1 <= SUC n /\ 
SUC (m + n) <= dimindex (:N)) <=> (n = 0 /\ SUC (m + n) <= dimindex (:N)))`;
MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN SIMP_TAC[tensor;
K_DEF;ARITH_RULE ` SUC (m+0) = SUC m /\ (m+0) = m`] THEN
SIMP_TAC[GSYM (REWRITE_RULE[EQ_CLAUSES] (SIMP_CONV[GSYM tensor_mlem1] 
` m <= dimindex (:N) ==> tensor m modes1 y =
tensor m ((lambda i. if i <= m then modes1$i else modes2$(i-m)):bqs^N) y`));
ARITH_RULE `(n = 0 /\ SUC(m+n) <= dimindex (:N)) <=> n = 0 /\ 
SUC(m+n) <= dimindex (:N) /\  m <= dimindex (:N)`] THEN
SIMP_TAC [ARITH ;COMPLEX_MUL_RID]);;





let tensor_mnlem = prove( `!(n:num). 
 n+m <= dimindex (:N) ==> (\y:real^N. (tensor m modes1) y * 
(tensor n (modes2:bqs^N)) ((lambda i. y$(i+m)):real^N))
= tensor (m+n) ((lambda i. if (i<=m) then
 modes1$i else modes2$(i-m)):bqs^N)`,
GEN_TAC THEN ASM_CASES_TAC ` 1 <= n` THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC [tensor_mnlem1;MESON[] 
`(p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
SIMP_TAC [tensor;K_DEF;ARITH_RULE `~(1 <= n)  <=> n = 0 `;
MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`]
THEN SIMP_TAC[GSYM (REWRITE_RULE[EQ_CLAUSES] 
(SIMP_CONV[GSYM tensor_mlem1] ` m <= dimindex (:N)
 ==> tensor m modes1 = tensor m ((lambda i. if i <= m then 
 modes1$i else modes2$(i-m)):bqs^N)`)); ARITH_RULE 
 `((m + 0) = m) /\ ((n = 0 /\ n+m <= dimindex (:N)) <=> 
 n = 0 /\ n+m <= dimindex (:N) /\  m <= dimindex (:N))`;
 ETA_AX;COMPLEX_MUL_RID]);;
    
    
    

let mode_tensor = prove(`!modes x k n. (n+1) <= dimindex (:N) 
/\ k <= (n+1) /\ 0 < k /\ (modes$k = (x:bqs)) ==> 
tensor (n+1) (modes:bqs^N) = 
tensor (n+1) ((lambda i. if (i=k) then x else modes$i):bqs^N)`,
REPEAT GEN_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN 
INDUCT_TAC THENL [SIMP_TAC[ARITH] THEN SIMP_TAC[ONE;tensor] THEN
IMP_REWRITE_TAC[ADD1;ARITH;LAMBDA_BETA;ARITH_RULE `1  <= 1`] THEN
IMP_REWRITE_TAC [MESON[ARITH_RULE `(k <= 1 /\ 0 < k) <=> k = 1`] 
`((1 <= dimindex (:N)) /\ (k <= 1 /\ 0 < k ) /\ 
(modes$k = x)) <=> ((k = 1) /\ (1 <= dimindex (:N)) /\ (modes$1 = x))`]; 
ASM_CASES_TAC `k < SUC n +1` THENL [POP_ASSUM MP_TAC THEN 
SIMP_TAC[MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN 
ASM_SIMP_TAC [tensor; MESON[CONJ_ACI;ARITH_RULE 
`(k < SUC n + 1  /\ k <= SUC n + 1) <=>  (k <= n + 1)` ] 
`((k < SUC n + 1  /\ SUC n + 1 <= dimindex (:N) /\ 
k <= SUC n + 1 /\ 0 < k /\ modes$k = x)  <=>  
(k <= n + 1  /\ SUC n + 1 <= dimindex (:N) /\ 0 < k /\ modes$k = x) )`; 
ARITH_RULE ` (SUC n + 1 = SUC (n+1)) /\ (SUC n + 1 <= dimindex (:N) 
==> n + 1 <= dimindex (:N))`] THEN IMP_REWRITE_TAC [LAMBDA_BETA;
ARITH_RULE `1 <= SUC (n + 1) `] THEN IMP_REWRITE_TAC [ARITH_RULE 
`k <= n + 1  ==> ((SUC (n + 1) = k) = F)`]; POP_ASSUM MP_TAC THEN
SIMP_TAC[MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
ASM_SIMP_TAC [tensor; MESON[CONJ_ACI;ARITH_RULE 
`(~(k < SUC n + 1)  /\ k <= SUC n + 1) <=>  (k = SUC n + 1)` ] 
`((~(k < SUC n + 1)  /\ SUC n + 1 <= dimindex (:N) /\ 
k <= SUC n + 1 /\ 0 < k /\ modes$k = x) <=> (k = SUC n + 1 /\ 
SUC n + 1 <= dimindex (:N) /\ 0 < k /\ modes$(SUC n + 1) = x) )`; 
ARITH_RULE ` (SUC n + 1 = SUC (n+1)) /\ 
(SUC n + 1 <= dimindex (:N)  ==> n + 1 <= dimindex (:N))`] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `SUC (n + 1) <= dimindex (:N) <=> 
(SUC (n + 1) <= dimindex (:N)  /\ (n + 1) <= dimindex (:N))` ] 
THEN ONCE_SIMP_TAC[ (ISPECL [`n+1`] tensor_mlem1d)] THEN
SIMP_TAC [MESON[ARITH_RULE `i <= n + 1 ==> ((i = SUC (n + 1)) = F)`] 
`(if i <= n + 1 then if i = SUC (n + 1) then k1 else k2 else k3) = 
(if i <= n + 1 then  k2 else k3)`] THEN 
ASM_SIMP_TAC[GSYM (ISPECL [`n+1`] tensor_mlem1d)] THEN
ASM_SIMP_TAC[LAMBDA_BETA;ARITH_RULE `1  <= SUC (n + 1)`;LAMBDA_ETA]]]);;
     
     


let tensor_blin_smul = prove(`!a x modes k n. (n+1) <= dimindex (:N) 
/\ k <= (n+1) /\ 0 < k /\ (modes$k = (((a:complex)%x):bqs))
==>  tensor (n+1) (modes:bqs^N)  = 
a % tensor (n+1) ((lambda i. if (i=k) then x else modes$i):bqs^N)`,
SIMP_TAC [(SPEC_V ("x", "a%x") mode_tensor)] THEN 
REPEAT GEN_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN
INDUCT_TAC THENL [SIMP_TAC[ARITH] THEN SIMP_TAC[ONE;tensor] THEN
IMP_REWRITE_TAC[ADD1;ARITH;LAMBDA_BETA;ARITH_RULE `1  <= 1`] THEN
IMP_REWRITE_TAC [MESON[ARITH_RULE `(k <= 1 /\ 0 < k) <=> k = 1`]  
`(1 <= dimindex (:N) /\ k <= 1 /\ 0 < k /\ (modes$k = ((a % x):bqs)))
 <=> (1 <= dimindex (:N) /\ k = 1 /\ (modes$k = ((a % x):bqs)))`] 
THEN SIMP_TAC[K_THM] THEN SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_RID] 
THEN CFUN_ARITH_TAC; SIMP_TAC[ARITH_RULE `SUC n + 1 = SUC (n+1)`;
tensor;GSYM ONE] THEN ASM_CASES_TAC `k <= n+1` THENL [POP_ASSUM MP_TAC 
THEN SIMP_TAC[MESON[] `(p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
IMP_REWRITE_TAC [LAMBDA_BETA;ARITH_RULE `1 <= SUC (n + 1) `] THEN
IMP_REWRITE_TAC [ARITH_RULE `k <= n + 1 ==> ((SUC (n + 1) = k) = F)`] 
THEN IMP_REWRITE_TAC [ARITH_RULE `(SUC (n + 1) <= dimindex (:N))
 ==> n + 1 <= dimindex (:N)`] THEN CFUN_ARITH_TAC; 
POP_ASSUM MP_TAC THEN SIMP_TAC[MESON[] `(p==>q==> Q) <=> (p /\ q ==> Q)`]
 THEN SIMP_TAC [MESON[CONJ_ACI;ARITH_RULE `(~(k <= n + 1) /\ 
 (k <= SUC (n + 1))) <=> (k = SUC (n + 1))`] 
 `(~(k <= n + 1) /\ SUC (n + 1) <= dimindex (:N) /\ 
 k <= SUC (n + 1) /\ 0 < k /\ (modes$k = ((a % x):bqs))) <=>  
( SUC (n + 1) <= dimindex (:N) /\ k = SUC (n + 1) /\ 
0 < k /\ (modes$k = ((a % x):bqs)))`] THEN
ONCE_ASM_REWRITE_TAC[ARITH_RULE `SUC (n + 1) <= dimindex (:N) <=>  
(SUC (n + 1) <= dimindex (:N) /\ (n + 1) <= dimindex (:N))` ] 
THEN ONCE_SIMP_TAC[ (ISPECL [`n+1`] tensor_mlem1d)] THEN
SIMP_TAC [MESON[ARITH_RULE `i <= n + 1 ==> ((i = SUC (n + 1)) = F)`] 
`(if i <= n + 1 then if i = SUC (n + 1) then k1 else k2 else k3) = 
(if i <= n + 1 then  k2 else k3)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`n+1`] tensor_mlem1d)] THEN
IMP_REWRITE_TAC[LAMBDA_BETA;ARITH_RULE `1  <= SUC (n + 1)`] THEN
CFUN_ARITH_TAC]]);;
    
    
    
    

let tensor_blin_add = prove (`!a b k modes n. (n+1) <= dimindex (:N) 
/\ k <= (n+1) /\ 0 < k /\ (modes$k = ((a+b):bqs)) ==> 
 tensor (n+1) (modes:bqs^N) = 
tensor (n+1) ((lambda i. if (i=k) then a else modes$i):bqs^N) +
tensor (n+1) ((lambda i. if (i=k) then b else modes$i):bqs^N)`,
SIMP_TAC [(SPEC_V ("x", "a+b") mode_tensor)] THEN 
REPEAT GEN_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN 
INDUCT_TAC THENL [SIMP_TAC[ARITH] THEN SIMP_TAC[ONE;tensor] THEN
IMP_REWRITE_TAC[ADD1;ARITH;LAMBDA_BETA;ARITH_RULE `1  <= 1`] THEN
IMP_REWRITE_TAC [MESON[ARITH_RULE `(k <= 1 /\ 0 < k) <=> (k = 1)`]
`(k <= 1 /\ 0 < k /\ (modes$k = ((a+b):bqs))) <=> (k = 1 /\ 
(modes$k = ((a+b):bqs)))`] THEN SIMP_TAC[K_THM] THEN  
SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_RID] THEN CFUN_ARITH_TAC; 
SIMP_TAC[ARITH_RULE `SUC n + 1 = SUC (n+1)`;tensor;GSYM ONE] THEN
ASM_CASES_TAC `k <= n+1` THENL [ POP_ASSUM MP_TAC  THEN
SIMP_TAC[MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
IMP_REWRITE_TAC [LAMBDA_BETA;ARITH_RULE `1 <= SUC (n + 1) `] THEN
IMP_REWRITE_TAC [ARITH_RULE `k <= n + 1 ==> ((SUC (n + 1) = k) = F)`] 
THEN SIMP_TAC[CFUN_ADD_THM;COMPLEX_ADD_RDISTRIB] THEN
IMP_REWRITE_TAC [ARITH_RULE `(SUC (n + 1) <= dimindex (:N)) 
==> n + 1 <= dimindex (:N)`] THEN CFUN_ARITH_TAC; 
POP_ASSUM MP_TAC THEN SIMP_TAC[MESON[] `(p==>q==> Q) <=> 
(p /\ q ==> Q)`] THEN SIMP_TAC [MESON[CONJ_ACI;ARITH_RULE 
`(~(k <= n + 1) /\ k <= SUC (n + 1)) <=> (k = SUC (n + 1))`] 
`(~(k <= n + 1) /\ SUC (n + 1) <= dimindex (:N) /\ 
k <= SUC (n + 1) /\ 0 < k  /\ (modes$k = ((a+b):bqs))) <=> 
(SUC (n + 1) <= dimindex (:N) /\ k = SUC (n + 1) /\ 0 < k 
/\ (modes$k = ((a+b):bqs)))`] THEN 
ONCE_ASM_REWRITE_TAC[ARITH_RULE `SUC (n + 1) <= dimindex (:N) <=>  
(SUC (n + 1) <= dimindex (:N) /\ (n + 1) <= dimindex (:N))` ] THEN
ONCE_SIMP_TAC[ (ISPECL [`n+1`] tensor_mlem1d)] THEN
 SIMP_TAC [MESON[ARITH_RULE `i <= n + 1 ==> ((i = SUC (n + 1)) = F)`] 
 `(if i <= n + 1 then if i = SUC (n + 1) then k1 else k2 else k3) = 
(if i <= n + 1 then  k2 else k3)`] THEN
IMP_REWRITE_TAC[GSYM (ISPECL [`n+1`] tensor_mlem1d)] THEN
IMP_REWRITE_TAC[LAMBDA_BETA;ARITH_RULE `1  <= SUC (n + 1)`] 
THEN CFUN_ARITH_TAC]]);;
   
   

let mode_zero_tensor = prove(`!k modes n. k <= (n+1) /\ 
0 < k /\ (n+1) <= dimindex (:N) /\ (modes$k = cfun_zero) ==>  
tensor (n+1) (modes:bqs^N) =  K (Cx (&0))`,
SIMP_TAC [(SPEC_V ("x", "a%x") mode_tensor)] THEN 
REPEAT GEN_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN
INDUCT_TAC THENL [SIMP_TAC[ARITH; MESON[ADD_CLAUSES;CONJ_ACI;
ARITH_RULE `(k <= 0 + 1 /\ 0 < k) <=> (k = 1)`]  
`(k <= 0 + 1 /\ 0 < k /\ 0 + 1 <= dimindex (:N) /\ 
(modes$k = cfun_zero)) <=> (k = 1 /\ 1 <= dimindex (:N) /\ 
(modes$1 = cfun_zero))`] THEN SIMP_TAC[tensor;ONE] THEN
SIMP_TAC[K_THM; ADD1;ARITH; LAMBDA_BETA;cfun_zero;
ARITH_RULE `1 <= 1`;COMPLEX_MUL_LID] THEN CFUN_ARITH_TAC;  
ASM_CASES_TAC `k < SUC n +1` THENL [POP_ASSUM MP_TAC THEN 
SIMP_TAC[MESON[] `  (p==>q==> Q) <=> (p /\ q ==> Q)`] THEN
ASM_SIMP_TAC [tensor; MESON[CONJ_ACI;ARITH_RULE 
`((k < SUC n + 1) /\ k <= SUC n + 1)  <=>  (k <= n + 1)`]
`((k < SUC n + 1 /\ k <= SUC n + 1 /\ 0 < k /\ 
SUC n + 1 <= dimindex (:N) /\ (modes$k = cfun_zero))  <=>   
(k <= n + 1 /\ 0 < k /\ SUC n + 1 <= dimindex (:N) /\ 
(modes$k = cfun_zero)) )`; ARITH_RULE `(SUC n + 1 = SUC (n+1)) 
/\ (SUC n + 1 <= dimindex (:N)  ==> n + 1 <= dimindex (:N))`;
K_THM;COMPLEX_MUL_LZERO;COMPLEX_MUL_LID] THEN CFUN_ARITH_TAC; 
POP_ASSUM MP_TAC THEN SIMP_TAC[MESON[] `  (p==>q==> Q) <=> 
(p /\ q ==> Q)`] THEN ASM_SIMP_TAC [tensor; 
MESON[CONJ_ACI;ARITH_RULE `(~(k < SUC n + 1) /\ 
k <= SUC n + 1)  <=>  (k = SUC n + 1)`] 
`((~(k < SUC n + 1) /\ k <= SUC n + 1 /\ 0 < k /\ 
SUC n + 1 <= dimindex (:N) /\ (modes$k = cfun_zero)) 
 <=>  (k = SUC n + 1 /\ 0 < k /\ SUC n + 1 <= dimindex (:N) /\ 
 (modes$(SUC n + 1) = cfun_zero)))`; ARITH_RULE 
 `(SUC n + 1 = SUC (n+1)) /\ (1 <= SUC (n + 1))`;
 LAMBDA_BETA;cfun_zero;COMPLEX_MUL_RZERO;K_THM]
THEN CFUN_ARITH_TAC]]);;