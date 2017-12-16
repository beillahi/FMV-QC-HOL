(* ========================================================================= *)
(*                                                                           *)
(*                        multi_mode.ml                                   *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: May 18, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "single_mode.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)  
let tensor = new_recursive_definition num_RECURSION
   `tensor 0 (modes:cfun^N) = K (Cx(&1)) /\
    tensor (SUC n) (modes) = (\y:A^N. ((tensor n modes) y) *  (modes $ (SUC n))
    (y $ (SUC n)))`;;
    
let is_tensor = new_definition
  `is_tensor (tens:cops^N->(A^N->complex)-> (A^N->complex)) <=>
    !(ops:cops^N) (modes:cfun^N) n. is_linear_cop (tens ops) /\
      tens ops  (tensor n modes) = tensor n (lambda i. (ops$i) (modes$i))`;;

let COP_TENSOR_CFUN = prove
(`!(tens:cops^N->(A^N->complex)-> (A^N->complex)) ops modes n. is_tensor tens
 ==>  
    tens ops  (tensor n modes) = tensor n (lambda i. (ops$i) (modes$i))`,
   SIMP_TAC[is_tensor]);; 
   
let COP_TENSOR_LINEAR = prove
(`!(tens:cops^N->(A^N->complex)-> (A^N->complex)) ops. is_tensor tens ==>  
is_linear_cop (tens ops)`,
   SIMP_TAC[is_tensor]);; 
 
let CFUN_LAMBDA_APP = prove(`!f g.((lambda i. f i (g i)):cfun^N) =
   (lambda i. (((lambda j. f j):(cfun->cfun)^N)$i) (((lambda j. g j):cfun^N)$i))`
   ,SIMP_TAC[CART_EQ;LAMBDA_BETA]);;
 
let COP_LAMBDA_COMPS = prove(
`! f g x. (lambda i. ((((lambda j. f j):(B->A)^N)$i) o
   (((lambda j. g j):(C->B)^N)$i)) ):(C->A)^N = (lambda i. (((lambda j. (f j) o 
   (g j)):(C->A)^N)$i) ):(C->A)^N`,
   SIMP_TAC[o_THM;CART_EQ;LAMBDA_BETA]);;
   
let LAMBDA_RAPP = prove(`!f g.((lambda i. (f i) (((lambda j. g j):B^N)$i)):A^N) =
   (lambda i. (f i) (g i))`
   ,SIMP_TAC[CART_EQ;LAMBDA_BETA]);;

let LAMBDA_LAPP = prove(`!f g.((lambda i.  (((lambda j. g j):(B->A)^N)$i) (f i)):A^N) =
   (lambda i. (g i) (f i) )`
   ,SIMP_TAC[CART_EQ;LAMBDA_BETA]);; 
   
let COP_TENSOR_ASSOC= prove
 (`!ten (ops1:cops^N) (ops2:cops^N) n (modes:cfun^N).
     is_tensor ten ==> ten ops2 ( ten ops1 (tensor n modes)) =
     ten ((lambda i. (ops2$i) o (ops1$i)):cops^N) (tensor n modes)`,
     SIMP_TAC[is_tensor;LAMBDA_RAPP;LAMBDA_LAPP;o_DEF]);;


(****************************************************************************)
(* BEAM SPLITTER  & PHASE SHIFTER                                                          *)
(****************************************************************************)

new_type_abbrev("bmsp",`:complex#complex#complex#complex#sm#sm#sm#sm`);;


let pos = new_definition
 `pos (tens:cops^N->(A^N->complex)-> (A^N->complex)) (op:cops) m = 
    tens (lambda i. if i = m then op else I)`;;
    

let is_beam_splitter = new_definition 
  `is_beam_splitter (p1,p2,p3,p4,ten,i1,m1,i2,m2,o1,m3,o2,m4) <=> 
     is_sm i1 /\ is_sm i2 /\ is_sm o1 /\ is_sm o2
     /\ w i1 = w i2 /\ w i2 = w o1 /\ w o1 = w o2 /\ 
       vac i1 = vac i2 /\ vac i2 = vac o1 /\ vac o1 = vac o2 /\  
     pos ten (anh i1) m1 = p1 % pos ten (anh o1) m3 + 
       p2 % pos ten (anh o2) m4 
    /\ pos ten (anh i2 ) m2  = p3 % pos ten (anh o1) m3 + 
       p4 % pos ten (anh o2) m4 
    /\
    pos ten (cr i1) m1  = cnj p1 % pos ten (cr o1) m3  + 
       cnj p2 % pos ten (cr o2)  m4 
    /\ pos ten (cr i2) m2  = cnj p3 % pos ten (cr o1) m3  + 
       cnj p4 % pos ten (cr o2) m4`;;
     

let PHASE_SHIFTER = new_definition
       `PHASE_SHIFTER (ten,f,i1,m1,o1,m2) <=> 
         (is_sm i1 /\ is_sm o1 /\ w i1 = w o1 /\ vac i1 = vac o1 /\
   pos ten (cr i1) m1 = (cexp (--ii * Cx f)) % pos ten (cr o1) m2 /\
   pos ten (anh i1) m1 = (cexp (ii * Cx f)) % pos ten (anh o1) m2)`;;
(****************************************************************************)
(* MACH-ZEHNDER                                                             *)
(****************************************************************************)

let keylem  =   GEN_ALL ( MESON[]  `(p x ==> f x = q) ==> (if p x then q else (f x)) = f x`);;
let MULTI_MODE_DECOMPOSE_TAC = 
        ONCE_REWRITE_TAC[MESON[I_THM] `(if p then (x:bqs) else y) = (if p then x else I y)`] THEN 
        ONCE_REWRITE_TAC[MESON[] `(if p then f1 x else f2 y) = (if p then f1  else f2 ) (if p then  x else  y)`]
        THEN ONCE_REWRITE_TAC[CFUN_LAMBDA_APP] THEN
        SIMP_TAC[keylem;ARITH;COND_ID] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[(MATCH_MP (GSYM COP_TENSOR_CFUN) th)]);;

let CFUN_FLATTEN_TAC =
            REWRITE_TAC[COP_MUL_THM;COP_SMUL_THM;COP_ADD_THM;CFUN_SMUL;FUN_EQ_THM;CFUN_ADD_THM]
            THEN REWRITE_TAC[COMPLEX_MUL_SYM;COMPLEX_ADD_AC];;
let mirror = new_definition
       `mirror (ten,i1,m1,o1,m2) <=> 
   pos ten (cr i1) m1 = --ii % pos ten (cr o1) m2 /\
   pos ten (anh i1) m1 = ii % pos ten (anh o1) m2`;;