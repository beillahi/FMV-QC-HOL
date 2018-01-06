(* ========================================================================= *)
(*                                                                           *)
(*                           tactics_1.ml                              *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: January 5th, 2018                                            *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "tensor_product_projection.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*) 

let spec_thm_tac thm = 
(CONV_RULE (RAND_CONV (RAND_CONV 
 (ONCE_REWRITE_CONV[CFUN_ARITH ` ((X:sm->(real->complex)) (x:sm)) = 
 Cx(&1) % ((X:sm->(real->complex)) (x:sm))`]))) (SPEC_ALL thm));;
 
(****************************************************************************************)

let conditionThmTac (n:int) =    
    let termstr = (String.concat "" ("i IN 1.."::[(string_of_int n)])) in 
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC NUM_REDUCE_CONV) THEN 
       REPEAT(MP_TAC(RAND_CONV NUMSEG_CONV (parse_term termstr)) THEN 
       ASM_REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY]) ;;
          
 let condition_thm n1 n3 = 
    let rec make_concl n i = if (i<n) then 
        "if i = " :: (string_of_int i) :: " then x" :: 
        (string_of_int i) :: " else " :: (make_concl n (i+1)) 
        else  "x" :: (string_of_int i) :: " else " :: ["g i):A"] in
    let make_cond n1 n2 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl n2 1) in
    let main_make_cond n1 n2 = parse_term (String.concat "" (make_cond n1 n2)) in 
    (prove( (mk_eq ((main_make_cond n1 n3), (main_make_cond n1 n1))), 
    conditionThmTac n1));;
        
(****************************************************************************************)
 
let conditionThm0Tac (n:int) =   
    let termstr = (String.concat "" ("i IN 1.."::[(string_of_int n)])) in 
       REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC NUM_REDUCE_CONV) THEN 
       REPEAT(MP_TAC(RAND_CONV NUMSEG_CONV (parse_term termstr)) THEN 
       ASM_REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN 
       CONV_TAC NUM_REDUCE_CONV) ;;
       
let condition_thm0 n1 n3 = 
    let rec make_concl n i = if (i<n) then 
        "if i = " :: (string_of_int i) :: " then x" :: 
        (string_of_int i) :: " else " :: (make_concl n (i+1)) 
        else  "x" :: (string_of_int i) :: " else " :: ["g i):A"] in
    let make_cond0 n1 n2 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl n2 0) in
    let make_cond n1 n2 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl n2 1) in
    let main_make_cond n1 n2 = parse_term (String.concat "" (make_cond n1 n2)) in 
    let main_make_cond0 n1 n2 = parse_term (String.concat "" (make_cond0 n1 n2)) in 
    (prove( (mk_eq ((main_make_cond0 n1 n3), (main_make_cond n1 n1))), 
    conditionThm0Tac n1));;

    
(****************************************************************************************)  

let rec condRecomposeTac (i:int) (j:int) (ll: int list)  =  
    let len = List.length ll in
        if (i=0) then  
          let termstr = (String.concat "" ("i IN 1.."::[(string_of_int (j+(List.nth ll i)))])) in 
          REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC NUM_REDUCE_CONV) THEN 
          REPEAT(MP_TAC(RAND_CONV NUMSEG_CONV (parse_term termstr)) THEN 
          (condRecomposeTac (i+1) (j+(List.nth ll i)) ll))
        else if (i<len) then 
          let termstr = (String.concat "" ("i IN 1.."::[(string_of_int (j+(List.nth ll i)))])) in 
          MP_TAC(RAND_CONV NUMSEG_CONV (parse_term termstr)) THEN
          (condRecomposeTac (i+1) (j+(List.nth ll i)) ll)
        else
          ASM_REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY];;
          
let condition_recompose m l  = 
    let rec make_concl1 n i = if (i<n) then 
        "if i = " :: (string_of_int i) :: " then x" :: (string_of_int i) :: 
        " else " :: (make_concl1 n (i+1)) 
        else  "x" :: (string_of_int i) :: " else " :: ["g i):A"] in
    let make_cond1 n1 n2 = "(if i <= " :: (string_of_int n1) :: 
        " /\ 1 <= i then " :: (make_concl1 n2 1) in
    let main_make_cond n1 n2 = parse_term (String.concat "" (make_cond1 n1 n2)) in
    let rec make_concl k n i = if (i<n) then 
        "if i = " :: (string_of_int (k+i)) :: " then x" :: 
        (string_of_int (k+i)) :: " else " :: (make_concl k n (i+1)) 
        else  "x" :: (string_of_int (k+i)) :: [""] in
    let rec main_make_concl l i k = 
        let len = List.length l in
            if (i<len) then
                (make_concl k (List.nth l i) 1) @ [" else " ] @ 
                (main_make_concl l (i+1) (k+(List.nth l i)))
            else [] in
        let rec make_fst_cond l i k = 
            let len = List.length l in
            if (i<(len-1)) then
            (make_fst_cond l (i+1) (k+(List.nth l i))) @ 
            ("if i <= " :: (string_of_int (k+(List.nth l i))) :: " then ":: []) 
            else [""] in
   (prove( (mk_eq ((parse_term (String.concat ""  ("(if i <= " :: 
    (string_of_int m) :: " /\ 1 <= i then " :: 
    (make_fst_cond l 0 0) @ (main_make_concl l 0 0) @ [" g i):A"]))), (main_make_cond m m))),
   condRecomposeTac 0 0 l));;

(****************************************************************************************)
            
let rew_condition_tac m l i = 
    let rec rew_condition m l i = 
        let len = List.length l in
        if (i < len)  then
            if (i = 0) then 
             (condition_thm (List.nth l i) m) :: (rew_condition (m-(List.nth l i)) l (i+1))
            else
             (condition_thm0 (List.nth l i) m) :: (rew_condition (m-(List.nth l i)) l (i+1))
        else
            [] in
        SIMP_TAC (rew_condition m l i);;
        
(****************************************************************************************)
        
let one_less n = 
    let thm_integer n =  
        parse_term (String.concat "" ("(1 <= " :: (string_of_int n) :: ["):bool"])) in
     map ARITH_RULE (map thm_integer (1--n));;

(****************************************************************************************)   
    
let rewrite_decompose_tac m l k i =
    let rec rewrite_decompose m l k i =  
       let len = List.length l in
       let thm_integer n m k = "((" :: (string_of_int m) :: " <= dimindex (:N) ==> (i <= " ::
       (string_of_int n) :: " ==> i + " :: (string_of_int k) :: " <= dimindex (:N))) /\ (1 <= i + " :: 
       (string_of_int k) :: [")):bool"] in 
        if (i < len)  then
            if (i = 0) then 
                (rewrite_decompose m l (k+(List.nth l i)) (i+1))
            else
            (parse_term (String.concat "" (thm_integer (List.nth l i) m k))) :: 
            (rewrite_decompose m l (k+(List.nth l i)) (i+1))
        else [] in  
    (ASM_SIMP_TAC ([ARITH_RULE `(((i:num) + j = k) <=> (if (j <= k) then i = k - j else F))`;
    LAMBDA_BETA] @ map ARITH_RULE (rewrite_decompose m l k i))) THEN CONV_TAC NUM_REDUCE_CONV;;
    
(****************************************************************************************)
     
let rewrite_recompose_tac m l k i =
    let rec rewrite_recompose m l k i =  
       let len = List.length l in
       let thm_integer n k  = "((("::(string_of_int n)::" <= dimindex (:N)) ==> (i <= "::
       (string_of_int n)::" ==> ((i - ":: (string_of_int k)::") <= dimindex (:N)))) /\ (~(i <= ":: 
       (string_of_int k):: ")  ==> (1 <= (i - ":: (string_of_int k)::[" )))):bool "] in 
        if (i < len)  then
           (parse_term (String.concat "" (thm_integer m k))) :: 
           (rewrite_recompose m l (k+(List.nth l i)) (i+1))
        else [] in
    ONCE_SIMP_TAC [(ISPECL [mk_numeral (Int m)] tensor_1mlem1d)] THEN       
    (ASM_SIMP_TAC ([ARITH_RULE `~(i <= j) ==> (((i:num) - j = k) <=> (i = k + j))`;
    LAMBDA_BETA] @ (map (REWRITE_RULE [SUB_0]) 
    (map ARITH_RULE (rewrite_recompose m l k i))))) THEN 
    CONV_TAC NUM_REDUCE_CONV ;; 
    
(****************************************************************************************)  


let read_file filename = 
let lines = ref [] in
let chan = Pervasives.open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; !lines
with End_of_file ->
  close_in chan;
  List.rev !lines ;;
  
(****************************************************************************************)   
  
let rec extract_port str0 str i j = 
    let len = String.length str in
    if (i < len) then 
      if ((((Char.code (String.get str i)) <= 122) && ((Char.code (String.get str i)) >= 97)) or 
        (((Char.code (String.get str i)) <= 90) && ((Char.code (String.get str i)) >= 65)) or 
        (((Char.code (String.get str i)) <= 57) && ((Char.code (String.get str i)) >= 48))) then
        
            (extract_port str0 str (i+1) (j+1))
            
      else if ((String.sub str i 1) = ",") then
         if (((String.sub str (i+1) 1) = "0") or ((String.sub str (i+1) 1) = "1")) then
         
            (extract_port (str0 @ [(String.sub str (i-j) j)]) str (i+2) 0)  
            
         else 
             (extract_port str0 str (i+1) j)
      else
         (extract_port str0 str (i+1) j)
    else
            str0;;

(****************************************************************************************)

let rec gate_column_sub str0 str new_circuits i j k   = 
      let element = fst (List.nth new_circuits k) in
      let element_size = snd (List.nth new_circuits k)  in
      let len  = String.length element in
      let size = List.length new_circuits in
      if (k < size) then
       if ((String.sub str 0 len) = element) then 
        (String.sub str 0 len)::string_of_int(element_size)::str0 @ [(String.sub str (i-j) j)]
       else 
        gate_column_sub str0 str new_circuits i j (k+1)
      else [];;
         
  
let rec gate_column str0 str new_circuits i j =
    let len = String.length str in
    if (i <= len)  then
      if ((String.sub str i 1) = ")")  then
        if ((String.sub str 0 9) = "FLIP_GATE") then
               (String.sub str 0 9)::"1"::str0 @ [(String.sub str (i-j) j)]
        else if ((String.sub str 0 13) = "HADAMARD_GATE") then
                (String.sub str 0 13)::"1"::str0 @ [(String.sub str (i-j) j)]
        else if (((String.sub str 0 7) = "CZ_GATE")) then
                 (String.sub str 0 7)::"2"::str0 @ [(String.sub str (i-j) j)]
        else if (((String.sub str 0 10) = "CNOT1_GATE") or ((String.sub str 0 10) = "CNOT2_GATE")) then 
                (String.sub str 0 10)::"2"::str0 @ [(String.sub str (i-j) j)]
        else if ((String.sub str 0 9) = "SWAP_GATE") then
                (String.sub str 0 9)::"2"::str0 @ [(String.sub str (i-j) j)]
        else if ((String.sub str 0 7) = "TS_GATE") then
                 (String.sub str 0 7)::"3"::str0 @ [(String.sub str (i-j) j)]
        else if (((String.sub str 0 13) = "TOFFOLI1_GATE") or ((String.sub str 0 13) = "TOFFOLI3_GATE") or
                ((String.sub str 0 13) = "FREDKIN1_GATE") or ((String.sub str 0 13) = "FREDKIN3_GATE")) then
                 (String.sub str 0 13)::"3"::str0 @ [(String.sub str (i-j) j)]
        else
            gate_column_sub str0 str new_circuits i j 0
      else
        if ((((Char.code (String.get str i)) <= 122) && ((Char.code (String.get str i)) >= 97)) or 
         (((Char.code (String.get str i)) <= 90) && ((Char.code (String.get str i)) >= 65)) or 
         (((Char.code (String.get str i)) <= 57) && ((Char.code (String.get str i)) >= 48))) then
            gate_column str0 str new_circuits (i+1) (j+1)
            else if ((String.sub str i 1) = ",") then
                gate_column (str0 @ [(String.sub str (i-j) j)]) str new_circuits (i+1) 0
            else
                gate_column str0 str new_circuits (i+1) 0
        else [];;
        
(****************************************************************************************)      
        
let rec gate_matrix file str new_circuits i  =
    let gates = read_file file in
    let len = List.length gates in
        if ( i < len) then
            gate_matrix file (str @ [(gate_column [] (List.nth gates i) new_circuits 0 0)]) new_circuits  (i+1)
        else
            str     ;;

(****************************************************************************************)          
            
let rec list_replace L n a= 
    match L with
    | [] -> []
    | (hd::l) -> if n = 0 then
                    a::l
                else
                    hd :: (list_replace l (n-1) a);;
                    
                    
                    
let rec connected_gates gate ports j i k =  
            if (j < (k+2)) then
             if (j = 1) then
              if (int_of_string (List.nth gate j) = k) then
               (connected_gates gate ports (j+1) i k) else  false
              else 
               if ( (List.nth gate j) = (List.nth ports i)) then
                (connected_gates gate ports (j+1) (i+1) k) else false
             else  true;;
             
    let rec list_replace_list gate ports j i k =
                if (j < k) then
                   list_replace_list gate (list_replace ports i (List.nth gate (2+k+j))) (j+1) (i+1) k
                else ports;;
                
let rec sub_procedure_1 gates ports  i j k ks = 
      let len_gates = List.length gates in
       if j < len_gates then
         if (k < (ks+1)) then
            if (connected_gates (List.nth gates j) ports 1 i k) then 
                [((string_of_int i) :: (List.nth gates j));(list_replace_list (List.nth gates j) ports 0 i k)]
            else 
                sub_procedure_1 gates ports  i j (k+1) ks
        else sub_procedure_1 gates ports  i (j+1) 1 ks
        else [];;
    
let rec sub_procedure_2 gates ports i ks fin =
        let len_gates = List.length gates in
        let len_port = List.length ports in
          if (ks > 0) then  
            if i <= (len_port - ks) then
               let sub2_result = sub_procedure_1 gates ports  i 0 1 ks in 
                 if sub2_result = [] then
                   sub_procedure_2 gates ports (i+1) ks fin
                 else 
   [(List.nth sub2_result 0)] @ ((sub_procedure_2 gates (List.nth sub2_result 1) (i+(int_of_string (List.nth (List.nth sub2_result 0) 2))) ks (fin+1)) )
            else 
                sub_procedure_2 gates ports i (ks-1) fin
           else [];;
           
let rec sub_procedure_3 gates ports i ks fin =
        let len_gates = List.length gates in
        let len_port = List.length ports in
          if (ks > 0) then  
            if i <= (len_port - ks) then
               let sub2_result = sub_procedure_1 gates ports  i 0 1 ks in 
                 if sub2_result = [] then
                   sub_procedure_3 gates ports (i+1) ks fin
                 else 
                  (sub_procedure_3 gates (List.nth sub2_result 1) (i+(int_of_string (List.nth (List.nth sub2_result 0) 2))) ks (fin+1))
            else 
                sub_procedure_3 gates ports i (ks-1) fin
           else fin;;

let rec sub_procedure_4 gates ports i ks fin =
        let len_gates = List.length gates in
        let len_port = List.length ports in
          if (ks > 0) then  
            if i <= (len_port - ks) then
               let sub2_result = sub_procedure_1 gates ports  i 0 1 ks in 
                 if sub2_result = [] then
                   sub_procedure_4 gates ports (i+1) ks fin
                 else 
                  (sub_procedure_4 gates (List.nth sub2_result 1) (i+(int_of_string (List.nth (List.nth sub2_result 0) 2))) ks (fin+1))
            else 
                sub_procedure_4 gates ports i (ks-1) fin
           else ports;;
           
let rec matrix_procedure str0 gates ports ks = 
    let fin = sub_procedure_3 gates ports 0 ks 0 in 
         if (fin > 0) then 
         matrix_procedure (str0 @ [sub_procedure_2 gates ports 0 ks 0]) gates (sub_procedure_4 gates ports 0 ks 0) ks
        else str0;;
                    
(****************************************************************************************)
let rec list_sum list = match list with
    | [] -> 0
    | head::tail -> head + list_sum tail;;
    

(****************************************************************************************)
let main_tab_gates l m =
    let rec tab_gates l i =
       let len = List.length l in
       let mem_list k = (List.nth (List.nth l i) k) in
       let mem_list1 k = (List.nth (List.nth l (i-1)) k) in
       if (i < len)  then 
            if  (i = 0)  then
                if ((int_of_string (mem_list 0)) = 0) then
                   (int_of_string (mem_list 2)) :: (tab_gates l (i+1))
                else 
                   (int_of_string (mem_list 0)) :: (int_of_string (mem_list 2)) :: (tab_gates l (i+1))
            else
                if ( ((int_of_string (mem_list1 0)) + (int_of_string (mem_list1 2))) = 
                     (int_of_string (mem_list 0))) then
                    (int_of_string (mem_list 2)) :: (tab_gates l (i+1))
                else
                    ((int_of_string (mem_list 0)) - (int_of_string (mem_list1 2)) - 
                    (int_of_string (mem_list1 0))) :: (int_of_string (mem_list 2)) ::
                    (tab_gates l (i+1))
       else [] in
    let k = tab_gates l 0 in
    if ((list_sum k) < m) then
       k @ [m-(list_sum k)]
    else    k;;

(****************************************************************************************)
let main_comp_inputs l m =
    let rec rewr_para_dev n k = 
            if (k < n)  then "(":: (rewr_para_dev n (k+1))
            else [] in
    let rec comp_inputs l m i =
      let len = List.length l in
      if (i < len)  then 
        if (i=0) then
         ((string_of_int m) :: "  = " :: (rewr_para_dev len 1)) @ 
         ((string_of_int (List.nth l i)):: (comp_inputs l m (i+1)))
        else
          " + " :: (string_of_int (List.nth l i)):: " ) " :: (comp_inputs l m (i+1))
      else [] in
      ARITH_RULE (parse_term (String.concat "" (comp_inputs l m 0)));;



(****************************************************************************************)
    
   let rec rewr_dev m i =    
        let rec rewr_para_dev n k = 
          if (k < n) then ("(" :: (rewr_para_dev n (k+1)))
          else  [] in
        let rec rewr_conc_orig n k = 
          if (k < n) then if(k=0) then
          (rewr_para_dev n 1) @ (" (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::
          ")" :: (rewr_conc_orig n (k+1)))
           else " * (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::")) " :: 
           (rewr_conc_orig n (k+1))
          else  [] in
        let rec rewr_sing_orig n k = 
          if (k < n) then if(k=0) then
          " (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::")" :: (rewr_sing_orig n (k+1))
           else " * (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::") " :: 
           (rewr_sing_orig n (k+1))
          else  [] in
        let rec rewr_conc_dev n k = 
          if (k < n) then if(k=0) then
           [" a0 * ("] @ (" (((f"::(string_of_int k)::":A^N->complex)) x"::
           (string_of_int k)::")" :: (rewr_conc_dev n (k+1)))
          else " * (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::") " :: 
          (rewr_conc_dev n (k+1))
          else  [")"] in
        let rec rewr_sing_dev n k l = 
          if (k < n) then if(k=0) then if (k=l) then 
            "  ((a0 % f0) x0) "::(rewr_sing_dev n (k+1) l)
           else "  ((f0) x0) "::(rewr_sing_dev n (k+1) l)
          else if (k=l) then 
           "* ((a0 % (f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::") "::
           (rewr_sing_dev n (k+1) l)
           else "* (((f"::(string_of_int k)::":A^N->complex)) x"::(string_of_int k)::") "::
           (rewr_sing_dev n (k+1) l)
          else [] in
        if (i < m) then
        (CFUN_ARITH (parse_term (String.concat "" ( ["! (f0:A^N->complex) a0. ("] @ (rewr_sing_dev m 0 i) @ [" = "] @ 
        (rewr_conc_dev m 0) @ [")"])) )) :: (rewr_dev m (i+1))
        else [(CFUN_ARITH (parse_term (String.concat "" ( ["! (f0:A^N->complex) . ( ("] @ (rewr_sing_orig m 0) @ 
        [")) =  ("] @ (rewr_conc_orig m 0)  @ [")"]))))];;

        
(****************************************************************************************)
     
let rewrite_l l =      
   let spec_k k = (ISPECL [mk_numeral (Int k)] tensor_1mlem1d) in 
        map spec_k l;;

(****************************************************************************************)
           
let integer_equiv n = 
    let thm_integer = ARITH_RULE `!n. n <= dimindex (:N) <=> 
    (n <= dimindex (:N) /\ (n-1) <= dimindex (:N))` in
    let spec_new thm x =  SPEC  (mk_numeral (Int x))  thm in 
    let once_acm_rewrite_new thm  = ONCE_ASM_REWRITE_TAC [thm] in 
    MAP_EVERY once_acm_rewrite_new (map (CONV_RULE NUM_REDUCE_CONV) 
    (rev (map (spec_new  thm_integer) (2--n))));;
    
(****************************************************************************************)
(****************************************************************************)
(*             Some useful linear algebra lemmas                            *)
(****************************************************************************)
let CFUN_ADD_LEMBDA =
 CFUN_ARITH `!f g. (\y:A^N. f y + g y) =
 (\y:A^N. f y) + (\y:A^N. g y)`;;

let CFUN_SUB_LEMBDA = 
CFUN_ARITH `!f g. (\y:A^N. f y - g y) = 
(\y:A^N. f y) - (\y:A^N. g y)`;;

let  CFUN_ADD_AC = 
CFUN_ARITH `(m:cfun) + (n:cfun) = n + m 
/\ (m + n) + (p:cfun) = m + n + p 
 /\ m + n + p = n + m + p`;;

let CFUN_SUB_AC = 
CFUN_ARITH`!(a:cfun)  (d:cfun) (f:cfun) . 
 a - ( d + f) = a - d - f /\
a - (d -f) = a - d + f /\ (a + d) - f = a + d - f `;;

let CFUN_ADD_RDISTRIB_NEW = CFUN_ARITH 
`!(a:complex) (b:complex) (x:cfun) (x1:cfun) (x2:cfun). 
(a + b) % x = a % x + b % x /\  
(a + b) % x + x1 = a % x + b % x + x1 /\ 
x2 + (a + b) % x + x1= x2+ a % (x:cfun) + b % x + x1`;;


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

(*

let thm1 =  MESON[REAL_OF_NUM_MUL;REAL_MUL_ASSOC;REAL_MUL_SYM]
`&m * &n * x = &(m * n) * x /\ &m * y * &n * x = &(m * n) * x * y /\ &m * &n = &(m * n) /\
z * &n  = &n * z /\ &n  * z * &m  = &(m * n) * z /\
z * &n * z2  = &n * z * z2   `;;


let thm2 =  REAL_FIELD `(y1:real) / x1 * y2 / x2 * z = (y1 * y2) / (x1 * x2) * z /\
y1 / x1 * z * y2 / x2  = (y1 * y2) / (x1 * x2) * z /\ 
(pi / x1) * x2 = pi * (x2 / x1) /\ 
x2  * (pi / x1)= pi * (x2 / x1) /\ 
z * (y1 / x1)  = (y1) / (x1) * z /\ 
z * (y1 / x1) * z2  = (y1) / (x1) * z * z2 /\ 
y1 / x1 * z1 * y2 / x2 * z2 = (y1 * y2) / (x1 * x2) * z1 * z2 /\  
y1 / x1 * y2 / x2 = (y1 * y2) / (x1 * x2)`;;

let thm3 =  COMPLEX_FIELD `x1 * cexp(y1) * x2 * cexp(y2) = (x1 * x2) * (cexp(y1) * cexp(y2)) /\
x1 * cexp(y1) * x2 * cexp(y2) * x3 = (x1 * x2 * x3) * (cexp(y1) * cexp(y2)) /\
cexp(y1) * x2 * cexp(y2) * x3 = (x2 * x3) * (cexp(y1) * cexp(y2)) /\
 cexp(y1) *  cexp(y2) * x3 = x3 * (cexp(y1) * cexp(y2)) /\ 
  cexp(y1) * x3 *  cexp(y2)  = x3 * (cexp(y1) * cexp(y2)) /\
 x2 *  cexp(y1) * x3 *  cexp(y2)  = (x2 * x3) * (cexp(y1) * cexp(y2)) /\
x1 * cexp(y1) *  cexp(y2) * x3 = (x1 * x3) * (cexp(y1) * cexp(y2)) /\ 
x1 * cexp(y1) * x2 * x3 * cexp(y2) = (x1 * x2 * x3) * (cexp(y1) * cexp(y2)) /\
x1 * cexp(y1) * x2 * x4 * cexp(y2) * x3 = (x1 * x2 * x4 * x3) * (cexp(y1) * cexp(y2)) /\
cexp(y1) * x1 * x2 * cexp(y2) * x3 = (x1 * x2 * x3) * (cexp(y1) * cexp(y2)) /\
x1 * cexp(y1) * x2 * x3 = (x1 * x2 * x3) * cexp(y1) /\ 
x1 * (ii * x2)  =ii * (x1 * x2) `;;  

*)

    
let thm4 =  prove( ` ii * x = x * ii /\
x * ii * y =  (x*y) * ii  /\ x * y * ii  = (x*y) * ii  /\
x * --ii * y =  (x*y) * --ii  /\ x * y * --ii  = (x*y) * --ii  /\
x * ii + y * ii = (x + y) * ii /\  x * ii + y * --ii = (x - y) * ii /\
x * --ii + y * ii = (y - x) * ii /\ x * --ii + y * --ii = (x + y) * --ii`,
SIMP_TAC[COMPLEX_MUL_AC;COMPLEX_MUL_LNEG;COMPLEX_MUL_RNEG;GSYM COMPLEX_POW_2;
COMPLEX_POW_II_2;COMPLEX_MUL_LID] THEN CONV_TAC COMPLEX_FIELD);;

let thm5 =  prove( ` (&x / sqrt(&y)) * &z = &z * (&x / sqrt(&y)) /\ 
(&x / sqrt(&y)) * &z * (v:real) = &z * (&x / sqrt(&y)) * v /\
(&x / sqrt(&y)) * (&z / &t) = (&z / &t) * (&x / sqrt(&y)) /\
 (&x / sqrt(&y)) * (&z / &t) * v = (&z / &t) * (&x / sqrt(&y)) * v  `, 
CONV_TAC REAL_FIELD);;

let CEXP_II_PI = prove(`cexp (ii * Cx(pi)) = --Cx(&1)`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI;
    SIN_PI;COMPLEX_ADD_RID;COMPLEX_MUL_RZERO;CX_NEG]);;  
    
let CEXP_II_PI_CNJ = prove(`cexp (-- (ii * Cx(pi))) = --Cx(&1)`,
   REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI;COMPLEX_ADD_RID;
    REAL_POS; SIN_PI;COS_NEG;SIN_NEG;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;CX_NEG] THEN 
    CONV_TAC COMPLEX_FIELD);; 
    
let CEXP_II_PI2 = prove(`cexp (ii * Cx(pi / &2)) = ii`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI2;
    SIN_PI2;COMPLEX_ADD_LID;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID]);; 
    
let CEXP_II_PI2_CNJ = prove(`cexp (--(ii * Cx(pi / &2))) = --ii`,
    REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI2;COMPLEX_ADD_RID;
    REAL_POS; SIN_PI2;COS_NEG;SIN_NEG;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;CX_NEG] THEN 
    CONV_TAC COMPLEX_FIELD);; 

let SIN_PI4 = prove
 (`sin(pi / &4) = sqrt(&1 / &2)`,
  MP_TAC(SPEC `pi / &4` SIN_CIRCLE) THEN
  SIMP_TAC[SPEC `pi / &4` COS_SIN; REAL_ARITH `p / &2 - p / &4 = p / &4`] THEN
  REWRITE_TAC[REAL_RING `x pow 2  + x pow 2= &1 <=> x pow 2 = &1 / &2 `] THEN
  MP_TAC (SPEC `sin(pi / &4)` (SPEC `&1 / &2` SQRT_UNIQUE)) THEN 
  MP_TAC(SPEC `pi / &4` SIN_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
  
let COS_PI4 = prove
 (`cos(pi / &4) = sqrt(&1 / &2)`,
  SIMP_TAC[SIN_PI4;SPEC `pi / &4` COS_SIN; REAL_ARITH `p / &2 - p / &4 = p / &4`]);;
  
let CEXP_II_PI4 = prove(`cexp (ii * Cx(pi / &4)) = Cx(&1 / sqrt(&2)) + ii * Cx(&1 / sqrt(&2))`,
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI4;SQRT_DIV;SQRT_1;
REAL_POS; SIN_PI4]);; 

let CEXP_II_PI4_CNJ = prove(`cexp (--(ii * Cx(pi / &4))) = Cx(&1 / sqrt(&2)) - ii * Cx(&1 / sqrt(&2))`,
    REWRITE_TAC[MESON[CX_NEG;COMPLEX_MUL_RNEG] `--(ii * Cx(x)) = ii * Cx(--x)`] THEN
    REWRITE_TAC[CEXP_EULER;GSYM CX_COS;GSYM CX_SIN;COS_PI4;SQRT_DIV;SQRT_1;
    REAL_POS; SIN_PI4;COS_NEG;SIN_NEG] THEN 
    REWRITE_TAC[CX_NEG;GSYM complex_sub;COMPLEX_MUL_RNEG]);; 
    
(****************************************************************************************)
    