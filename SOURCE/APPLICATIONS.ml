(* ========================================================================= *)
(*                                                                           *)
(*                        APPLICATIONS.ml                                                *)
(*                                                                           *)
(*                                                                           *)
(*                                                                           *)
(* Last update: October 24, 2016                                               *)
(*                                                                           *)
(* ========================================================================= *)


(*-------------REQUIRED LIBRARIES ---------------------*)


needs "FULL_ADDER.ml";;



(*-----------------------------------------------------*)
(*----------------Formalization------------------------*)
(*-----------------------------------------------------*)
(*--------------------**********************------------------*)  

(****************************************************************************************)
(**************** Grover's oracle ********************************************************)
(****************************************************************************************)

let grover = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 5 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE((b0:sm),c0,c1,b1,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b1,d0,d1,b2,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b2,e0,i0,b3,e1,i1,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d1,b3,b4,d2,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c1,b4,b5,c2,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(d2,e1,i1,d3,e2,i2,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(e2,i2,e3,i3,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d3,e3,e4,d4,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c2,e4,e5,c3,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(c3,d4,i3,c4,d5,i4,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(d5,i4,d6,i5,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b5,e5,e6,b6,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c4,d6,d7,c5,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b6,d7,d8,b7,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b7,c5,i5,b8,c6,i6,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(c6,i6,c7,i7,ten,LH,LV,m_modes_pro)  /\ 
SWAP_GATE(b8,c7,c8,b9,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(b9,i7,b10,i8,ten,LH,LV,m_modes_pro) ==>
tensor 5 ((lambda i. if i = 1 then LH (b0) else if i = 2 then  LV (c0) else
if i = 3 then  LV (d0) else if i = 4 then  LV (e0) else LH (i0)):bqs^N) = 
Cx (&1 / &4951760157141521099596496896) %
tensor 5 (lambda i. if i = 1 then LV e6 else if i = 2 then LV d8
else if i = 3 then LV c8 else if i = 4 then LH b10 else LV i8)`,
quantum_tac (matrix_procedure [] (gate_matrix "test1.txt" [] [] 0) 
     (extract_port [] "(b0,0,c0,1,d0,1,e0,1,i0,0)" 0 0) 3) 5 0 0 []);;   
CPU time (user): 273.830371
(* 5 * 2 + 12 * 10 + 4 * 4 +  4 * 12= 120+16+24+10=170*)
( 10 * 3 + 4 + 4 * 3=  46)
   
(****************************************************************************************)
(*************hwb4 is the hidden weighted bit function with parameter N=4****************)
(****************************************************************************************)   
   
let hwb4 = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 4 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\    
CNOT2_GATE(a0,b0,a1,b1,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b1,c0,c1,b2,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(b2,d0,b3,d1,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(c1,b3,c2,b4,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(a1,c2,a2,c3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c3,b4,b5,c4,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(a2,b5,a3,b6,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c4,d1,d2,c5,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(a3,b6,d2,a4,b7,d3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a4,b7,b8,a5,ten,LH,LV,m_modes_pro) /\
TOFFOLI1_GATE(a5,d3,c5,a6,d4,c6,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d4,c6,c7,d5,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b8,a6,a7,b9,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(b9,c7,b10,c8,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b10,c8,c9,b11,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(a7,c9,a8,c10,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b11,d5,d6,b12,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(a8,c10,d6,a9,c11,d7,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(d7,b12,d8,b13,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(a9,c11,a10,c12,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d8,b13,b14,d9,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c12,b14,b15,c13,ten,LH,LV,m_modes_pro) ==>
tensor 4 ((lambda i. if i = 1 then LH (a0) else if i = 2 then  LV (b0) 
else if i = 3 then  LV (c0) else LH (d0)):bqs^N) = 
Cx (&1 / &79228162514264337593543950336) %
 tensor 4 (lambda i. if i = 1 then LV a10 else if i = 2
 then LH b15 else if i = 3 then LH c13 else LV d9)`,
quantum_tac (matrix_procedure [] (gate_matrix "test3.txt" [] [] 0) 
   (extract_port [] "(a0,0,b0,1,c0,1,d0,0)" 0 0) 3) 4 0 0 []);;
   
CPU time (user): 277.812766
(* 4 * 2 + 12 * 10 + 9 * 4 +  3 * 12= 120+36+36+8=200*)
( 10 * 3 + 9 + 3 * 3=  48)

(***************gf23mult finds product of two elements of a field GF(23)*****************)
(***********a=a0+a1x+a2x2 and b=b0+b1x+b2x2 with the output*******************************)
(************* ab=c=c0+c1x+c2x2 written on the last 3 bits *******************************)

let gf23mult = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 9 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
SWAP_GATE(a2,b0,b01,a21,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b1,b2,b21,b11,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a21,b21,b22,a22,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(a22,b11,c0,a23,b12,c1,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a1,b01,b02,a11,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b22,a23,a24,b23,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b23,b12,b13,b24,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a11,a24,a25,a12,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a12,b13,b14,a13,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(a13,b24,c1,a14,b25,c2,ten,LH,LV,m_modes_pro) /\   
SWAP_GATE(a25,b14,b15,a26,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a26,a14,a15,a27,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c2,d0,d1,c3,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(a27,b25,d1,a28,b26,d2,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d2,c3,c4,d3,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(d3,e0,d4,e1,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(c4,d4,c5,d5,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b02,b15,b16,b03,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b03,a15,a16,b04,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a28,b26,b27,a29,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b04,b27,b28,b05,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d5,e1,e2,d6,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c5,e2,e3,c6,ten,LH,LV,m_modes_pro)  /\ 
TOFFOLI3_GATE(b05,a29,e3,b06,a210,e4,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a16,b28,b29,a17,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a17,b06,b07,a18,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a18,a210,a211,a19,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b16,b29,b210,b17,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b17,b07,b08,b18,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b18,a211,a212,b19,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b19,a19,e4,b110,a110,e5,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b210,b08,b09,b211,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b211,a212,a213,b212,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b212,b110,b111,b213,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b213,a110,a111,b214,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a0,b09,b010,a01,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a01,a213,a214,a02,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a02,b111,b112,a03,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a03,a111,a112,a04,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(a04,b214,e5,a05,b215,e6,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a112,a05,a06,a113,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a113,b215,b216,a114,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b010,a214,a215,b011,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b011,b112,b113,b012,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b012,a06,a07,b013,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b013,b216,b217,b014,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(c6,d6,d7,c7,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(e6,d7,d8,e7,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b014,a114,d8,b015,a115,d9,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a07,b217,b218,a08,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a08,b015,b016,a09,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(a09,a115,a116,a010,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b113,b218,b219,b114,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b114,b016,b017,b115,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b115,a116,a117,b116,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b116,a010,d9,b117,a011,d10,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b017,a117,a118,b018,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b018,b117,b118,b019,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(e7,c7,c8,e8,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(d10,c8,c9,d11,ten,LH,LV,m_modes_pro) /\ 
TOFFOLI3_GATE(b019,a011,c9,b020,a012,c10,ten,LH,LV,m_modes_pro) ==>
tensor 9 ((lambda i. if i = 1 then LH (a0) else if i = 2 then  LH (a1) else
if i = 3 then LH (a2) else if i = 4 then  LV (b0) else 
if i = 5 then LV (b1) else if i = 6 then  LV (b2) else
if i = 7 then  LH (c0) else if i = 8 then  LH (d0) else LH (e0)):bqs^N) = 
Cx (&1 / &587135645693458306972370149197334256843920637227079967676822742883052256278652110865924749596192175757983744) %
tensor 9 (lambda i. if i = 1 then LH a215 else if i = 2 then LV b219 else if i = 3
then LH a118 else if i = 4 then LV b118 else if i = 5 then LV b020 else if i = 6
then LH a012 else if i = 7 then LH c10 else if i = 8 then LH d11 else LH e8) `,
quantum_tac (matrix_procedure [] (gate_matrix "test2.txt" [] [] 0) 
(extract_port [] "(a0,0,a1,0,a2,0,b0,1,b1,1,b2,1,c0,0,d0,0,e0,0)" 0 0) 3) 9 0 0 []);;
        
CPU time (user): 13634.248279
(* 9 * 2 + 12 * 50 + 2 * 4 +  9 * 12= 600+8+108+18=734*)
( 50 * 3 + 4 + 12 * 3=  190)
(****************************************************************************************)



(****************************************************************************************)
(**  output is 1 if and only if the number of ones in the input pattern is 2, 3 or 4.  **)
(****************************************************************************************)   

let sym6 = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 10 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\
SWAP_GATE(x20,x30,x31,x21,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x21,x40,x41,x22,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x22,x50,x51,x23,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x23,x60,x61,x24,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x10,x31,x32,x11,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x11,x41,x42,x12,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x12,x51,x52,x13,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x13,x61,x62,x14,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x14,x24,a0,x15,x25,a1,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(x15,x25,x16,x26,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x32,x42,x43,x33,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x33,x52,x53,x34,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x34,x62,x63,x35,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x35,x16,x17,x36,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x36,x26,x27,x37,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x37,a1,b0,x38,a2,b1,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x27,x38,a2,x28,x39,a3,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(x28,x39,x29,x310,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x43,x53,x54,x44,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x44,x63,x64,x45,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x45,x17,x18,x46,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x46,x29,x210,x47,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x47,x310,x311,x48,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x48,a3,a4,x49,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x49,b1,c0,x410,b2,c1,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(a4,x410,b2,a5,x411,b3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a5,x411,x412,a6,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x311,x412,a6,x312,x413,a7,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(x312,x413,x313,x414,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x54,x64,x65,x55,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x55,x18,x19,x56,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x56,x210,x211,x57,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x57,x313,x314,x58,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x58,x414,x415,x59,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x59,a7,a8,x510,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x510,b3,b4,x511,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x511,c1,d0,x512,c2,d1,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(b4,x512,c2,b5,x513,c3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b5,x513,x514,b6,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a8,x514,x515,a9,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x515,a9,b6,x516,a10,b7,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x415,x516,a10,x416,x517,a11,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(x416,x517,x417,x518,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x65,x19,x110,x66,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x66,x211,x212,x67,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x67,x314,x315,x68,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(x68,x417,x418,x69,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x69,x518,x519,x610,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x610,a11,a12,x611,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(x611,b7,b8,x612,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x612,c3,d1,x613,c4,d2,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(b8,x613,c4,b9,x614,c5,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b9,x614,x615,b10,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a12,x615,x616,a13,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(x519,x616,a13,x520,x617,a14,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(x520,x617,x521,x618,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a14,b10,b11,a15,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(a15,c5,c6,a16,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(a16,d2,a17,d3,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c6,a17,a18,c7,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(c7,d3,c8,d4,ten,LH,LV,m_modes_pro)  ==>
tensor 10 ((lambda i. if i = 1 then LH (x10) else if i = 2 then  LH (x20) else
if i = 3 then LH (x30) else if i = 4 then  LV (x40) else 
if i = 5 then LV (x50) else if i = 6 then  LV (x60) else
if i = 7 then  LH (a0) else if i = 8 then  LH (b0) else 
if i = 9 then  LH (c0) else LH (d0)):bqs^N) = 
Cx (&1 / &559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944) %
tensor 10 (lambda i. if i = 1 then LH x110 else if i = 2 then LH x212
else if i = 3 then LH x315 else if i = 4 then LV x418 else if i = 5
then LH x521 else if i = 6 then LV x618 else if i = 7 then LH b11
else if i = 8 then LV a18 else if i = 9 then LH c8 else LV d4)`,                                         
quantum_tac (matrix_procedure [] (gate_matrix "test5.txt" [] [] 0) 
(extract_port [] "(x10,0,x20,0,x30,0,x40,1,x50,1,x60,1,a0,0,b0,0,c0,0,d0,0)" 0 0) 3) 10 0 0 []);;                 
    CPU time (user): 20679.371257    
(* 10 * 2 + 12 * 41 + 7 * 4 +  13 * 12= 156+492+28+20=696*)
( 41 * 3 + 7 + 13 * 3=  169)
(****************************************************************************************)

(****************************************************************************************)
(***2-to-4 decoder  has 3 inputs and 4 outputs. If enable bit (E, one of the 3 inputs) is low, ****)
(*** all the output lines will be zero. If the enable bit is high, one of the four output ****)
(***lines will become high selected by the remaining two input lines.***)
(****************************************************************************************)

let decoder = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 6 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\
SWAP_GATE(a0,b0,b1,a1,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE(a1,e0,i0,a2,e1,i01,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b1,a2,a3,b2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(i01,i1,i11,i02,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE(b2,e1,i11,b3,e2,i12,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b3,e2,o0,b4,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(b4,i12,o2,b5,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE(b5,i02,i2,b6,o1,o3,ten,LH,LV,m_modes_pro) ==>
tensor 6 ((lambda i. if i = 1 then LV (a0) else if i = 2 then  LH (b0) else
if i = 3 then LV (e0) else if i = 4 then  LH (i0) else 
if i = 5 then LH (i1) else LH (i2)):bqs^N) = 
Cx (&1 / &1152921504606846976) %
tensor 6 (lambda i. if i = 1 then LV a3 else if i = 2 then LH o0
else if i = 3 then LH o2 else if i = 4 then LH b6
else if i = 5 then LV o1 else LH o3)`,
quantum_tac (matrix_procedure [] (gate_matrix "test4.txt" [] [] 0) 
(extract_port [] "(a0,1,b0,0,e0,1,i0,0,i1,0,i2,0)" 0 0) 3) 6 0 0 []);;

CPU time (user): 132.209901
(* 6 * 2 + 12 * 5 + 20 * 3 = 132 *)
( 10 * 3 =  30)

(****************************************************************************************)

(****************************************************************************************)
(***************Function ham3 is the size 3 Hamming optimal coding function **************)
(****************************************************************************************)


let ham3 = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 3 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\
TOFFOLI1_GATE(a0,b0,c0,a1,b1,c1,ten,LH,LV,m_modes_pro) /\ 
CNOT1_GATE(b1,c1,b2,c2,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(b2,c2,b3,c3,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE(b3,c3,c4,b4,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(a1,c4,a2,c5,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(c5,b4,c6,b5,ten,LH,LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (a0) else if i = 2 then  LH (b0) else LH (c0)):bqs^N) = 
Cx (&1 / &1048576) %
tensor 3 (lambda i. if i = 1 then LV a2 else if i = 2 then LV c6 else LV b5)`,
quantum_tac (matrix_procedure [] (gate_matrix "test6.txt" [] [] 0) 
(extract_port [] "(a0,1,b0,0,c0,0)" 0 0) 3) 3 0 0 []);;

CPU time (user): 21.973659

(* 3 * 2 + 12 * 1 + 4 * 4 +  1 * 12= 16+24+6=46*)
(3 + 3 + 4 =  10)
(****************************************************************************************)
(*******nth_prime3_inc may be used to find primes with up to 3 binary digits************)
(****************************************************************************************)

let nth_prime3_inc= time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 3 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\
SWAP_GATE(b0,c0,c1,b1,ten,LH,LV,m_modes_pro) /\ 
CNOT2_GATE(a0,c1,a1,c2,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE(c2,b1,c3,b2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(c3,b2,b3,c4,ten,LH,LV,m_modes_pro) /\
TOFFOLI3_GATE(a1,b3,c4,a2,b4,c5,ten,LH,LV,m_modes_pro) /\
CNOT1_GATE(a2,b4,a3,b5,ten,LH,LV,m_modes_pro) ==>
tensor 3 ((lambda i. if i = 1 then LV (a0) else if i = 2 then  LH (b0) else LH (c0)):bqs^N) = 
Cx (&1 / &16777216) %
tensor 3 (lambda i. if i = 1 then LH a3 else if i = 2 then LV b5 else LH c5)`,
quantum_tac (matrix_procedure [] (gate_matrix "test7.txt" [] [] 0) 
(extract_port [] "(a0,1,b0,0,c0,0)" 0 0) 3) 3 0 0 []);;
CPU time (user): 18.712156
(* 3 * 2 + 12 * 2 + 3 * 4 +  1 * 12= 36+12+6=54*)
(2 * 3 + 3 + 3 =  12)
(****************************************************************************************)
(*******Highrarchical 3-qubit Ripple Full Adder************)
(****************************************************************************************)

let highrarchical_ripple_adder = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
10 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\ 
F_ADDER(a1,b1,c0,d0,d01,c1,f0,s1,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d01,c1,c11,d02,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d1,c11,c12,d11,ten,LH,LV,m_modes_pro) /\
F_ADDER(a2,b2,c12,d11,d12,c2,f1,s2,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d12,c2,c21,d13,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d2,c21,c22,d21,ten,LH,LV,m_modes_pro) /\   
F_ADDER(a3,b3,c22,d21,d22,c3,f2,s3,ten,LH,LV,m_modes_pro)  ==>
tensor 10 ((lambda i. if i = 1 then LH (a3) else if i = 2 then  LH (b3)
else if i = 3 then  LH (d2) else if i = 4 then  LV (a2) 
else if i = 5 then  LV (b2) else if i = 6 then  LH (d1)
else if i = 7 then  LV (a1) else if i = 8 then  LH (b1) 
else if i = 9 then  LH (c0) else LH (d0)):bqs^N) = 
Cx (&1 / &324518553658426726783156020576256) %
tensor 10 (lambda i. if i = 1 then LH d22 else if i = 2 then LH c3
else if i = 3 then LV f2 else if i = 4 then LV s3
else if i = 5 then LH d13 else if i = 6 then LH f1
else if i = 7 then LH s2 else if i = 8 then LV d02
else if i = 9 then LV f0 else LV s1)`,
quantum_tac (matrix_procedure [] ((gate_matrix "test11.txt" [] [("F_ADDER",4)] 0))  
(extract_port [] "(a3,0,b3,0,d2,0,a2,1,b2,1,d1,0,a1,1,b1,0,c0,0,d0,0)" 0 0) 4) 10 0 0 [("F_ADDER",full_adder_tac)]);;
CPU time (user): 1506.897917
(* 54 * 3 +  10 * 2 + 12 * 4 = 162+20+48=230*)
(14 * 3 + 3 * 4  =  54)
(****************************************************************************************)
(****************************************************************************************)
(*******Flat 3-qubit Ripple Full Adder************)
(****************************************************************************************)
let flat_ripple_adder = time prove(
`!(ten:qop^N->(real^N->complex)-> (real^N->complex))
(LH:sm->(real->complex)) (LV:sm->(real->complex))
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
10 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\     
CNOT2_GATE (a1,b1,a10,b10,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (c0,d0,c01,d01,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (b10,c01,b11,c02,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE (a10,b11,b12,a11,ten,LH,LV,m_modes_pro) /\
SWAP_GATE (c02,d01,d02,s1,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE (b12,a11,d02,d03,c1,f0,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d03,c1,c11,d04,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d1,c11,c12,d11,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (a2,b2,a20,b20,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (c12,d11,c13,d12,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (b20,c13,b21,c14,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE (a20,b21,b22,a21,ten,LH,LV,m_modes_pro) /\
SWAP_GATE (c14,d12,d13,s2,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE (b22,a21,d13,d14,c2,f1,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d14,c2,c21,d15,ten,LH,LV,m_modes_pro) /\
SWAP_GATE(d2,c21,c22,d21,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (a3,b3,a30,b30,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (c22,d21,c23,d22,ten,LH,LV,m_modes_pro) /\
CNOT2_GATE (b30,c23,b31,c24,ten,LH,LV,m_modes_pro) /\ 
SWAP_GATE (a30,b31,b32,a31,ten,LH,LV,m_modes_pro) /\
SWAP_GATE (c24,d22,d23,s3,ten,LH,LV,m_modes_pro) /\
FREDKIN1_GATE (b32,a31,d23,d24,c3,f2,ten,LH,LV,m_modes_pro)  ==>
tensor 10 ((lambda i. if i = 1 then LH (a3) else if i = 2 then  LH (b3)
else if i = 3 then  LH (d2) else if i = 4 then  LV (a2) 
else if i = 5 then  LV (b2) else if i = 6 then  LH (d1)
else if i = 7 then  LV (a1) else if i = 8 then  LH (b1) 
else if i = 9 then  LH (c0) else LH (d0)):bqs^N) = 
Cx (&1 / &324518553658426726783156020576256) %
tensor 10 (lambda i. if i = 1 then LH d24 else if i = 2 then LH c3
else if i = 3 then LV f2 else if i = 4 then LV s3
else if i = 5 then LH d15 else if i = 6 then LH f1
else if i = 7 then LH s2 else if i = 8 then LV d04
else if i = 9 then LV f0 else LV s1)`,
quantum_tac (matrix_procedure [] ((gate_matrix "test12.txt" [] [] 0)) 
(extract_port [] "(a3,0,b3,0,d2,0,a2,1,b2,1,d1,0,a1,1,b1,0,c0,0,d0,0)" 0 0) 4) 10 0 0 []);;
CPU time (user): 4551.165118
(10 * 3 + 3 * 5  + 9= 45 + 9 = 54)
(* 18 * 3 +  10 * 2 + 12 * 10  + 9 * 4= 54+20+120+36=230*)


let five_qubits_ripple_adder = time prove(`!(ten:qop^N->(real^N->complex)-> (real^N->complex)) 
(LH:sm->(real->complex)) (LV:sm->(real->complex))  
(m_modes_pro:(real^N->complex)->(real^N->complex)->(real^N->complex)).
8 <= dimindex (:N) /\ 16 <= dimindex (:N) 
/\ is_tensor_pro m_modes_pro /\ is_tensor ten /\
CIRCUIT1(ca0,cin,(y0),x0,(ca01:sm),(cin1:sm),(y01:sm),(x01:sm),ten,LH,LV,m_modes_pro) /\
CIRCUIT3((ca1),(y1),x1,ca01,ca11,y11,x11,ca02,ten,LH,LV,m_modes_pro) /\
CIRCUIT3((ca2),(y2),x2,ca11,ca21,y21,x21,ca12,ten,LH,LV,m_modes_pro) /\
CIRCUIT3((ca3),(y3),x3,ca21,ca31,y31,x31,ca22,ten,LH,LV,m_modes_pro) /\
CIRCUIT3((ca4),(y4),(x4),ca31,ca41,y41,x41,ca32,ten,LH,LV,m_modes_pro)   ==>
tensor 16 ((lambda i. if i = 1 then LH (ca4) else
if i = 2 then LV (y4) else if i = 3 then  LH (x4) else 
if i = 4 then LH (ca3) else if i = 5 then  LV (y3) else
if i = 6 then LV (x3) else if i = 7 then  LH (ca2) else 
if i = 8 then LH (y2) else if i = 9 then  LV (x2) else
if i = 10 then LH (ca1) else if i = 11 then  LH (y1) else 
if i = 12 then LH (x1) else if i = 13 then  LH (ca0) else
if i = 14 then LV (cin) else if i = 15 then  LH (y0) else LH (x0)):bqs^N) = 
Cx (&1 / &133499189745056880149688856635597007162669032647290798121690100488888732861290034376435130433536) %
tensor 16 (lambda i. if i = 1 then LV ca41 else if i = 2 then LV y41 else if i = 3 then LH x41
else if i = 4 then LH ca32 else if i = 5 then LH y31 else if i = 6 then LV x31 else if i = 7 then LH ca22
else if i = 8 then LV y21 else if i = 9 then LV x21 else if i = 10 then LV ca12 else if i = 11 then LH y11
else if i = 12 then LH x11 else if i = 13 then LH ca02 else if i = 14 then LV cin1 else
if i = 15 then LH y01 else LH x01)`,
quantum_tac (matrix_procedure [] (gate_matrix "test21.txt" [] [("CIRCUIT3",4);("CIRCUIT1",4)] 0) 
(extract_port [] "(ca4,1,y4,0,x4,0,ca3,1,y3,0,x3,1,ca2,1,y2,0,x2,0,ca1,1,y1,0,x1,0,ca0,1,cin,0,y0,0,x0,1)" 0 0) 4) 16 
0 0 [("CIRCUIT3",circuit3_tac);("CIRCUIT1",circuit1_tac)]);;

(* (144 - 4*2) * 4 +  10 * 2 + (96 - 4*2) = 544+20+88=652*)
(34 * 4 + 22 = 136 + 22 = 158)

CPU time (user): 33523.306683