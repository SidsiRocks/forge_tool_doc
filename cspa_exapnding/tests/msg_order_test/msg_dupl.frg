#lang forge 
open "msg_order.rkt"

option run_sterling "../../../crypto_viz.js"


msg_order_test: run {
    wellformed 
    exec_msg_order_A
    exec_msg_order_B

    -- testing duplicate subterms would appear separately for 
    -- sequences implementation
    msg_order_A.msg_order_A_n1 = msg_order_A.msg_order_A_n2

    msg_order_A.agent != msg_order_B.agent
    msg_order_A.agent != AttackerStrand.agent
    msg_order_B.agent != AttackerStrand.agent
    
}for 
    exactly 4 Timeslot,16 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 0 Ciphertext,
    exactly 1 msg_order_A,exactly 1 msg_order_B,
    1 Int 
for {next is linear}