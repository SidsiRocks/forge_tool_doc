//In this version of the file the Attacker is able to send the first term
//because of cyclic justification, 
//Attacker sends msg in TimeSlot0 to Attacker
//Because of this it is present in workspace at Timeslot0 hence 
//as Attacker is both sender and receiver it is able 
//to add the term to its learned_times property and is able to send it
//CYCLIC JUSTIFICATION
//now have to figure out why honest agent cannot send it 

//FINALY HAVE AN IDEA SEEMS LIKE AGENT CAN LEARN ANOTHER AGENTS NAME ONLY IF 
//IT RECEIVES IT BEFORE SO IT IS UNABLE TO SEND NAME0,NAME1 INITIALLY
//WE CAN CHANGE BASE KNOWN TO FIX THIS POSSIBLY

//THIS ALSO EXPLAINS THE PREVIOUS UNSAT CORE INCLUDING != Attacker as the culprit
//HAVE TO CHANGE FORGE CODE UNINSTALL AND REINSTALL THE FORGE PACKAGE

//NAME NOT KNOWN PROBLEM FIXED (MAYBE COULD HAVE REPLACED ALL NAMES WITH THEIR PUBLIC KEYS)
//DIFFERENT PROBLEM OF THE ATTACKER JUST GENERATING THE LONG TERM KEY OF THE OTHER PEOPLE
//INVOLVED(although the example i saw he generated only (ltk name1 name1) maybe can only generated duplicate ltks)
//NVM AFTER DISALLOWING DUPLICATE NAME LTKS JUST SAW THE ATTACKER GENERATE THAT (ltk name1 name2)
//CAN TRY ADDING (uniq-orig (ltk name1 name2)) as well might help, will later add constraint that cannot 
//generate ltks as well

//ADDING THAT(uniq-orig (ltk a b) (ltk b a)) MADE IT UNSAT, ADDING THE CONSTRAINT FOR NOT GEN LTK INSTEAD
//STARTED TALKING TO ATTACKER INSTEAD, WILL TEMPORARILY CHANGE TO ALREADY FIX WHAT A,B,S ARE TO SEE IF IT WORKS
//ADDING CONSTRAINTS FOR HONEST RUN MAKES IT UNSAT HAVE TO GO BACK TO STEP BY STEP PROGRESS

//PREV. CONSTRAINT FOR LTK GEN. WAS WRONG, TRYING FULL FILE WITH NEW CONSTRAINT
//WITH NEW CONSTRAINT ALMOST WORKS, ONE OF THE AGENTS SENT LTK INSTEAD OF K_AB ADDING CONSTRAINT WITH THAT

//HONEST RUN GENERATED AFTER ADDING THE ABOVE CONSTRAINT(HAVE TO CROSS CHECK)
//ADDING THIS PROGRESS TO GIT NOW
#lang forge
open "ootway_step_1.rkt"
option run_sterling "../../crypto_viz.js"
option solver MiniSatProver
option logtranslation 2
option coregranularity 1
option engine_verbosity 3
option core_minimization rce
//now the visualizer is broken in some way
pred prot_conditions{
    //ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    //ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent

    //nothing to state nonces being different 
    //only one nonce being sent currently  

    //ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
}
//the execution is almost correct with only 
//  ootway_rees_B.agent != Attacker
ootway_prot_run : run {
    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    constrain_skeleton_ootway_rees_0
}for 
    //mesg = Key + name + Ciphertext + text 
    //mesg = 2 (one ltk,one k_ab)  + 3 (2 agent 1 attacker)+ 2 (only 2 enc term)+ 2 (m,na)
    exactly 4 Timeslot,9 mesg,
    exactly 1 KeyPairs,exactly 2 Key,exactly 0 akey,exactly 2 skey, //1 key for ltk a b,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 3 name,exactly 2 text,exactly 2 Ciphertext, //4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    1 Int
for {next is linear}