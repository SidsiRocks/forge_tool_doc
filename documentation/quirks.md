# Introduction 
This quirks file consists of a list of doubts which need clarification.
(Have included the files refrenced in the questions below for reference)

# two_nonce.frg (Needham Schroeder Implementation)
```frg
#lang forge 

open "two_nonce.rkt"

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0
    
    two_nonce_resp.agent != two_nonce_init.agent
    //should not need restriction on a and b this time?

    //this may prevent attack have to check
    two_nonce_init.agent != AttackerStrand.agent
    two_nonce_resp.agent != AttackerStrand.agent

    //prevents responder from sending same nonce again
    two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2
    //prevents attacker from sending duplicate n1,n2 in a run of protocol
    two_nonce_init.two_nonce_init_n1 != two_nonce_init.two_nonce_init_n2
    
    //attacker_learns[AttackerStrand,two_nonce_resp.two_nonce_resp_n2]
    
    //finding attack where init beleives it is talking to resp 
    //but attacker knows the nonce
    two_nonce_init.two_nonce_init_b = two_nonce_resp.agent
    corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
    //same nonce problem seems to be resolved
    //have to deal with initiator trying tot talk to attacker, may want to change that
    //when planning to detect an attack
}for 
    exactly 6 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 6 text,exactly 10 Ciphertext,
    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
    1 Int
for {next is linear}
```
# two_nonce.rkt (Needham Schroeder Implementation)
```rkt
#lang forge/domains/crypto
;; How did this work outside of the directory
;; is forge implementation in PATH have to see
(defprotocol two_nonce basic
    (defrole init
        (vars (a b name) (n1 n2 text))
        (trace
            (send (enc n1 (pubk b)))
            (recv (enc n1 n2 (pubk a)))
            (send (enc n2 (pubk b)))
        )    
    )
    (defrole resp 
        (vars (a b name) (n1 n2 text))
        (trace
            (recv (enc n1 (pubk b)))
            (send (enc n1 n2 (pubk a)))
            (recv (enc n2 (pubk b)))
        )
    )
)

(defskeleton two_nonce
    (vars (a b name) (n1 n2 text))
    (defstrand init 3 (a a) (b b) (n1 n1) (n2 n2))
    (non-orig (privk a) (privk b))
    (uniq-orig n1 n2)    
)
```

- Why is two_nonce_init.agent != AttackerStrand.agent needed (present in the two_nonce.frg file above) shouldn't that constraint be applied by default?
- Why is two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2 needed?
(Also present in the two_nonce.frg file before). I added this to the file after seeing that in some of the runs it generated an example where both nonces in the protocol were identical. Shouldn't it enforce the nonces being different by default?
- Why visualization doesn't work properly when exactly is not included in constraints for text and Ciphertext. (In this case the text/ciphertext are both represented as different message types)
- Exact length of attack should be known in advance to find attack, is there a way in forge to easily iterate over different possible lengths of the attack?
- option run_sterling "../vis/crypto_viz.js" Doesn't seem to work, it doesn't open up the visualizer with the script anymore is there any alternative method to add that script?
- Is there a constraint saying two agents owning LTK cannot be the same, couldn't find anything for that exactly
