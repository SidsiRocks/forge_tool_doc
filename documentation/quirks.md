# Introduction 
This quirks file consists of a list of doubts which need clarification.
- Why two_nonce_init.agent != AttackerStrand.agent needed (makes sense in some way may want to investigate scenario where attacker is one of the agents)
- Why two_nonce_resp.two_nonce_resp_n1 != two_nonce_resp.two_nonce_resp_n2, shouldn't nonces already be different (sent by attacker though so may not have to generate fresh nonce when sending)
- Why constraints need to be refered to with exaclty, and why sometimes int bitwidth needs to be increased and sometimes not. Why visualization doesn't work properly when exactly is not included in constraints for text and CipherText.