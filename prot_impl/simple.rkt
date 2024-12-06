#lang forge/domains/crypto

(defprotocol simple basic 
    (defrole init 
        ; how to enforce a is it's own name it is sending?
        (vars (a b name))
        (trace (send a) (recv b)))
    (defrole resp 
        (vars (a b name))
        (trace (recv a) (send b)))
)