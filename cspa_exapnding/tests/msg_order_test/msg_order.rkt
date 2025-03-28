#lang forge/domains/crypto
(defprotocol msg_order basic
    (defrole A 
        (vars (n1 n2 n3 text) (b name))
        (trace
            (send (cat n1 n2))
            (recv (cat b n3))
        )
    )
    (defrole B
        (vars (n1 n2 text) (b name))
        (trace
            (recv (cat n1 n2))
            (send (cat b n2))
        )
    ) 
)