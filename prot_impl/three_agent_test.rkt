#lang forge/domains/crypto
(defprotocol three_agent basic
    (defrole A 
        (vars (a b s name) (n1 text))
        (trace
            (send s)
            (recv a)
        )
    )
    (defrole S 
        (vars (a b s name) (n1 text))
        (trace
            (recv s)
            (send b)
        )
    )
    (defrole B
        (vars (a b s name) (n1 text))
        (trace
            (recv b)
            (send a)
        )    
    )
)
;(defskeleton three_agent
;    (vars (a b s name) (n1 text))
;    (defstrand S 2 (a a) (b b) (s s) (n1 n1))
;    (non-orig (privk a) (privk b) (privk s))
;    (uniq-orig n1)
;)