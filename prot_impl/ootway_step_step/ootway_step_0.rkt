#lang forge/domains/crypto
(defprotocol ootway_rees basic 
    (defrole A 
        (vars (a b name) (m na text))
        (trace
            (send (cat m a b (enc na m a b (ltk a b))))
            (recv (cat m a b (enc na m a b (ltk a b)))) 
        )
    )
    (defrole B 
        (vars (a b name) (m na text))
        (trace
            (recv (cat m a b (enc na m a b (ltk a b))))
            (send (cat m a b (enc na m a b (ltk a b)))) 
        )
    )
)
(defskeleton ootway_rees
    (vars (a b name) (m na text))
    (defstrand A 2 (a a) (b b) (m m) (na na))
    (uniq-orig m)    
)