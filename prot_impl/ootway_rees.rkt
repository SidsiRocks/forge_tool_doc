#lang forge/domains/crypto
(defprotocol ootway_rees basic 
    (defrole A 
        (vars (a b s name) (m na nb text) (k_ab skey))
        (trace
            (send (cat m a b (enc na m a b (ltk a s))))
            (recv (cat m (enc na k_ab (ltk a s))))
        )
    )
    (defrole B 
        (vars (a b s name) (m na nb text) (k_ab skey))
        (trace
            (recv (cat m a b (enc na m a b (ltk a s))))
            (send (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))
            (recv (cat m (enc na k_ab (ltk a s)) (enc nb k_ab (ltk b s))))
            (send (cat m (enc na k_ab (ltk a s))))
        )
    )
    (defrole S 
        (vars (a b s name) (m na nb text) (k_ab skey))
        (trace
            (recv (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))
            (send (cat m (enc na k_ab (ltk a s)) (enc nb k_ab (ltk b s))))
        )
    )
)
(defskeleton ootway_rees
    (vars (a b s name) (m na nb text) (k_ab skey))
    (defstrand S 2 (a a) (b b) (s s) (m m) (na na) (nb nb) (k_ab k_ab))
    (non-orig (ltk a s) (ltk b s))
    (uniq-orig m na nb)    
)