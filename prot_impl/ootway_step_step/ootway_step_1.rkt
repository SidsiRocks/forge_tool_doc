#lang forge/domains/crypto
(defprotocol ootway_rees basic 
    (defrole A 
        (vars (a b name) (m na text) (kab skey))
        (trace
            (send (cat m a b (enc na m a b (ltk a b))))
            (recv (cat m (enc na kab (ltk a b))))
        )
    )
    (defrole B 
        (vars (a b name) (m na text) (kab skey))
        (trace
            (recv (cat m a b (enc na m a b (ltk a b))))
            (send (cat m (enc na kab (ltk a b))))
        )
    )
)
(defskeleton ootway_rees
    (vars (a b name) (m na text) (kab skey))
    (defstrand B 2 (a a) (b b) (m m) (na na) (kab kab))
    (non-orig (ltk a b))
    ; may add (ltk a b) to uniq-orig
    (uniq-orig m na kab)
)