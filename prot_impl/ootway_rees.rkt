#lang forge/domains/crypto
(defprotocol ootway_rees basic 
    (defrole A 
        (vars (a b s name) (m na nb text) (kab skey))
        (trace
            (send (cat m a b (enc na m a b (ltk a s)))) 
            (recv (cat m (enc na kab (ltk a s))))
        )
    )
    (defrole B 
        (vars (a b s name) (m na nb text) (kab skey))
        (trace
            (recv (cat m a b (enc na m a b (ltk a s))))
            (send (cat m a b (enc na m a b (ltk a s))  (enc nb m a b (ltk b s))  )   )
            (recv (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))
            (send (cat m (enc na kab (ltk a s))))
        )
    )
    (defrole S 
        (vars (a b s name) (m na nb text) (kab skey))
        (trace
            (recv (cat m a b (enc na m a b (ltk a s))  (enc nb m a b (ltk b s))  )   )
            (send (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))
        )
    )
)
(defskeleton ootway_rees
    (vars (a b s name) (m na nb text) (kab skey))
    (defstrand S 2 (a a) (b b) (s s) (m m) (na na) (nb nb) (kab kab))
    (non-orig (ltk a s) (ltk b s))
    ; may need to add ltk's also here found an example where another person was able to generate the long term key
    (uniq-orig m na nb kab)
    ; (try ltk a s)
)