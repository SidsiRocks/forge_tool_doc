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
