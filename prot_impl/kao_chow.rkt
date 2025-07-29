#lang forge/domains/crypto
;; since tuples are not ordered here could lead to incorrect
;; executions if a and b or na and kab are exchanged in some way
;; TODO this file is probably not following kao chow specification
;; correctly delete this file or implement specification correctly
(defprotocol kao_chow basic 
    (defrole A 
        (vars (a b s name) (na nb text))
        (trace
            (send (cat a b na))
            (recv (cat 
                    (enc (a b na (ltk a b)) (ltk a s)) 
                    (enc na (ltk a b)) 
                    nb)
                  )
            (send (enc nb (ltk a b)))
        )
    )
    (defrole B 
        (vars (b a s name) (na nb text))  
        (trace
            (recv (cat 
                    (enc (a b na (ltk a b)) (ltk a s)) 
                    (enc (a b na (ltk a b)) (ltk b s))))
            (send (cat 
                    (enc (a b na (ltk a b)) (ltk a s)) 
                    (enc na (ltk a b)) 
                    nb)
            )
            (recv (enc nb (ltk a b)))
        )
    )  
    (defrole S 
        (vars (s a b name) (na nb text))
        (trace
            (recv (cat a b na))
            (send (cat 
                    (enc (a b na (ltk a b)) (ltk a s)) 
                    (enc (a b na (ltk a b)) (ltk b s))))
        )
    )
)

(defskeleton kao_chow
    (vars (a b s name) (na nb text))
    (defstrand A 3 (a a) (b b) (s s) (na na) (nb nb))
    (non-orig (ltk a b) (ltk a s) (ltk b s))
    (uniq-orig na nb)
(comment "A point of view"))
