#lang forge/domains/crypto

(defprotocol nspk basic 
    (defrole A
        (vars (a b s name) (na nb text))
        (trace 
; should always send both a and b but one run of protocol seems to show only 1 is sent
; could cause problems if a and b are switched here since no ordering in tuple?
            (send (cat a b))
            (recv (enc (pubk b) b (privk s)))
            (send (enc na a (pubk b)))
            (recv (enc na nb (pubk a))) 
            (send (enc nb (pubk b)))
        ))
    (defrole B
        (vars (b a s name) (na nb text))
        (trace
            (recv (enc na a (pubk b)))
            (send (cat b a)) ;confirm this should be b a
            (recv (enc (pubk a) a (privk s)))
            (send (enc na nb (pubk a)))
            (recv (enc nb (pubk b)))
        ))
    (defrole S
        (vars (s a b name) (na nb text))
        (trace
            (recv (cat a b))
            (send (enc (pubk b) b (privk s)))
            (recv (cat b a))
            (send (enc (pubk a) a (privk s)))
        )))

(defskeleton nspk
    (vars (a b s name) (na nb text))
    (defstrand B 5 (a a) (b b) (s s) (na na) (nb nb))
    (non-orig (privk a) (privk b) (privk s))
    (uniq-orig na nb)
(comment "B point of view"))