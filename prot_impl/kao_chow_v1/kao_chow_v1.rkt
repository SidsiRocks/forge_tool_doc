#lang forge/domains/crypto

(defprotocol kao_chow_v1 basic
    (defrole init
        (vars (a b s name) (Kab Kbs Kas skey) (Na Nb text))
        (trace
            (send (cat a b Na))
            (recv (cat (enc (cat a b Na Kab) Kas) (enc Na Kab) Nb))
            (send (enc Nb Kab))
        )
        (constraint
            (non-orig (privk a))
            (non-orig Kas)
            (not-eq a b) (not-eq a s) (not-eq b s)
            (uniq-orig Na) 
            (fresh-gen Na)
        )
    )

    (defrole server
        (vars (a b s name) (Kab Kbs Kas skey) (Na Nb text))
        (trace 
            (recv (cat a b Na))
            (send (cat (enc (cat a b Na Kab) Kas) (enc (cat a b Na Kab) Kbs)))
        )
        (constraint
            (non-orig (privk s))
            (non-orig Kas)
            (non-orig Kbs)
            (uniq-orig Kab)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Kab Kbs Kas skey) (Na Nb text))
        (trace
            (recv (cat (enc (cat a b Na Kab) Kas) (enc (cat a b Na Kab) Kbs)))
            (send (cat (enc (cat a b Na Kab) Kas) (enc Na Kab) Nb))
            (recv (enc Nb Kab))
        )
        (constraint
            (uniq-orig Nb)
            (fresh-gen Nb)
            (non-orig (privk b))
            (non-orig Kbs)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton kao_chow_v1
    (vars (a b s name) (Kab Kbs Kas skey) (Na Nb text))
    (defstrand init 3 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand resp 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Na Na) (Nb Nb))
)