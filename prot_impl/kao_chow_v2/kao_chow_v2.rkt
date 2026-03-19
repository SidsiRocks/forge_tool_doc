#lang forge/domains/crypto

(defprotocol kao_chow_v1 basic
    (defrole init
        (vars (a b s name) (Kab Kbs Kas Kt skey) (Na Nb text))
        (trace
            (send (cat a b Na))
            (recv (cat b (enc (cat a b Na Kab Kt) Kas) (enc (cat Na Kab) Kt) Nb))
            (send (enc (cat Nb Kab) Kt))
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
        (vars (a b s name) (Kab Kbs Kas Kt skey) (Na Nb text))
        (trace 
            (recv (cat a b Na))
            (send (cat (enc (cat a b Na Kab Kt) Kas) (enc (cat a b Na Kab Kt) Kbs)))
        )
        (constraint
            (non-orig (privk s))
            (non-orig Kas)
            (non-orig Kbs)
            (uniq-orig Kab)
            (uniq-orig Kt)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp 
        (vars (a b s name) (Kab Kbs Kas skey) (Na Nb text))
        (trace
            (recv (cat (enc (cat a b Na Kab Kt) Kas) (enc (cat a b Na Kab Kt) Kbs)))
            (send (cat b (enc (cat a b Na Kab Kt) Kas) (enc (cat Na Kab) Kt) Nb))
            (recv (enc (cat Nb Kab) Kt))
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
    (vars (a b s name) (Kab Kbs Kas Kt skey) (Na Nb text))
    (defstrand init 3 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Kt Kt) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Kt Kt) (Na Na) (Nb Nb))
    (defstrand resp 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Kt Kt) (Na Na) (Nb Nb))
)