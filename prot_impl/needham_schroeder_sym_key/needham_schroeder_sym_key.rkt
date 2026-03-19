#lang forge/domains/crypto

(defprotocol needham_schroeder_sym_key basic
    (defrole init 
        (vars (a b s name) (Na Nb Text) (Kab Kas Kbs skey))
        (trace 
            (send (cat a b Na))
            (recv (enc (cat Na b Kab (enc (cat Kab a) Kbs)) Kas))
            (send (enc (cat Kab a) Kbs))
            (recv (enc Nb Kab))
            (send (enc (hash Nb) Kab))
        )
        (constraint
            (non-orig (privk a))
            (non-orig Kas)
            (non-orig Na) (fresh-gen Na)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server 
        (vars (a b s name) (Na Nb Text) (Kab Kas Kbs skey))
        (trace
            (recv (cat a b Na))
            (send (enc (cat Na b Kab (enc (cat Kab a) Kbs)) Kas))
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
        (vars (a b s name) (Na Nb Text) (Kab Kas Kbs skey))
        (trace
            (recv (enc (cat Kab a) Kbs))
            (send (enc Nb Kab))
            (recv (enc (hash Nb) Kab))
        )
        (constraint
            (uniq-orig Nb) (fresh-gen Nb)
            (non-orig (privk b))
            (non-orig Kbs)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton needham_schroeder_sym_key
    (vars (a b s name) (Na Nb Text) (Kab Kas Kbs skey))
    (defstrand init 5 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Na Na) (Nb Nb))
    (defstrand server 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (Na Na))
    (defstrand resp 3 (a a) (b b) (s s) (Kbs Kbs) (Kab Kab) (Nb Nb))
)