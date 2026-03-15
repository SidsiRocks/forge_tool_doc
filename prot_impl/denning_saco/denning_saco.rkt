#lang forge/domains/crypto

(defprotocol denning_saco basic
    (defrole init
        (vars (a b s name) (Kas Kbs Kab skey) (T text)))
        (trace
            (send (cat a b))
            (recv (enc (cat b Kab T (enc (cat Kab a T) (Kbs))) (Kas)))
            (send (enc (cat Kab a T) (Kbs)))
        )
        (constraint
            (non-orig (privk a))
            (non-orig Kas)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole server
        (vars (a b s name) (Kas Kbs Kab skey) (T text)))
        (trace
            (recv (cat a b))
            (send (enc (cat b Kab T (enc (cat Kab a T) (Kbs))) (Kas)))
        )
        (constraint
            (non-orig (privk s))
            (non-orig Kas)
            (non-orig Kbs)
            (uniq-orig Kab)
            (uniq-orig T)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )

    (defrole resp
        (vars (a b s name) (Kas Kbs Kab skey) (T text)))
        (trace
            (recv (enc (cat Kab a T) (Kbs)))
        )
        (constraint
            (non-orig (privk b))
            (non-orig Kbs)
            (not-eq a b) (not-eq a s) (not-eq b s)
        )
    )
)

(defskeleton denning_saco
    (vars (a b s name) (Kas Kbs Kab skey) (T text)))
    (defstrand init 3 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T))
    (defstrand server 2 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T))
    (defstrand resp 1 (a a) (b b) (s s) (Kas Kas) (Kbs Kbs) (Kab Kab) (T T))
)
