#lang forge/domains/crypto

(defprotocol splice basic
    (defrole client
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace 
            (send (cat c s N1))
            (recv (cat as (enc (cat as c N1 (pubk s)) (privk as))))
            (send (cat c s (enc (cat c T L (enc N2 (pubk s))) (privk c))))
            (recv (cat s c (enc (cat s (hash N2)) (pubk c))))
        )
        (constraint
            (non-orig (privk c))
            (uniq-orig N1) (fresh-gen N1)
            (uniq-orig N2) (fresh-gen N2)
            (uniq-orig T) (fresh-gen T)
            (uniq-orig L) (fresh-gen L)
            (not-eq c s) (not-eq as s) (not-eq c as)
        )
    )

    (defrole authority
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace 
            (recv (cat c s N1))
            (send (cat as (enc (cat as c N1 (pubk s)) (privk as))))
            (recv (cat s c N3))
            (send (cat as (enc (cat as s N3 (pubk c)) (privk as))))
        )
        (constraint
            (non-orig (privk as))
            (not-eq c s) (not-eq as s) (not-eq c as)
        )
    )

    (defrole server
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace
            (recv (cat c s (enc (cat c T L (enc N2 (pubk s))) (privk c))))
            (send (cat s c N3))
            (recv (cat as (enc (cat as s N3 (pubk c)) (privk as))))
            (send (cat s c (enc (cat s (hash N2)) (pubk c))))
        )
        (constraint
            (non-orig (privk s))
            (uniq-orig N3) (fresh-gen N3)
            (not-eq c s) (not-eq as s) (not-eq c as)
        )
    )
)


(defskeleton splice
    (vars (c s as name) (N1 N2 N3 T L text))
    (defstrand client 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand authority 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand server 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
)