#lang forge/domains/crypto

(defprotocol splice basic
    (defrole client
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace 
            (send (cat c s N1))
            (recv (cat as (enc as c N1 (pubk s) (privk as))))
            (send (cat c s (enc c T L (enc N2 (pubk s)) (privk c))))
            (recv (cat s c (enc s (hash N2) (pubk c))))
        )
        (constraint
            (non-orig (privk c))
            (uniq-orig N1 N2 T L) (fresh-gen N1 N2 T L)
            (not-eq c s) (not-eq as s) (not-eq c as)
            (not-eq T L) (not-eq T N1) (not-eq T N2) (not-eq T N3)
            (not-eq L N1) (not-eq L N2) (not-eq L N3)
        )
    )

    (defrole authority
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace 
            (recv (cat c s N1))
            (send (cat as (enc as c N1 (pubk s) (privk as))))
            (recv (cat s c N3))
            (send (cat as (enc as s N3 (pubk c) (privk as))))
        )
        (constraint
            (non-orig (privk as))
            (not-eq c s) (not-eq as s) (not-eq c as)
            (not-eq T L) (not-eq T N1) (not-eq T N2) (not-eq T N3)
            (not-eq L N1) (not-eq L N2) (not-eq L N3)
        )
    )

    (defrole server
        (vars (c s as name) (N1 N2 N3 T L text))
        (trace
            (recv (cat c s (enc c T L (enc N2 (pubk s)) (privk c))))
            (send (cat s c N3))
            (recv (cat as (enc as s N3 (pubk c) (privk as))))
            (send (cat s c (enc s (hash N2) (pubk c))))
        )
        (constraint
            (non-orig (privk s))
            (uniq-orig N3) (fresh-gen N3)
            (not-eq c s) (not-eq as s) (not-eq c as)
            (not-eq T L) (not-eq T N1) (not-eq T N2) (not-eq T N3)
            (not-eq L N1) (not-eq L N2) (not-eq L N3)
        )
    )
)


(defskeleton splice
    (vars (c s as name) (N1 N2 N3 T L text))
    (defstrand client 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand authority 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand server 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
)

(defskeleton attack1
    (vars (c s as name) (N1 N2 N3 T L text) (authority_strand role_authority) (server_strand role_server))
    ; (defstrand client 4 (c c) (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand authority 4 (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand server 4 (s s) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))

    ; (deftrace attack1
    ;     (recv-by authority_strand (cat Attacker s N1))
    ;     (send-from authority_strand (cat as (enc as Attacker N1 (pubk s) (privk as))))
    ;     (recv-by server_strand (cat c s (enc c T L (enc N2 (pubk s)) (privk Attacker))))
    ;     (send-from server_strand (cat s c N3))
    ;     (recv-by authority_strand (cat s Attacker N3))
    ;     (send-from authority_strand (cat as (enc as s N3 (pubk Attacker) (privk as))))
    ;     (recv-by server_strand (cat as (enc as s N3 (pubk Attacker) (privk as))))
    ;     (send-from server_strand (cat s c (enc s (hash N2) (pubk Attacker))))
    ; )
)

(defskeleton attack2 
    (vars (c s as name) (N1 N2 N3 T L text))
    (defstrand client 4 (c c) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
    (defstrand authority 4 (c c) (as as) (N1 N1) (N2 N2) (N3 N3) (T T) (L L))
)

(defaltinstance honest_run_bounds
    (Timeslot 12)
    (mesg 34)
    (Key 8) (name 4) (Ciphertext 5) (text 5) (tuple 11) (Hashed 1)
    (skey 0) (akey 8)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (client 1) (authority 1) (server 1) (Attacker 1)
)

(defaltinstance attack1_bounds
    (Timeslot 8)
    (mesg 35)
    (Key 8) (name 4) (Ciphertext 5) (text 5) (tuple 12) (Hashed 1)
    (skey 0) (akey 8)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (client 1) (authority 1) (server 1) (Attacker 1)
)

(defaltinstance attack2_bounds 
    (Timeslot 9)
    (mesg 35)
    (Key 8) (name 4) (Ciphertext 5) (text 5) (tuple 12) (Hashed 1)
    (skey 0) (akey 8)
    (PublicKey 4) (PrivateKey 4)
    (enc-depth 2) (tuple-length 4)
    (client 1) (authority 1) (server 1) (Attacker 1)
)