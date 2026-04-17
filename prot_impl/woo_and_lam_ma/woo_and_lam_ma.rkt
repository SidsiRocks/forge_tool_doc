#lang forge/domains/crypto

(defprotocol woo_and_lam_ma basic 
    (defrole init 
        (vars (p q s name) (N1 N2 text) (Kpq skey))
        (trace 
            (send (cat p N1))
            (recv (cat q N2))
            (send (enc p q N1 N2 (ltk p s)))
            (recv (cat (enc q N1 N2 Kpq (ltk p s)) (enc N1 N2 Kpq)))
            (send (enc N2 Kpq))
        )
        (constraint 
            (non-orig (ltk p s))
            (uniq-orig N1) (fresh-gen N1)
            (not-eq p q) (not-eq p s) (not-eq q s)
        )
    )

    (defrole resp 
        (vars (p q s name) (N1 N2 text) (Kpq skey) (msg1 msg2 mesg))
        (trace 
            (recv (cat p N1))
            (send (cat q N2))
            (recv msg1)
            (send (cat msg1 (enc p q N1 N2 (ltk q s))))
            (recv (cat msg2 (enc p N1 N2 Kpq (ltk q s))))
            (send (cat msg2 (enc N1 N2 Kpq)))
            (recv (enc N2 Kpq))
        )
        (constraint 
            (non-orig (ltk q s))
            (uniq-orig N2) (fresh-gen N2)
            (not-eq p q) (not-eq p s) (not-eq q s)
        )
    )

    (defrole server 
        (vars (p q s name) (N1 N2 text) (Kpq skey))
        (trace 
            (recv (cat (enc p q N1 N2 (ltk p s)) (enc p q N1 N2 (ltk q s))))
            (send (cat (enc q N1 N2 Kpq (ltk p s)) (enc p N1 N2 Kpq (ltk q s))))
        )
        (constraint 
            (non-orig (ltk p s))
            (non-orig (ltk q s))
            (fresh-gen Kpq) (uniq-orig Kpq)
            (not-eq p q) (not-eq p s) (not-eq q s)
        )
    )
)

(defskeleton woo_and_lam_ma
    (vars (p q s name) (N1 N2 text) (Kpq skey) (init_strand role_init) (msg1 msg2 mesg) (resp_strand role_resp) (server_strand role_server))
    (defstrand init 5 (p p) (q q) (s s) (Kpq Kpq) (N1 N1) (N2 N2))
    (defstrand resp 7 (p p) (q q) (s s) (Kpq Kpq) (N1 N1) (N2 N2))
    (defstrand server 2 (p p) (q q) (s s) (Kpq Kpq) (N1 N1) (N2 N2))

    (deftrace honest_run 
        (send-from init_strand (cat p N1))
        (recv-by resp_strand (cat p N1))

        (send-from resp_strand (cat q N2))
        (recv-by init_strand (cat q N2))

        (send-from init_strand (enc p q N1 N2 (ltk p s)))
        (recv-by resp_strand msg1)

        (send-from resp_strand (cat msg1 (enc p q N1 N2 (ltk q s))))
        (recv-by server_strand (cat (enc p q N1 N2 (ltk p s)) (enc p q N1 N2 (ltk q s))))

        (send-from server_strand (cat (enc q N1 N2 Kpq (ltk p s)) (enc p N1 N2 Kpq (ltk q s))))
        (recv-by resp_strand (cat msg2 (enc p N1 N2 Kpq (ltk q s))))

        (send-from resp_strand (cat msg2 (enc N1 N2 Kpq)))
        (recv-by init_strand (cat (enc q N1 N2 Kpq (ltk p s)) (enc N1 N2 Kpq)))

        (send-from init_strand (enc N2 Kpq))
        (recv-by resp_strand (enc N2 Kpq))
    )
)

(defaltinstance honest_run_bounds 
    (Timeslot 14)
    (mesg 34)
    (Key 7) (name 4) (Ciphertext 8) (text 2) (tuple 13) (Hashed 0)
    (skey 7) (akey 0)
    (PublicKey 0) (PrivateKey 0)
    (enc-depth 1) (tuple-length 4)
    (init 1) (resp 1) (server 1) (Attacker 1)
    (have-ltks)
)