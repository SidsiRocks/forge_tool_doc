#lang forge/domains/crypto
(defprotocol ootway_rees basic
  (defrole A
    (vars (a b s name) (m na nb text) (kab skey))
    (trace
     (send (cat m a b (enc na m a b (ltk a s))))
     (recv (cat m (enc na kab (ltk a s))))
    )
    (constraint
      (non-orig (ltk a s))
      ;; (uniq-orig na)
      ;; (uniq-orig m)
    )
  )

  (defrole B
    (vars (a b s name) (m nb text) (kab skey) (first_a_s_mesg second_a_s_mesg mesg))
    (trace
     (recv (cat m a b first_a_s_mesg))
     (send (cat m a b first_a_s_mesg (enc nb m a b (ltk b s))))
     (recv (cat m second_a_s_mesg (enc nb kab (ltk b s))))
     (send (cat m second_a_s_mesg))
    )
    (constraint
      (non-orig (ltk b s))
      ;; (uniq-orig nb)
    )
  )

  (defrole S
    (vars (a b s name) (m na nb text) (kab skey))
    (trace
     (recv (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))
     (send (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))
    )
    (constraint
      (non-orig (ltk a s))
      (non-orig (ltk b s))
      ;; (uniq-orig kab)
    )
  )
)

(defaltinstance honest_run_bounds
  (Timeslot 8)
  (mesg 41)
  (Key 7) (name 4) (Ciphertext 8) (text 6) (tuple 16) (Hashed 0)
  (akey 0) (skey 7) (Attacker 1)
  (PublicKey 0) (PrivateKey 0)
  (enc-depth 1) (tuple-length 5)
  (A 1) (B 1) (S 1)
  (have-ltks)
)

(defskeleton honest_run_with_1_ABS
  (vars (a b s name) (m na nb text) (kab skey) (A role_A) (B role_B) (S role_S))
  (defstrand A 2 (a a) (b b) (s s))
  (defstrand B 4 (a a) (b b) (s s))
  (defstrand S 4 (a a) (b b) (s s))

  (deftrace honest_run
    (send-from A (cat m a b (enc na m a b (ltk a s))))
    (recv-by B (cat m a b (enc na m a b (ltk a s))))

    (send-from B (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))
    (recv-by S (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))

    (send-from S (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))
    (recv-by B (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))

    (send-from B (cat m (enc na kab (ltk a s))))
    (recv-by A (cat m (enc na kab (ltk a s))))
  )
)
