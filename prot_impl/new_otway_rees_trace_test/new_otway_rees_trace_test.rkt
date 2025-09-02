#lang forge/domains/crypto
(defprotocol ootway_rees basic
  (defrole A
    (vars (a b s name) (m na text) (kab skey))
    (trace
     (send (cat m a b (enc na m a b (ltk a s))))
     (recv (cat m (enc na kab (ltk a s))))
     )
    )
  (defrole B
    (vars (a b s name) (m nb text) (kab skey) (first_a_s_mesg second_a_s_mesg mesg))
    (trace
     (recv (cat m a b first_a_s_mesg))
     (send (cat m a b first_a_s_mesg  (enc nb m a b (ltk b s))  )   )
     (recv (cat m second_a_s_mesg (enc nb kab (ltk b s))))
     (send (cat m second_a_s_mesg))
     )
    )
  (defrole S
    (vars (a b s name) (m na nb text) (kab skey))
    (trace
     (recv (cat m a b (enc na m a b (ltk a s))  (enc nb m a b (ltk b s))  )   )
     (send (cat m (enc na kab (ltk a s)) (enc nb kab (ltk b s))))
     )
    )
)
(defskeleton ootway_rees
  (vars (a b s name) (m na nb text) (kab skey) (A role_A) (B role_B) (S role_S))
  (defstrand A 2 (a a) (b b) (s s) (m m) (na na) (kab kab))
  (defstrand B 2 (nb nb))
  (not-eq a b) (not-eq a s) (not-eq b s)
  (not-eq m na) (not-eq m nb) (not-eq na nb)
  ;; (deftrace honest_run
  ;;   (send-from A (cat m a b (enc na m a b (ltk a s))))
  ;;   (recv-by B (cat m a b (enc na m a b (ltk a s))))

  ;;   (send-from B (cat m a b (enc na m a b (ltk a s)) (enc na m a b (ltk b s))))
  ;;   (recv-by S (cat m a b (enc na m a b (ltk a s)) (enc na m a b (ltk b s))))

  ;;   (send-from S (cat m (enc na kab (ltk a s)) (enc na kab (ltk b s))))
  ;;   (recv-by B (cat m (enc na kab (ltk a s)) (enc na kab (ltk b s))))

  ;;   (send-from B (cat m (enc na kab (ltk a s))))
  ;;   (recv-by A (cat m (enc na kab (ltk a s))))
  ;; )
  (non-orig (ltk a s) (ltk b s))
  ;; add uniq-orig nb here after adding another strand declaration
  ;; previous code was incorrect not adding immediately incase it makes it
  ;; unsat
  (uniq-orig m na kab nb)
)
