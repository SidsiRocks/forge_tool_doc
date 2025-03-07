(defskeleton ootway_rees
    (vars (a b s name) (m na nb text) (kab skey))
    (defstrand S 2 (a a) (b b) (s s) (m m) (na na) (nb nb) (kab kab))
    (non-orig (ltk a s) (ltk b s))
    ; may need to add ltk's also here found an example where another person was able to generate the long term key
    (uniq-orig m na nb kab)
    ; (try ltk a s)
)