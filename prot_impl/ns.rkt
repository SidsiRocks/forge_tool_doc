#lang forge/domains/crypto

(defprotocol ns basic
    (defrole init
        (vars (a b name ) (n1 n2 text ) )
        (trace
            (send (enc n1 (pubk b ) ) )
            (recv (enc (cat n1 n2) (pubk a ) ) )
            (send (enc n2 (pubk b ) ) ) ) )
    (defrole resp
        (vars (b a name ) (n2 n1 text ) )
        (trace
            (recv (enc n1 (pubk b ) ) )
            (send (enc (cat n1 n2) (pubk a ) ) )
            (recv (enc n2 (pubk b ) ) ) ) )
            (comment " Needham - Schroeder ") )
(defskeleton ns
    (vars (a b name) (n1 n2 text) )
    (defstrand resp 3 (a a) (b b) (n2 n2) )
    (non-orig (privk a) (privk b) )
    (uniq-orig n2 n1)
(comment " Responder point - of - view ") )