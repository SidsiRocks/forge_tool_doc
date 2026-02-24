#lang forge/domains/crypto

(defprotocol splice basic
    (defrole init
        (vars (s c as name) )))