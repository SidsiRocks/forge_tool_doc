# Intro
This file contains explantion of difference between base_with_seq_text.frg and base_with_seq.frg. 
base_with_seq_text.frg was created to have a message type seq which 
holds multiple message terms. This was needed to model a protocol which 
has a type flaw attack. 
See: prot_impl/type_flaw_prot_seq/
This approach has shortcomings so may remove this seq approach and instead defined a new tuple message datatype which also has nesting. This should be sufficient for modeling type flaw attack and is conceptually simpler to understand.
# Differences
## Changing sig heirachy
previous heirachy:
```
mesg
|
-------------------------------
|            |        |        |
Ciphertext   text     Key      name
                      |        |
                    --------   Attacker
                    |      |
                    akey   skey
                    |
            -----------------
            |               |            
            PrivateKey      PublicKey
```

New heirachy:
```
mesg
|
text
|
-----------
|          |
atomic     seq
|     
--------------------------------
|            |         |       |
Ciphertext   nonce     Key     name
                        |       |
                    ---------   Attacker
                    |       |
                    akey    skey
                    |
           --------------------- 
           |                   |                   
           PrivateKey          PublicKey
```
The heirachy is mostly similar, new sigs seq,atomic and nonce have been introduced.
nonce is equivalent in meaning to old text datatype, infact the text sig is now redundant. Only kept to not have to change transcription code as much.
The atomic type is only present to act as common supertype for Ciphertext,nonce,Key,name.
Each element of seq refers to a sequence of atomic terms.
## Explaining different between base_with_seq_text and base_with_seq
### sig seq code
The code for the new seq sig is
```frg
sig seq extends text {
    --remember to include constraint to ensure the components present are non empty
    components: pfunc Int -> atomic
}
```
As mentioned before seq stores a sequence of atomic terms.
### pred wellformed changes
```frg
  all s: seq | isSeqOf[s.components,atomic]
  -- OLD all m: Timeslot | m.sender not in m.receiver

  -- this should be m.sender.agent not in m.receiver.agent
  -- I don't think there is circumstance where different strand but same agent
  -- would occur, problem with allowing different strands and same agent leads
  -- to cylic justification. Can learn as the term is learnt on the reciever side
  -- because someone sent it, can send it becuase already learnt it.
  -- all m: Timeslot | m.sender not in m.receiver
  all m: Timeslot | m.sender.agent not in m.receiver.agent
```

```frg
    -- TODO
    -- if recieve something like in timeslot t_i (enc (seq (pubk a) (enc n (pubk b))) (pubk b))
    -- then first decryption happens in microticks giving us (seq (pubk a) (enc n (pubk b)))
    -- and (seq (pubk a) (enc n (pubk b))) in agent.learned_times[t_i]
    -- also learn (pubk a) and (enc n (pubk b)) in agent.learned_times[t_i]
    -- but microtick only allows supertem in (a.learned_times).(Timeslot - t.*next)
    -- so cannot decrypt (enc n (pubk b)). Most likely chaning to ^next to allow
    -- decrypting terms learnt now would cause more problems, as a temporary fix
    -- adding similar decryption logic for seq terms. This can lead to other problems
    -- down the line so have to fix this
    or
    {
      {some superterm : seq | {
      d in elems[superterm.components] and
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}}
```
The above two codeblocks have comments explaining the change
```frg
    or 
    { 
        t.receiver.agent = a and
        {some s : seq | {
            d in elems[s.components]
            s in (a.learned_times).(Timeslot - t.^next)
        }}
    }
```
```frg
    { d in seq and
      elems[d.components] in (a.learned_times).(Timeslot - t.^next) and
      {a not in t.receiver.agent}
    }
```
The two codeblocks above are for breaking down and building up seq terms respectively. To prevent cyclic justification only breakdown terms when receiver and build up terms when sender.

```frg
  -- OLD   all a: name | all d: text | lone t: Timeslot | d in (a.generated_times).t
  all a: name | all d: nonce | lone t: Timeslot | d in (a.generated_times).t
```
Since nonce now plays the role played by text we simply replace which set is being referred to here.

```frg
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  --old_plainw ould be unique so some or all doesn't
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
      let components_rel = {seq_term:seq,msg:mesg | {msg in elems[seq_term.components]}} | {
          -- OLD all d: mesg | d not in d.^(old_plain)
          all d: mesg | d not in d.^(old_plain + components_rel)
      }
  }
```
As explained by the comments whenever we add another type of mesg that contains data we have to add that here as well to ensure it is acyclic.
```frg
  -- OLD  n.generated_times.Timeslot in text+Key
  n.generated_times.Timeslot in nonce+Key
```
Like in a prior example we change text to be nonce.
```frg
/** Definition of subterms for some set of terms */
fun subterm[supers: set mesg]: set mesg {
  -- VITAL: if you add a new subterm relation, needs to be added here, too!
  -- do cross check that it actually returns the correct thing and not an empty set
  -- or something
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
      let components_rel = {seq_term:seq,msg:mesg | {msg in elems[seq_term.components]}} | {
          -- OLD     supers + supers.^(old_plain) -- union on new subterm relations inside parens
          supers + supers.^(old_plain + components_rel) -- union on new subterm relations inside parens
      }
  }
  -- TODO add something for finding subterms of seq which extends text
}
```
Here just like in the constraint which ensured that plaintext and components relations are acyclic was updateed we also have to update the subterm relation so the non-orig and uniq-orig continues to hold correctly.
