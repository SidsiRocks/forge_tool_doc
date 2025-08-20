# Intro 
This file contains the difference between the original base.frg file and the base_with_seq.frg file currently being used
# Differences
## Changing cat,enc to use sequences
### Change to signatures
```
sig Timeslot {
  -- structure of time (must be rendered linear in every run via `next is linear`)
  next: lone Timeslot,
  
  -- <=1 actual "message tuple" sent/received per timeslot
  sender: one strand,
  receiver: one strand,  
  -- OLD: data: set mesg, 
  data: pfunc Int -> mesg,
  -- relation is: Tick x Microtick x learned-mesg
  -- Only one agent per tick is receiving, so always know which agent's workspace it is
  workspace: set Timeslot -> mesg
}
```
Previously cat terms were internally represented as a set of messages in the data field. Now it is expressed as a pfunc of Int->mesg, with extra restrictions placed on it so that it represents a sequence of messages. (These restrictions added in the well formed predicate).
Similarly for Ciphertexts signature,
```
sig Ciphertext extends mesg {
   -- encrypted with this key
   encryptionKey: one Key,
   -- result in concating plaintexts
   --OLD: plaintext: set mesg
   plaintext: pfunc Int -> mesg
}
```
Here plaintext was used to denote a set of terms in this encrypted term, we changed this to pfunc Int -> mesg exactly like the change made to data field in Timeslot signature.
### Changes to predicates
For the wellformed predicate the following changes were made
```
pred wellformed{
    all m: Timeslot | isSeqOf[m.data,mesg]
    all t: Ciphertext | isSeqOf[t.plaintext,mesg]
    
    ...
    
    -- OLD: all m: Timeslot | some m.data
    all m: Timeslot | some elems[m.data]
    
    ...
    
    -- OLD: {d in t.data and no microt.~next}
    {d in elems[t.data] and no microt.~next}
    
    ...
    
    -- OLD: d in superterm.plaintext and     
    d in elems[superterm.plaintext]     
    
    ...

    -- OLD: d.plaintext in (a.learned_times).(Timeslot - t.^next)
    elems[d.plaintext] in (a.learned_times).(Timeslot - t.^next)

    ...

    -- OLD: all m: Timeslot | m.data in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
    all m: Timeslot | elems[m.data] in (((m.sender).agent).learned_times).(Timeslot - m.^next)

    ...

    -- OLD: all d: mesg | d not in d.^(plaintext)
    let old_plain = {cipher: Ciphertext,msg:mesg |     {msg in elems[cipher.plaintext]}} | {
     all d: mesg | d not in d.^(old_plain)
   }

    --OLD all c: Ciphertext | some elems[c.plaintext]
    all c: Ciphertext | some c.plaintext
    
}
```

```
pred originates[s:strand,d:mesg]{
    ...
    --OLD: d in subterm[m.data] -- d is a sub-term of m     
    d in subterm[elems[m.data]] -- d is a sub-term of m     
    --OLD: {d not in subterm[elems[m2.data]]}
    {d not in subterm[m2.data]}
}
```

Most of these changes involve applying elems function to the old field. The elem function when apllied to a sequence returns the set of elements of the sequence. Applying elems to our new fields would give a representation equivalent to the old field.
One change however is needed when we are expressing that the plaintext relation is acylic.
```
-- OLD: all d: mesg | d not in d.^(plaintext)
let old_plain = {cipher: Ciphertext,msg:mesg |     {msg in elems[cipher.plaintext]}} | {
    all d: mesg | d not in d.^(old_plain)
}
```
We cannot directly apply transitive closure to the new field as it no longer has arity 2, so we must extract the old relation. the elems relation would only allow us to extract the set of messages for a particular ciphertext.
Hence we define the old_plain set using set builder like notation which is identical to our previous plaintext relation, it has arity 2 so we can apply transitive closure.
