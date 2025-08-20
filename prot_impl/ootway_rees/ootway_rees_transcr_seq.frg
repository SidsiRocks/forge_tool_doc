#lang forge

/*
  Base domain model of strand space style crypto (2021)
    Abby Siegel
    Mia Santomauro 
    Tim Nelson 

  We say "strand space style" above because this model approximates the strand-space 
  formalism. See the "Prototyping Formal Methods Tools" paper for more information.

  Design notes: 
    - We opted to build this in Relational Forge, not Temporal Forge; at the time, 
      Temporal Forge was very new and still being tested. 
    - Forge has a somewhat more restricted syntax than Alloy. E.g., Forge doesn't 
      have `facts` (which are always true); instead, predicates must be asserted. 
    - CPSA has some idiosyncratic terminology, which we echo here somewhat. For 
      example, the "strand" is not the same as the "agent" for that strand; it 
      may be best to think of the agent as a knowledge database and the strand 
      as the protocol role execution.
    - This model embraces Dolev-Yao in a very concrete way: there is an explicit 
      attacker, who is also the medium of communication between participants.
*/

-- NOTE WELL: `mesg` is what CPSA calls terms; we echo that here, do not confuse 
-- `mesg` with just messages being sent or received.
abstract sig mesg {} 

abstract sig Key extends mesg {}
abstract sig akey extends Key {} -- asymmetric key
sig skey extends Key {}          -- symmetric key
sig PrivateKey extends akey {}
sig PublicKey extends akey {}

-- Helper to hold relations that match key pairs
one sig KeyPairs {
  pairs: set PrivateKey -> PublicKey,
  owners: func PrivateKey -> name,
  ltks: set name -> name -> skey
}

/** Get a long-term key associated with a pair of agents */
fun getLTK[name_a: name, name_b: name]: lone skey {
  (KeyPairs.ltks)[name_a][name_b]
}

/** Get the inverse key for a given key (if any). The structure of this predicate 
    is due to Forge's typechecking as of January 2025. The (none & Key) is a workaround
    to give Key type to none, which has univ type by default.  */
fun getInv[k: Key]: one Key {
  (k in PublicKey => ((KeyPairs.pairs).k) else (k.(KeyPairs.pairs)))
  +
  (k in skey => k else (none & Key))
}


-- Time indexes (t=0, t=1, ...). These are also used as micro-tick indexes, so the 
-- bound on `Timeslot` will also affect how many microticks are available between ticks.
sig Timeslot {
  -- structure of time (must be rendered linear in every run via `next is linear`)
  next: lone Timeslot,
  
  -- <=1 actual "message tuple" sent/received per timeslot
  sender: one strand,
  receiver: one strand,  
  -- data: set mesg, 
  data: pfunc Int -> mesg,
  -- relation is: Tick x Microtick x learned-mesg
  -- Only one agent per tick is receiving, so always know which agent's workspace it is
  workspace: set Timeslot -> mesg
}

-- As names process received messages, they learn pieces of data
-- (they may also generate new values on their own)
sig name extends mesg {
  learned_times: set mesg -> Timeslot,
  generated_times: set mesg -> Timeslot
}

-- every strand will be either a protocol role or the attacker/medium
abstract sig strand {
  -- the name associated with this strand
  agent: one name
}

one sig AttackerStrand extends strand {}
one sig Attacker extends name {}

sig Ciphertext extends mesg {
   -- encrypted with this key
   encryptionKey: one Key,
   -- result in concating plaintexts
   --plaintext: set mesg
   plaintext: pfunc Int -> mesg
}

-- Non-name base value (e.g., nonces)
sig text extends mesg {}

/** The starting knowledge base for all agents */
fun baseKnown[a: name]: set mesg {
    -- name knows all public keys
    PublicKey
    +
    -- name knows the private keys it owns
    (KeyPairs.owners).a
    +
    -- name knows long-term keys they are party to    
    {d : skey | some a2 : name - a | d in getLTK[a, a2] + getLTK[a2, a] }
    +
    -- names know their own names
    name
}

/** This (large) predicate contains the vast majority of domain axioms */
pred wellformed {
  -- Design choice: only one message event per timeslot;
  --   assume we have a shared notion of time
  all m: Timeslot | isSeqOf[m.data,mesg]
  all t: Ciphertext | isSeqOf[t.plaintext,mesg]
  -- You cannot send a message with no data
  all m: Timeslot | some elems[m.data]

  -- someone cannot send a message to themselves
  all m: Timeslot | m.sender not in m.receiver

  -- workspace: workaround to avoid cyclic justification within just deconstructions
  -- AGENT -> TICK -> MICRO-TICK LEARNED_SUBTERM
  all d: mesg | all t, microt: Timeslot | let a = t.receiver.agent | d in (workspace[t])[microt] iff {
    -- Base case:
    -- received the data in the clear just now 
    {d in elems[t.data] and no microt.~next}
    or
    -- Inductive case:
    -- breaking down a ciphertext we learned *previously*, or that we've produced from 
    -- something larger this timeslot via a key we learned *previously*, or that we've 
    -- produced from something larger in this timeslot Note use of "previously" by 
    -- subtracting the *reflexive* transitive closure is crucial in preventing cyclic justification.
    --   Note: the baseKnown function includes an agent's private key, otherwise "prior
    --   knowledge" is empty (even of their private key!)
    { 
      --d not in ((a.workspace)[t])[Timeslot - microt.^next] and -- first time appearing
      {some superterm : Ciphertext | {      
      d in elems[superterm.plaintext] and     
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a] and
      getInv[superterm.encryptionKey] in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}}
  }
 
  -- names only learn information that associated strands are explicitly sent 
  -- (start big disjunction for learned_times)
  all d: mesg | all t: Timeslot | all a: name | d->t in a.learned_times iff {
    -- they have not already learned this value
    {d not in (a.learned_times).(Timeslot - t.*next)} and 

    -- This base-case is handled in the workspace now, hence commented out:
    --   They received a message directly containing d (may be a ciphertext)
    { --{some m: Message | {d in m.data and t = m.sendTime and m.receiver.agent = a}}
    --or
    
    -- deconstruct encrypted term 
    -- constrain time to reception to avoid cyclic justification of knowledge. e.g.,
    --    "I know enc(other-agent's-private-key, pubk(me)) [from below via construct]"
    --    "I know other-agent's-private-key [from above via deconstruct]""
    -- instead: separate the two temporally: deconstruct on recv, construct on non-reception
    -- in that case, the cycle can't exist in the same timeslot
    -- might think to write an accessibleSubterms function as below, except:
    -- consider: (k1, enc(k2, enc(n1, invk(k2)), invk(k1)))
    -- or, worse: (k1, enc(x, invk(k3)), enc(k2, enc(k3, invk(k2)), invk(k1)))
    { t.receiver.agent = a
      d in workspace[t][Timeslot] -- derived in any micro-tick in this (reception) timeslot
    }   
    or 
    -- construct encrypted terms (only allow at NON-reception time; see above)
    -- NOTE WELL: if ever allow an agent to send/receive at same time, need rewrite 
    {d in Ciphertext and 
	   d.encryptionKey in (a.learned_times).(Timeslot - t.^next) and        
	   elems[d.plaintext] in (a.learned_times).(Timeslot - t.^next)
     {a not in t.receiver.agent} -- non-reception
    }
    or

    {d in baseKnown[a]}

    or
    -- This was a value generated by the name in this timeslot
    {d in (a.generated_times).t}    
    }} -- (end big disjunction for learned_times)
  
  -- If you generate something, you do it once only
  all a: name | all d: text | lone t: Timeslot | d in (a.generated_times).t

  -- Messages comprise only values known by the sender
  all m: Timeslot | elems[m.data] in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
  -- Always send or receive to the adversary
  all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 

  -- plaintext relation is acyclic  
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  --old_plainw ould be unique so some or all doesn't
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
    all d: mesg | d not in d.^(old_plain)
  }
  
  -- Disallow empty ciphertexts
  -- might not need elemes here just some works
  all c: Ciphertext | some elems[c.plaintext]

  (KeyPairs.pairs).PublicKey = PrivateKey -- total
  PrivateKey.(KeyPairs.pairs) = PublicKey -- total
  all privKey: PrivateKey | {one pubKey: PublicKey | privKey->pubKey in KeyPairs.pairs} -- uniqueness re: pairing
  all priv1: PrivateKey | all priv2: PrivateKey - priv1 | all pub: PublicKey | priv1->pub in KeyPairs.pairs implies priv2->pub not in KeyPairs.pairs

  -- Private keys are disjoint with respect to ownership
  all a1, a2: name | { 
    (some KeyPairs.owners.a1 and a1 != a2) implies 
      (KeyPairs.owners.a1 != KeyPairs.owners.a2)
  }


  -- at most one long-term key per (ordered) pair of names
  all a:name, b:name | lone getLTK[a,b]
  
  -- assume long-term keys are used for only one agent pair (or unused)
  all k: skey | lone (KeyPairs.ltks).k

  -- The Attacker agent is represented by the attacker strand
  AttackerStrand.agent = Attacker

/*
  -- If one agent has a key, it is different from any other agent's key
  all a1, a2: name | { 
    (some KeyPairs.owners.a1 and a1 != a2) implies 
      (KeyPairs.owners.a1 != KeyPairs.owners.a2)
  }

  -- private key ownership is unique 
  all p: PrivateKey | one p.(KeyPairs.owners) 
*/

  -- generation only of text and keys, not complex terms
  --  furthermore, only generate if unknown
  all n: name | {
      n.generated_times.Timeslot in text+Key
      all t: Timeslot, d: mesg | {
          d in n.generated_times.t implies {
              all t2: t.~(^next) | { d not in n.learned_times.t2 }
              d not in baseKnown[n]              
          }
      }
  }
}

/** Definition of subterms for some set of terms */
fun subterm[supers: set mesg]: set mesg {
  -- VITAL: if you add a new subterm relation, needs to be added here, too!
  -- do cross check that it actually returns the correct thing and not an empty set
  -- or something
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
    supers + supers.^(old_plain) -- union on new subterm relations inside parens
  }
}

/** When does a strand 'originate' some term? 
(Note: it's vital this definition is about strands, not names.)
*/
pred originates[s: strand, d: mesg] {

  -- unsigned term t originates on n in N iff
  --   term(n) is positive and
  --   t subterm of term(n) and
  --   whenever n' precedes n on the same strand, t is not subterm of n'

  some m: sender.s | { -- messages sent by strand s (positive term)     
      d in subterm[elems[m.data]] -- d is a sub-term of m     
      all m2: (sender.s + receiver.s) - m | { -- everything else on the strand
          -- ASSUME: messages are sent/received in same timeslot
          {m2 in m.^(~(next))}
          implies          
          {d not in subterm[elems[m2.data]]}
      }
  }
}

-- the agent generates this term
pred generates[s: strand, d: mesg] {
  some ((s.agent).generated_times)[d]
}

-- the attacker eventually learns this field value
pred attacker_learns[s: strand, d: mesg] {
  s.d in Attacker.learned_times.Timeslot
}
-- the agent for this strand eventually learns this value
pred strand_agent_learns[learner: strand, s: strand, d: mesg] {
  s.d in (learner.agent).learned_times.Timeslot
}

------------------------------------------------------
-- Keeping notes on what didn't work in modeling;
--   everything after this point is not part of the model.
------------------------------------------------------

-- Problem: (k1, enc(k2, enc(n1, invk(k2)), invk(k1)))
--  Problem: (k1, enc(x, invk(k3)), enc(k2, enc(k3, invk(k2)), invk(k1)))
--    needs knowledge to grow on the way through the tree, possibly sideways
-- so this approach won't work
/*fun accessibleSubterms[supers: set mesg, known: set mesg]: set mesg {
  let openable = {c: Ciphertext | getInv[c.encryptionKey] in known} |
    supers + 
    supers.^(plaintext & (openable -> mesg))
}*/

/*
-- This is the example of where narrowing would be useful; it currently causes
-- an error in last-checker (necessarily empty join on a side of an ITE that isn't
-- really used).  January 2024
run {
  some pub: PublicKey | {
      some getInv[pub]
  }
}
*/


fun getPRIVK[name_a:name] : lone Key{
    (KeyPairs.owners).name_a
}
fun getPUBK[name_a:name] : lone Key {
    (KeyPairs.owners.(name_a)).(KeyPairs.pairs)
}
pred learnt_term_by[m:mesg,a:name,t:Timeslot] {
    m in (a.learned_times).(Timeslot - t.^next)
}

sig ootway_rees_A extends strand{
    ootway_rees_A_a: one name,
    ootway_rees_A_b: one name,
    ootway_rees_A_s: one name,
    ootway_rees_A_m: one text,
    ootway_rees_A_na: one text,
    ootway_rees_A_nb: one text,
    ootway_rees_A_kab: one skey
}

-- predicate follows below
pred exec_ootway_rees_A {
    all arbitrary_ootway_rees_A : ootway_rees_A | {
        some t0,t1 : Timeslot | {
            t1 in t0.(^next)
            
            t0 + t1  = sender.arbitrary_ootway_rees_A + receiver.arbitrary_ootway_rees_A
            
            t0.sender = arbitrary_ootway_rees_A
            t1.receiver = arbitrary_ootway_rees_A
            
            inds[t0.data] = 0 + 1 + 2 + 3
            some atom1,atom2,atom3,enc4 : elems[t0.data] {
                (t0.data)[0] = atom1
                (t0.data)[1] = atom2
                (t0.data)[2] = atom3
                (t0.data)[3] = enc4
                atom1 = arbitrary_ootway_rees_A.ootway_rees_A_m
                atom2 = arbitrary_ootway_rees_A.ootway_rees_A_a
                atom3 = arbitrary_ootway_rees_A.ootway_rees_A_b
                enc4 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_A.ootway_rees_A_a,arbitrary_ootway_rees_A.ootway_rees_A_s],arbitrary_ootway_rees_A.agent,t0] => {
                    getLTK[arbitrary_ootway_rees_A.ootway_rees_A_a,arbitrary_ootway_rees_A.ootway_rees_A_s] = (enc4).encryptionKey
                    inds[((enc4).plaintext)] = 0 + 1 + 2 + 3
                    some atom5,atom6,atom7,atom8 : elems[((enc4).plaintext)] {
                        (((enc4).plaintext))[0] = atom5
                        (((enc4).plaintext))[1] = atom6
                        (((enc4).plaintext))[2] = atom7
                        (((enc4).plaintext))[3] = atom8
                        atom5 = arbitrary_ootway_rees_A.ootway_rees_A_na
                        atom6 = arbitrary_ootway_rees_A.ootway_rees_A_m
                        atom7 = arbitrary_ootway_rees_A.ootway_rees_A_a
                        atom8 = arbitrary_ootway_rees_A.ootway_rees_A_b
                    }
                }
            }
            inds[t1.data] = 0 + 1
            some atom9,enc10 : elems[t1.data] {
                (t1.data)[0] = atom9
                (t1.data)[1] = enc10
                atom9 = arbitrary_ootway_rees_A.ootway_rees_A_m
                enc10 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_A.ootway_rees_A_a,arbitrary_ootway_rees_A.ootway_rees_A_s],arbitrary_ootway_rees_A.agent,t1] => {
                    getLTK[arbitrary_ootway_rees_A.ootway_rees_A_a,arbitrary_ootway_rees_A.ootway_rees_A_s] = (enc10).encryptionKey
                    inds[((enc10).plaintext)] = 0 + 1
                    some atom11,atom12 : elems[((enc10).plaintext)] {
                        (((enc10).plaintext))[0] = atom11
                        (((enc10).plaintext))[1] = atom12
                        atom11 = arbitrary_ootway_rees_A.ootway_rees_A_na
                        atom12 = arbitrary_ootway_rees_A.ootway_rees_A_kab
                    }
                }
            }
        }
    }
}
-- end of predicate

sig ootway_rees_B extends strand{
    ootway_rees_B_a: one name,
    ootway_rees_B_b: one name,
    ootway_rees_B_s: one name,
    ootway_rees_B_m: one text,
    ootway_rees_B_na: one text,
    ootway_rees_B_nb: one text,
    ootway_rees_B_kab: one skey
}

-- predicate follows below
pred exec_ootway_rees_B {
    all arbitrary_ootway_rees_B : ootway_rees_B | {
        some t0,t1,t2,t3 : Timeslot | {
            t1 in t0.(^next)
            t2 in t1.(^next)
            t3 in t2.(^next)
            
            t0 + t1 + t2 + t3  = sender.arbitrary_ootway_rees_B + receiver.arbitrary_ootway_rees_B
            
            t0.receiver = arbitrary_ootway_rees_B
            t1.sender = arbitrary_ootway_rees_B
            t2.receiver = arbitrary_ootway_rees_B
            t3.sender = arbitrary_ootway_rees_B
            
            inds[t0.data] = 0 + 1 + 2 + 3
            some atom13,atom14,atom15,enc16 : elems[t0.data] {
                (t0.data)[0] = atom13
                (t0.data)[1] = atom14
                (t0.data)[2] = atom15
                (t0.data)[3] = enc16
                atom13 = arbitrary_ootway_rees_B.ootway_rees_B_m
                atom14 = arbitrary_ootway_rees_B.ootway_rees_B_a
                atom15 = arbitrary_ootway_rees_B.ootway_rees_B_b
                enc16 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t0] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc16).encryptionKey
                    inds[((enc16).plaintext)] = 0 + 1 + 2 + 3
                    some atom17,atom18,atom19,atom20 : elems[((enc16).plaintext)] {
                        (((enc16).plaintext))[0] = atom17
                        (((enc16).plaintext))[1] = atom18
                        (((enc16).plaintext))[2] = atom19
                        (((enc16).plaintext))[3] = atom20
                        atom17 = arbitrary_ootway_rees_B.ootway_rees_B_na
                        atom18 = arbitrary_ootway_rees_B.ootway_rees_B_m
                        atom19 = arbitrary_ootway_rees_B.ootway_rees_B_a
                        atom20 = arbitrary_ootway_rees_B.ootway_rees_B_b
                    }
                }
            }
            inds[t1.data] = 0 + 1 + 2 + 3 + 4
            some atom21,atom22,atom23,enc24,enc25 : elems[t1.data] {
                (t1.data)[0] = atom21
                (t1.data)[1] = atom22
                (t1.data)[2] = atom23
                (t1.data)[3] = enc24
                (t1.data)[4] = enc25
                atom21 = arbitrary_ootway_rees_B.ootway_rees_B_m
                atom22 = arbitrary_ootway_rees_B.ootway_rees_B_a
                atom23 = arbitrary_ootway_rees_B.ootway_rees_B_b
                enc24 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t1] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc24).encryptionKey
                    inds[((enc24).plaintext)] = 0 + 1 + 2 + 3
                    some atom26,atom27,atom28,atom29 : elems[((enc24).plaintext)] {
                        (((enc24).plaintext))[0] = atom26
                        (((enc24).plaintext))[1] = atom27
                        (((enc24).plaintext))[2] = atom28
                        (((enc24).plaintext))[3] = atom29
                        atom26 = arbitrary_ootway_rees_B.ootway_rees_B_na
                        atom27 = arbitrary_ootway_rees_B.ootway_rees_B_m
                        atom28 = arbitrary_ootway_rees_B.ootway_rees_B_a
                        atom29 = arbitrary_ootway_rees_B.ootway_rees_B_b
                    }
                }
                enc25 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_b,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t1] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_b,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc25).encryptionKey
                    inds[((enc25).plaintext)] = 0 + 1 + 2 + 3
                    some atom30,atom31,atom32,atom33 : elems[((enc25).plaintext)] {
                        (((enc25).plaintext))[0] = atom30
                        (((enc25).plaintext))[1] = atom31
                        (((enc25).plaintext))[2] = atom32
                        (((enc25).plaintext))[3] = atom33
                        atom30 = arbitrary_ootway_rees_B.ootway_rees_B_nb
                        atom31 = arbitrary_ootway_rees_B.ootway_rees_B_m
                        atom32 = arbitrary_ootway_rees_B.ootway_rees_B_a
                        atom33 = arbitrary_ootway_rees_B.ootway_rees_B_b
                    }
                }
            }
            inds[t2.data] = 0 + 1 + 2
            some atom34,enc35,enc36 : elems[t2.data] {
                (t2.data)[0] = atom34
                (t2.data)[1] = enc35
                (t2.data)[2] = enc36
                atom34 = arbitrary_ootway_rees_B.ootway_rees_B_m
                enc35 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t2] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc35).encryptionKey
                    inds[((enc35).plaintext)] = 0 + 1
                    some atom37,atom38 : elems[((enc35).plaintext)] {
                        (((enc35).plaintext))[0] = atom37
                        (((enc35).plaintext))[1] = atom38
                        atom37 = arbitrary_ootway_rees_B.ootway_rees_B_na
                        atom38 = arbitrary_ootway_rees_B.ootway_rees_B_kab
                    }
                }
                enc36 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_b,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t2] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_b,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc36).encryptionKey
                    inds[((enc36).plaintext)] = 0 + 1
                    some atom39,atom40 : elems[((enc36).plaintext)] {
                        (((enc36).plaintext))[0] = atom39
                        (((enc36).plaintext))[1] = atom40
                        atom39 = arbitrary_ootway_rees_B.ootway_rees_B_nb
                        atom40 = arbitrary_ootway_rees_B.ootway_rees_B_kab
                    }
                }
            }
            inds[t3.data] = 0 + 1
            some atom41,enc42 : elems[t3.data] {
                (t3.data)[0] = atom41
                (t3.data)[1] = enc42
                atom41 = arbitrary_ootway_rees_B.ootway_rees_B_m
                enc42 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s],arbitrary_ootway_rees_B.agent,t3] => {
                    getLTK[arbitrary_ootway_rees_B.ootway_rees_B_a,arbitrary_ootway_rees_B.ootway_rees_B_s] = (enc42).encryptionKey
                    inds[((enc42).plaintext)] = 0 + 1
                    some atom43,atom44 : elems[((enc42).plaintext)] {
                        (((enc42).plaintext))[0] = atom43
                        (((enc42).plaintext))[1] = atom44
                        atom43 = arbitrary_ootway_rees_B.ootway_rees_B_na
                        atom44 = arbitrary_ootway_rees_B.ootway_rees_B_kab
                    }
                }
            }
        }
    }
}
-- end of predicate

sig ootway_rees_S extends strand{
    ootway_rees_S_a: one name,
    ootway_rees_S_b: one name,
    ootway_rees_S_s: one name,
    ootway_rees_S_m: one text,
    ootway_rees_S_na: one text,
    ootway_rees_S_nb: one text,
    ootway_rees_S_kab: one skey
}

-- predicate follows below
pred exec_ootway_rees_S {
    all arbitrary_ootway_rees_S : ootway_rees_S | {
        some t0,t1 : Timeslot | {
            t1 in t0.(^next)
            
            t0 + t1  = sender.arbitrary_ootway_rees_S + receiver.arbitrary_ootway_rees_S
            
            t0.receiver = arbitrary_ootway_rees_S
            t1.sender = arbitrary_ootway_rees_S
            
            inds[t0.data] = 0 + 1 + 2 + 3 + 4
            some atom45,atom46,atom47,enc48,enc49 : elems[t0.data] {
                (t0.data)[0] = atom45
                (t0.data)[1] = atom46
                (t0.data)[2] = atom47
                (t0.data)[3] = enc48
                (t0.data)[4] = enc49
                atom45 = arbitrary_ootway_rees_S.ootway_rees_S_m
                atom46 = arbitrary_ootway_rees_S.ootway_rees_S_a
                atom47 = arbitrary_ootway_rees_S.ootway_rees_S_b
                enc48 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_S.ootway_rees_S_a,arbitrary_ootway_rees_S.ootway_rees_S_s],arbitrary_ootway_rees_S.agent,t0] => {
                    getLTK[arbitrary_ootway_rees_S.ootway_rees_S_a,arbitrary_ootway_rees_S.ootway_rees_S_s] = (enc48).encryptionKey
                    inds[((enc48).plaintext)] = 0 + 1 + 2 + 3
                    some atom50,atom51,atom52,atom53 : elems[((enc48).plaintext)] {
                        (((enc48).plaintext))[0] = atom50
                        (((enc48).plaintext))[1] = atom51
                        (((enc48).plaintext))[2] = atom52
                        (((enc48).plaintext))[3] = atom53
                        atom50 = arbitrary_ootway_rees_S.ootway_rees_S_na
                        atom51 = arbitrary_ootway_rees_S.ootway_rees_S_m
                        atom52 = arbitrary_ootway_rees_S.ootway_rees_S_a
                        atom53 = arbitrary_ootway_rees_S.ootway_rees_S_b
                    }
                }
                enc49 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_S.ootway_rees_S_b,arbitrary_ootway_rees_S.ootway_rees_S_s],arbitrary_ootway_rees_S.agent,t0] => {
                    getLTK[arbitrary_ootway_rees_S.ootway_rees_S_b,arbitrary_ootway_rees_S.ootway_rees_S_s] = (enc49).encryptionKey
                    inds[((enc49).plaintext)] = 0 + 1 + 2 + 3
                    some atom54,atom55,atom56,atom57 : elems[((enc49).plaintext)] {
                        (((enc49).plaintext))[0] = atom54
                        (((enc49).plaintext))[1] = atom55
                        (((enc49).plaintext))[2] = atom56
                        (((enc49).plaintext))[3] = atom57
                        atom54 = arbitrary_ootway_rees_S.ootway_rees_S_nb
                        atom55 = arbitrary_ootway_rees_S.ootway_rees_S_m
                        atom56 = arbitrary_ootway_rees_S.ootway_rees_S_a
                        atom57 = arbitrary_ootway_rees_S.ootway_rees_S_b
                    }
                }
            }
            inds[t1.data] = 0 + 1 + 2
            some atom58,enc59,enc60 : elems[t1.data] {
                (t1.data)[0] = atom58
                (t1.data)[1] = enc59
                (t1.data)[2] = enc60
                atom58 = arbitrary_ootway_rees_S.ootway_rees_S_m
                enc59 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_S.ootway_rees_S_a,arbitrary_ootway_rees_S.ootway_rees_S_s],arbitrary_ootway_rees_S.agent,t1] => {
                    getLTK[arbitrary_ootway_rees_S.ootway_rees_S_a,arbitrary_ootway_rees_S.ootway_rees_S_s] = (enc59).encryptionKey
                    inds[((enc59).plaintext)] = 0 + 1
                    some atom61,atom62 : elems[((enc59).plaintext)] {
                        (((enc59).plaintext))[0] = atom61
                        (((enc59).plaintext))[1] = atom62
                        atom61 = arbitrary_ootway_rees_S.ootway_rees_S_na
                        atom62 = arbitrary_ootway_rees_S.ootway_rees_S_kab
                    }
                }
                enc60 in Ciphertext
                learnt_term_by[getLTK[arbitrary_ootway_rees_S.ootway_rees_S_b,arbitrary_ootway_rees_S.ootway_rees_S_s],arbitrary_ootway_rees_S.agent,t1] => {
                    getLTK[arbitrary_ootway_rees_S.ootway_rees_S_b,arbitrary_ootway_rees_S.ootway_rees_S_s] = (enc60).encryptionKey
                    inds[((enc60).plaintext)] = 0 + 1
                    some atom63,atom64 : elems[((enc60).plaintext)] {
                        (((enc60).plaintext))[0] = atom63
                        (((enc60).plaintext))[1] = atom64
                        atom63 = arbitrary_ootway_rees_S.ootway_rees_S_nb
                        atom64 = arbitrary_ootway_rees_S.ootway_rees_S_kab
                    }
                }
            }
        }
    }
}
-- end of predicate

one sig skeleton_ootway_rees_0 {
    skeleton_ootway_rees_0_a: one name,
    skeleton_ootway_rees_0_b: one name,
    skeleton_ootway_rees_0_s: one name,
    skeleton_ootway_rees_0_m: one text,
    skeleton_ootway_rees_0_na: one text,
    skeleton_ootway_rees_0_nb: one text,
    skeleton_ootway_rees_0_kab: one skey
}
pred constrain_skeleton_ootway_rees_0 {
    some skeleton_ootway_rees_0_strand0 : ootway_rees_S | {
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_a = skeleton_ootway_rees_0_strand0.ootway_rees_S_a
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_b = skeleton_ootway_rees_0_strand0.ootway_rees_S_b
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_s = skeleton_ootway_rees_0_strand0.ootway_rees_S_s
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_m = skeleton_ootway_rees_0_strand0.ootway_rees_S_m
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_na = skeleton_ootway_rees_0_strand0.ootway_rees_S_na
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb = skeleton_ootway_rees_0_strand0.ootway_rees_S_nb
        skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab = skeleton_ootway_rees_0_strand0.ootway_rees_S_kab
    }

    not ( getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_a,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s] in baseKnown[Attacker]  )
    no aStrand : strand | {
        originates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_a,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
        or
        generates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_a,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
    }
    
    not ( getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_b,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s] in baseKnown[Attacker]  )
    no aStrand : strand | {
        originates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_b,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
        or
        generates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_b,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
    }
    
    not ( skeleton_ootway_rees_0.skeleton_ootway_rees_0_m in baseKnown[Attacker]  )
    one aStrand : strand | {
        originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_m]
        or
        generates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_m]
    }
    
    not ( skeleton_ootway_rees_0.skeleton_ootway_rees_0_na in baseKnown[Attacker]  )
    one aStrand : strand | {
        originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_na]
        or
        generates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_na]
    }
    
    not ( skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb in baseKnown[Attacker]  )
    one aStrand : strand | {
        originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb]
        or
        generates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb]
    }
    
    not ( skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab in baseKnown[Attacker]  )
    one aStrand : strand | {
        originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab]
        or
        generates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab]
    }
    
}
option run_sterling "../../crypto_viz_seq.js"

--option run_sterling off
pred prot_conditions{
        
    --ensure agents performing their own role correctly
    
    ootway_rees_A.ootway_rees_A_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_b = ootway_rees_B.agent
    ootway_rees_S.ootway_rees_S_s = ootway_rees_S.agent 
    

    ootway_rees_A.ootway_rees_A_na != ootway_rees_A.ootway_rees_A_m  
    
    ootway_rees_B.ootway_rees_B_nb != ootway_rees_B.ootway_rees_B_m 
    ootway_rees_B.ootway_rees_B_nb != ootway_rees_B.ootway_rees_B_na   
    
    ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_nb != ootway_rees_S.ootway_rees_S_kab
    ootway_rees_S.ootway_rees_S_m  != ootway_rees_S.ootway_rees_S_kab
    --ensuring k_ab is not a long term key
    --no (KeyPairs.ltks).(ootway_rees_S.ootway_rees_S_kab)

    ootway_rees_A.agent != Attacker
    ootway_rees_B.agent != Attacker
    ootway_rees_S.agent != Attacker
    
    --Adding this below by itself makes it unsat somehow
    --ootway_rees_S.ootway_rees_S_na != ootway_rees_S.ootway_rees_S_nb

    --Adding these to create an honest run of the protocol
    ootway_rees_A.ootway_rees_A_b = ootway_rees_B.agent 
    ootway_rees_A.ootway_rees_A_s = ootway_rees_S.agent 

    ootway_rees_B.ootway_rees_B_a = ootway_rees_A.agent
    ootway_rees_B.ootway_rees_B_s = ootway_rees_S.agent

    ootway_rees_S.ootway_rees_S_a = ootway_rees_A.agent
    ootway_rees_S.ootway_rees_S_b = ootway_rees_B.agent

    --added this because a run generated code where ltk was sent instead of k_ab
    not (ootway_rees_S.ootway_rees_S_kab in (name.(name.(KeyPairs.ltks))))
}

ootway_prot_run : run {
    --should not ideally need this anyway
    all n: name | no getLTK[n,n]
    --placing constraint that no long term key can be generated
    --first part is all long term keys, second part is all generated terms
    --the set difference should be empty
    --no (  (name.(name.(KeyPairs.ltks))) - (name.generated_times.Timeslot))
    --Above was the old constraint which had incorrect logic

    --This is what the correct constraint would look like
    (name.(name.(KeyPairs.ltks))) = (name.(name.(KeyPairs.ltks))) - (name.generated_times.Timeslot)

    wellformed
    prot_conditions
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_ootway_rees_0
} for 
    --mesg = Key + name + Ciphertext + text
    --mesg = 3   + 4    + 9          + 4
    exactly 8 Timeslot,20 mesg,
    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,exactly 3 skey, --3 keys for ltk a s, ltk b s,kab 
    exactly 0 PublicKey,exactly 0 PrivateKey,
    exactly 4 name,exactly 4 text,exactly 9 Ciphertext, --4 names a,b,s,attacker ; 4 texts m,na,nb,kab ; cipher texts 6 based on estimate ; 4 Ciphertext should also work
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S,
    4 Int
for {next is linear}