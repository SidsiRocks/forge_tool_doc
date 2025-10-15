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
  data: one mesg,
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
   plaintext: one mesg
}

-- Non-name base value (e.g., nonces)
sig text extends mesg {}
sig tuple extends mesg {
    components: pfunc Int -> mesg
}
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
  -- Constraint ensures that m.components is a well formed sequence
  all m: tuple | isSeqOf[m.components,mesg]

  -- someone cannot send a message to themselves
  all m: Timeslot | m.sender not in m.receiver

  -- workspace: workaround to avoid cyclic justification within just deconstructions
  -- AGENT -> TICK -> MICRO-TICK LEARNED_SUBTERM
  all d: mesg | all t, microt: Timeslot | let a = t.receiver.agent | d in (workspace[t])[microt] iff {
    -- Base case:
    -- received the data in the clear just now 
    {d in t.data and no microt.~next}
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
      d in superterm.plaintext and     
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a] and
      getInv[superterm.encryptionKey] in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}
    or
    {some superterm: tuple | {
      d in elems[superterm.components] and
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}
    }
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
	   d.plaintext in (a.learned_times).(Timeslot - t.^next)
     {a not in t.receiver.agent} -- non-reception
    }
    or

    -- Only build up tuples when sending a message no need to breakdown when receiving a message
    -- (breakdown of tuples handled inside microtick idea probably do not need it inside)
    -- NOTE: this means maximum nesting which can be broken down currently depends on the number of timeslots in the trae
    -- this is undesirable as with the addition of a tuple inside every encrypted term the depth will certainly increase
    { d in tuple and 
      elems[d.components] in (a.learned_times).(Timeslot - t.^next) and
      {a not in t.receiver.agent}
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
  all m: Timeslot | m.data in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
  -- Always send or receive to the adversary
  all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 

  -- plaintext relation is acyclic  
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  -- Now the only type contatining data is tuple and Ciphertext so only have to write 
  -- constraint for those two
  let components_relation = {msg1:mesg,msg2:mesg | {msg2 in (elems[msg1.components] + msg1.plaintext)}} | {
    all d: mesg | d not in d.^(components_relation)
  }
  -- Disallow empty tuples
  -- TODO might not need elemes here just some works
  all t: tuple | some elems[t.components]

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

  let components_relation = {msg1:mesg,msg2:mesg | {msg2 in (elems[msg1.components] + msg1.plaintext)}} | {
    supers + supers.^(components_relation + plaintext) -- union on new subterm relations inside parens
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
      d in subterm[m.data] -- d is a sub-term of m     
      all m2: (sender.s + receiver.s) - m | { -- everything else on the strand
          -- ASSUME: messages are sent/received in same timeslot
          {m2 in m.^(~(next))}
          implies          
          {d not in subterm[m2.data]}
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

sig two_nonce_init extends strand {
  two_nonce_init_a : one name,
  two_nonce_init_b : one name,
  two_nonce_init_n1 : one text,
  two_nonce_init_n2 : one text
}
pred exec_two_nonce_init {
  all arbitrary_init_two_nonce : two_nonce_init | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        some t2 : t1.(^next) {
          t0+t1+t2 = sender.arbitrary_init_two_nonce + receiver.arbitrary_init_two_nonce
          t0.sender = arbitrary_init_two_nonce
          (t0.data) in tuple
          inds[((t0.data).components)] = 0
          some enc_2 : elems[((t0.data).components)] | {
            ((t0.data).components)[0] = enc_2
            ((enc_2).plaintext) in tuple
            inds[(((enc_2).plaintext).components)] = 0
            (((enc_2).plaintext).components)[0] = arbitrary_init_two_nonce.two_nonce_init_n1
            ((enc_2).encryptionKey) = getPUBK[arbitrary_init_two_nonce.two_nonce_init_b]
          }

          t1.receiver = arbitrary_init_two_nonce
          (t1.data) in tuple
          inds[((t1.data).components)] = 0
          some enc_5 : elems[((t1.data).components)] | {
            ((t1.data).components)[0] = enc_5
            learnt_term_by[getPRIVK[arbitrary_init_two_nonce.two_nonce_init_a],arbitrary_init_two_nonce.agent,t1]
            ((enc_5).plaintext) in tuple
            inds[(((enc_5).plaintext).components)] = 0+1
            (((enc_5).plaintext).components)[0] = arbitrary_init_two_nonce.two_nonce_init_n1
            (((enc_5).plaintext).components)[1] = arbitrary_init_two_nonce.two_nonce_init_n2
            ((enc_5).encryptionKey) = getPUBK[arbitrary_init_two_nonce.two_nonce_init_a]
          }

          t2.sender = arbitrary_init_two_nonce
          (t2.data) in tuple
          inds[((t2.data).components)] = 0
          some enc_9 : elems[((t2.data).components)] | {
            ((t2.data).components)[0] = enc_9
            ((enc_9).plaintext) in tuple
            inds[(((enc_9).plaintext).components)] = 0
            (((enc_9).plaintext).components)[0] = arbitrary_init_two_nonce.two_nonce_init_n2
            ((enc_9).encryptionKey) = getPUBK[arbitrary_init_two_nonce.two_nonce_init_b]
          }

        }
      }
    }
  }
}
sig two_nonce_resp extends strand {
  two_nonce_resp_a : one name,
  two_nonce_resp_b : one name,
  two_nonce_resp_n1 : one text,
  two_nonce_resp_n2 : one text
}
pred exec_two_nonce_resp {
  all arbitrary_resp_two_nonce : two_nonce_resp | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        some t2 : t1.(^next) {
          t0+t1+t2 = sender.arbitrary_resp_two_nonce + receiver.arbitrary_resp_two_nonce
          t0.receiver = arbitrary_resp_two_nonce
          (t0.data) in tuple
          inds[((t0.data).components)] = 0
          some enc_12 : elems[((t0.data).components)] | {
            ((t0.data).components)[0] = enc_12
            learnt_term_by[getPRIVK[arbitrary_resp_two_nonce.two_nonce_resp_b],arbitrary_resp_two_nonce.agent,t0]
            ((enc_12).plaintext) in tuple
            inds[(((enc_12).plaintext).components)] = 0
            (((enc_12).plaintext).components)[0] = arbitrary_resp_two_nonce.two_nonce_resp_n1
            ((enc_12).encryptionKey) = getPUBK[arbitrary_resp_two_nonce.two_nonce_resp_b]
          }

          t1.sender = arbitrary_resp_two_nonce
          (t1.data) in tuple
          inds[((t1.data).components)] = 0
          some enc_15 : elems[((t1.data).components)] | {
            ((t1.data).components)[0] = enc_15
            ((enc_15).plaintext) in tuple
            inds[(((enc_15).plaintext).components)] = 0+1
            (((enc_15).plaintext).components)[0] = arbitrary_resp_two_nonce.two_nonce_resp_n1
            (((enc_15).plaintext).components)[1] = arbitrary_resp_two_nonce.two_nonce_resp_n2
            ((enc_15).encryptionKey) = getPUBK[arbitrary_resp_two_nonce.two_nonce_resp_a]
          }

          t2.receiver = arbitrary_resp_two_nonce
          (t2.data) in tuple
          inds[((t2.data).components)] = 0
          some enc_19 : elems[((t2.data).components)] | {
            ((t2.data).components)[0] = enc_19
            learnt_term_by[getPRIVK[arbitrary_resp_two_nonce.two_nonce_resp_b],arbitrary_resp_two_nonce.agent,t2]
            ((enc_19).plaintext) in tuple
            inds[(((enc_19).plaintext).components)] = 0
            (((enc_19).plaintext).components)[0] = arbitrary_resp_two_nonce.two_nonce_resp_n2
            ((enc_19).encryptionKey) = getPUBK[arbitrary_resp_two_nonce.two_nonce_resp_b]
          }

        }
      }
    }
  }
}
one sig skeleton_two_nonce_0 {
  skeleton_two_nonce_0_a : one name,
  skeleton_two_nonce_0_b : one name,
  skeleton_two_nonce_0_n1 : one text,
  skeleton_two_nonce_0_n2 : one text,
  skeleton_two_nonce_0_init : one two_nonce_init,
  skeleton_two_nonce_0_resp : one two_nonce_resp
}
pred constrain_skeleton_two_nonce_0_attack_run {
  some t_0 : Timeslot {
    some t_1 : t_0.(^next) {
      some t_2 : t_1.(^next) {
        some t_3 : t_2.(^next) {
          some t_4 : t_3.(^next) {
            some t_5 : t_4.(^next) {
              t_0.sender = skeleton_two_nonce_0.skeleton_two_nonce_0_init
              (t_0.data) in tuple
              inds[((t_0.data).components)] = 0
              some enc_21 : elems[((t_0.data).components)] | {
                ((t_0.data).components)[0] = enc_21
                ((enc_21).plaintext) in tuple
                inds[(((enc_21).plaintext).components)] = 0
                (((enc_21).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n1
                ((enc_21).encryptionKey) = getPUBK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]
              }

              t_1.receiver = skeleton_two_nonce_0.skeleton_two_nonce_0_resp
              (t_1.data) in tuple
              inds[((t_1.data).components)] = 0
              some enc_23 : elems[((t_1.data).components)] | {
                ((t_1.data).components)[0] = enc_23
                ((enc_23).plaintext) in tuple
                inds[(((enc_23).plaintext).components)] = 0
                (((enc_23).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n1
                ((enc_23).encryptionKey) = getPUBK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]
              }

              t_2.sender = skeleton_two_nonce_0.skeleton_two_nonce_0_resp
              (t_2.data) in tuple
              inds[((t_2.data).components)] = 0
              some enc_25 : elems[((t_2.data).components)] | {
                ((t_2.data).components)[0] = enc_25
                ((enc_25).plaintext) in tuple
                inds[(((enc_25).plaintext).components)] = 0+1
                (((enc_25).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n1
                (((enc_25).plaintext).components)[1] = skeleton_two_nonce_0.skeleton_two_nonce_0_n2
                ((enc_25).encryptionKey) = getPUBK[Attacker]
              }

              t_3.receiver = skeleton_two_nonce_0.skeleton_two_nonce_0_init
              (t_3.data) in tuple
              inds[((t_3.data).components)] = 0
              some enc_28 : elems[((t_3.data).components)] | {
                ((t_3.data).components)[0] = enc_28
                ((enc_28).plaintext) in tuple
                inds[(((enc_28).plaintext).components)] = 0+1
                (((enc_28).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n1
                (((enc_28).plaintext).components)[1] = skeleton_two_nonce_0.skeleton_two_nonce_0_n2
                ((enc_28).encryptionKey) = getPUBK[skeleton_two_nonce_0.skeleton_two_nonce_0_a]
              }

              t_4.sender = skeleton_two_nonce_0.skeleton_two_nonce_0_init
              (t_4.data) in tuple
              inds[((t_4.data).components)] = 0
              some enc_31 : elems[((t_4.data).components)] | {
                ((t_4.data).components)[0] = enc_31
                ((enc_31).plaintext) in tuple
                inds[(((enc_31).plaintext).components)] = 0
                (((enc_31).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n2
                ((enc_31).encryptionKey) = getPUBK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]
              }

              t_5.receiver = skeleton_two_nonce_0.skeleton_two_nonce_0_resp
              (t_5.data) in tuple
              inds[((t_5.data).components)] = 0
              some enc_33 : elems[((t_5.data).components)] | {
                ((t_5.data).components)[0] = enc_33
                ((enc_33).plaintext) in tuple
                inds[(((enc_33).plaintext).components)] = 0
                (((enc_33).plaintext).components)[0] = skeleton_two_nonce_0.skeleton_two_nonce_0_n2
                ((enc_33).encryptionKey) = getPUBK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]
              }

            }
          }
        }
      }
    }
  }
}
pred constrain_skeleton_two_nonce_0 {
  some skeleton_init_0_strand_0 : two_nonce_init | {
    skeleton_init_0_strand_0.two_nonce_init_a = skeleton_two_nonce_0.skeleton_two_nonce_0_a
    skeleton_init_0_strand_0.two_nonce_init_b = skeleton_two_nonce_0.skeleton_two_nonce_0_b
    skeleton_init_0_strand_0.two_nonce_init_n1 = skeleton_two_nonce_0.skeleton_two_nonce_0_n1
  }
  some skeleton_resp_0_strand_1 : two_nonce_resp | {
    skeleton_resp_0_strand_1.two_nonce_resp_a = skeleton_two_nonce_0.skeleton_two_nonce_0_a
    skeleton_resp_0_strand_1.two_nonce_resp_b = skeleton_two_nonce_0.skeleton_two_nonce_0_b
    skeleton_resp_0_strand_1.two_nonce_resp_n2 = skeleton_two_nonce_0.skeleton_two_nonce_0_n2
  }
  skeleton_two_nonce_0.skeleton_two_nonce_0_n1 != skeleton_two_nonce_0.skeleton_two_nonce_0_n2
  no aStrand : strand | {
    originates[aStrand,getPRIVK[skeleton_two_nonce_0.skeleton_two_nonce_0_a]] or generates [aStrand,getPRIVK[skeleton_two_nonce_0.skeleton_two_nonce_0_a]]
  }
  no aStrand : strand | {
    originates[aStrand,getPRIVK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]] or generates [aStrand,getPRIVK[skeleton_two_nonce_0.skeleton_two_nonce_0_b]]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_two_nonce_0.skeleton_two_nonce_0_n1] or generates [aStrand,skeleton_two_nonce_0.skeleton_two_nonce_0_n1]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_two_nonce_0.skeleton_two_nonce_0_n2] or generates [aStrand,skeleton_two_nonce_0.skeleton_two_nonce_0_n2]
  }
  constrain_skeleton_two_nonce_0_attack_run
}
option run_sterling "../../crypto_viz_tuple.js"

pred corrected_attacker_learns[d:mesg]{
    d in (Attacker.learned_times).Timeslot
}

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

--option engine_verbosity 3
--option solver "./run_z3.sh"

pred depth_limitation{
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in (elems[msg1.components] + msg1.plaintext)}} | {
      no subterm_rel.subterm_rel.subterm_rel.subterm_rel.subterm_rel.subterm_rel
  }
}

two_nonce_init_pov : run {
    wellformed

    exec_two_nonce_init
    exec_two_nonce_resp

    constrain_skeleton_two_nonce_0

    two_nonce_init.agent != Attacker
    two_nonce_resp.agent != Attacker

    two_nonce_init.agent != two_nonce_resp.agent

    -- Attacker learns n2 when init believes they are not talking to attacker
    -- corrected_attacker_learns[two_nonce_init.two_nonce_init_n2]
    -- two_nonce_init.two_nonce_init_n2 != two_nonce_resp.two_nonce_resp_n2
    -- depth_limitation
}for
    exactly 6 Timeslot,exactly 25 mesg,exactly 6 Key,
    exactly 6 akey,exactly 3 PublicKey,exactly 3 PrivateKey,
    exactly 3 name,exactly 6 Ciphertext,exactly 2 text,exactly 8 tuple,
    exactly 1 KeyPairs,
    exactly 1 two_nonce_init,exactly 1 two_nonce_resp,
    3 Int
for {next is linear}

--run {} for 3
