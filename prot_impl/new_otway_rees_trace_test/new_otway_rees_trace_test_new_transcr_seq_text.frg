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

abstract sig text extends mesg {}
abstract sig atomic extends text {}

abstract sig Key extends atomic {}
abstract sig akey extends Key {}
sig skey extends Key {}
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
sig name extends atomic {
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

sig Ciphertext extends atomic {
   -- encrypted with this key
   encryptionKey: one Key,
   -- result in concating plaintexts
   --plaintext: set mesg
   plaintext: pfunc Int -> mesg
}

-- Non-name base value (e.g., nonces)
sig nonce extends atomic {}

sig seq extends text {
    --remember to include constraint to ensure the components present are non empty
    components: pfunc Int -> atomic
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
  all m: Timeslot | isSeqOf[m.data,mesg]
  all t: Ciphertext | isSeqOf[t.plaintext,mesg]
  all s: seq | isSeqOf[s.components,atomic]
  -- You cannot send a message with no data
  all m: Timeslot | some elems[m.data]

  -- TODO: ask mam if this assumption is correct
  -- someone cannot send a message to themselves
  -- this should be m.sender.agent not in m.receiver.agent
  -- I don't think there is circumstance where different strand but same agent
  -- would occur, problem with allowing different strands and same agent leads
  -- to cylic justification. Can learn as the term is learnt on the reciever side
  -- because someone sent it, can send it becuase already learnt it.
  -- all m: Timeslot | m.sender not in m.receiver
  all m: Timeslot | m.sender.agent not in m.receiver.agent

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
    { 
        t.receiver.agent = a and
        {some s : seq | {
            d in elems[s.components]
            s in (a.learned_times).(Timeslot - t.^next)
        }}
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
    { d in seq and
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
  all a: name | all d: nonce | lone t: Timeslot | d in (a.generated_times).t

  -- Messages comprise only values known by the sender
  all m: Timeslot | elems[m.data] in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
  -- Always send or receive to the adversary
  all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 

  -- plaintext relation is acyclic  
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  --old_plainw ould be unique so some or all doesn't
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
      let components_rel = {seq_term:seq,msg:mesg | {msg in elems[seq_term.components]}} | {
          all d: mesg | d not in d.^(old_plain + components_rel)
      }
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
      n.generated_times.Timeslot in nonce+Key
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
      let components_rel = {seq_term:seq,msg:mesg | {msg in elems[seq_term.components]}} | {
          supers + supers.^(old_plain + components_rel) -- union on new subterm relations inside parens
      }
  }
  -- TODO add something for finding subterms of seq which extends text
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

-- added comment here to test commit all command



fun getPRIVK[name_a:name] : lone Key{
    (KeyPairs.owners).name_a
}
fun getPUBK[name_a:name] : lone Key {
    (KeyPairs.owners.(name_a)).(KeyPairs.pairs)
}
pred learnt_term_by[m:mesg,a:name,t:Timeslot] {
    m in (a.learned_times).(Timeslot - t.^next)
}

sig ootway_rees_A extends strand {
  ootway_rees_A_a : one name,
  ootway_rees_A_b : one name,
  ootway_rees_A_s : one name,
  ootway_rees_A_m : one text,
  ootway_rees_A_na : one text,
  ootway_rees_A_nb : one text,
  ootway_rees_A_kab : one skey
}
pred exec_ootway_rees_A {
  all arbitrary_A_ootway_rees : ootway_rees_A | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        t0+t1 = sender.arbitrary_A_ootway_rees + receiver.arbitrary_A_ootway_rees
        t0.sender = arbitrary_A_ootway_rees
        inds[(t0.data)] = 0+1+2+3
        some enc_1 : elems[(t0.data)] | {
          (t0.data)[3] = enc_1
          (t0.data)[0] in nonce
          (t0.data)[0] = arbitrary_A_ootway_rees.ootway_rees_A_m
          (t0.data)[1] = arbitrary_A_ootway_rees.ootway_rees_A_a
          (t0.data)[2] = arbitrary_A_ootway_rees.ootway_rees_A_b
          inds[(enc_1).plaintext] = 0+1+2+3
          (enc_1).plaintext[0] in nonce
          (enc_1).plaintext[0] = arbitrary_A_ootway_rees.ootway_rees_A_na
          (enc_1).plaintext[1] in nonce
          (enc_1).plaintext[1] = arbitrary_A_ootway_rees.ootway_rees_A_m
          (enc_1).plaintext[2] = arbitrary_A_ootway_rees.ootway_rees_A_a
          (enc_1).plaintext[3] = arbitrary_A_ootway_rees.ootway_rees_A_b
          (enc_1).encryptionKey = getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]
        }

        t1.receiver = arbitrary_A_ootway_rees
        inds[(t1.data)] = 0+1
        some enc_6 : elems[(t1.data)] | {
          (t1.data)[1] = enc_6
          (t1.data)[0] = arbitrary_A_ootway_rees.ootway_rees_A_m
          learnt_term_by[getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s],arbitrary_A_ootway_rees.agent,t1]
          inds[(enc_6).plaintext] = 0+1
          (enc_6).plaintext[0] = arbitrary_A_ootway_rees.ootway_rees_A_na
          (enc_6).plaintext[1] = arbitrary_A_ootway_rees.ootway_rees_A_kab
          (enc_6).encryptionKey = getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]
        }

      }
    }
  }
}
sig ootway_rees_B extends strand {
  ootway_rees_B_a : one name,
  ootway_rees_B_b : one name,
  ootway_rees_B_s : one name,
  ootway_rees_B_m : one text,
  ootway_rees_B_nb : one text,
  ootway_rees_B_kab : one skey,
  ootway_rees_B_first_a_s_mesg : one mesg,
  ootway_rees_B_second_a_s_mesg : one mesg
}
pred exec_ootway_rees_B {
  all arbitrary_B_ootway_rees : ootway_rees_B | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        some t2 : t1.(^next) {
          some t3 : t2.(^next) {
            t0+t1+t2+t3 = sender.arbitrary_B_ootway_rees + receiver.arbitrary_B_ootway_rees
            t0.receiver = arbitrary_B_ootway_rees
            inds[(t0.data)] = 0+1+2+3
            (t0.data)[0] = arbitrary_B_ootway_rees.ootway_rees_B_m
            (t0.data)[1] = arbitrary_B_ootway_rees.ootway_rees_B_a
            (t0.data)[2] = arbitrary_B_ootway_rees.ootway_rees_B_b
            (t0.data)[3] = arbitrary_B_ootway_rees.ootway_rees_B_first_a_s_mesg

            t1.sender = arbitrary_B_ootway_rees
            inds[(t1.data)] = 0+1+2+3+4
            some enc_9 : elems[(t1.data)] | {
              (t1.data)[4] = enc_9
              (t1.data)[0] in nonce
              (t1.data)[0] = arbitrary_B_ootway_rees.ootway_rees_B_m
              (t1.data)[1] = arbitrary_B_ootway_rees.ootway_rees_B_a
              (t1.data)[2] = arbitrary_B_ootway_rees.ootway_rees_B_b
              (t1.data)[3] = arbitrary_B_ootway_rees.ootway_rees_B_first_a_s_mesg
              inds[(enc_9).plaintext] = 0+1+2+3
              (enc_9).plaintext[0] in nonce
              (enc_9).plaintext[0] = arbitrary_B_ootway_rees.ootway_rees_B_nb
              (enc_9).plaintext[1] in nonce
              (enc_9).plaintext[1] = arbitrary_B_ootway_rees.ootway_rees_B_m
              (enc_9).plaintext[2] = arbitrary_B_ootway_rees.ootway_rees_B_a
              (enc_9).plaintext[3] = arbitrary_B_ootway_rees.ootway_rees_B_b
              (enc_9).encryptionKey = getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]
            }

            t2.receiver = arbitrary_B_ootway_rees
            inds[(t2.data)] = 0+1+2
            some enc_14 : elems[(t2.data)] | {
              (t2.data)[2] = enc_14
              (t2.data)[0] = arbitrary_B_ootway_rees.ootway_rees_B_m
              (t2.data)[1] = arbitrary_B_ootway_rees.ootway_rees_B_second_a_s_mesg
              learnt_term_by[getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s],arbitrary_B_ootway_rees.agent,t2]
              inds[(enc_14).plaintext] = 0+1
              (enc_14).plaintext[0] = arbitrary_B_ootway_rees.ootway_rees_B_nb
              (enc_14).plaintext[1] = arbitrary_B_ootway_rees.ootway_rees_B_kab
              (enc_14).encryptionKey = getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]
            }

            t3.sender = arbitrary_B_ootway_rees
            inds[(t3.data)] = 0+1
            (t3.data)[0] in nonce
            (t3.data)[0] = arbitrary_B_ootway_rees.ootway_rees_B_m
            (t3.data)[1] = arbitrary_B_ootway_rees.ootway_rees_B_second_a_s_mesg

          }
        }
      }
    }
  }
}
sig ootway_rees_S extends strand {
  ootway_rees_S_a : one name,
  ootway_rees_S_b : one name,
  ootway_rees_S_s : one name,
  ootway_rees_S_m : one text,
  ootway_rees_S_na : one text,
  ootway_rees_S_nb : one text,
  ootway_rees_S_kab : one skey
}
pred exec_ootway_rees_S {
  all arbitrary_S_ootway_rees : ootway_rees_S | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        t0+t1 = sender.arbitrary_S_ootway_rees + receiver.arbitrary_S_ootway_rees
        t0.receiver = arbitrary_S_ootway_rees
        inds[(t0.data)] = 0+1+2+3+4
        some enc_17,enc_18 : elems[(t0.data)] | {
          (t0.data)[3] = enc_17
          (t0.data)[4] = enc_18
          (t0.data)[0] = arbitrary_S_ootway_rees.ootway_rees_S_m
          (t0.data)[1] = arbitrary_S_ootway_rees.ootway_rees_S_a
          (t0.data)[2] = arbitrary_S_ootway_rees.ootway_rees_S_b
          learnt_term_by[getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s],arbitrary_S_ootway_rees.agent,t0]
          inds[(enc_17).plaintext] = 0+1+2+3
          (enc_17).plaintext[0] = arbitrary_S_ootway_rees.ootway_rees_S_na
          (enc_17).plaintext[1] = arbitrary_S_ootway_rees.ootway_rees_S_m
          (enc_17).plaintext[2] = arbitrary_S_ootway_rees.ootway_rees_S_a
          (enc_17).plaintext[3] = arbitrary_S_ootway_rees.ootway_rees_S_b
          (enc_17).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]
          learnt_term_by[getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s],arbitrary_S_ootway_rees.agent,t0]
          inds[(enc_18).plaintext] = 0+1+2+3
          (enc_18).plaintext[0] = arbitrary_S_ootway_rees.ootway_rees_S_nb
          (enc_18).plaintext[1] = arbitrary_S_ootway_rees.ootway_rees_S_m
          (enc_18).plaintext[2] = arbitrary_S_ootway_rees.ootway_rees_S_a
          (enc_18).plaintext[3] = arbitrary_S_ootway_rees.ootway_rees_S_b
          (enc_18).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]
        }

        t1.sender = arbitrary_S_ootway_rees
        inds[(t1.data)] = 0+1+2
        some enc_27,enc_28 : elems[(t1.data)] | {
          (t1.data)[1] = enc_27
          (t1.data)[2] = enc_28
          (t1.data)[0] in nonce
          (t1.data)[0] = arbitrary_S_ootway_rees.ootway_rees_S_m
          inds[(enc_27).plaintext] = 0+1
          (enc_27).plaintext[0] in nonce
          (enc_27).plaintext[0] = arbitrary_S_ootway_rees.ootway_rees_S_na
          (enc_27).plaintext[1] = arbitrary_S_ootway_rees.ootway_rees_S_kab
          (enc_27).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]
          inds[(enc_28).plaintext] = 0+1
          (enc_28).plaintext[0] in nonce
          (enc_28).plaintext[0] = arbitrary_S_ootway_rees.ootway_rees_S_nb
          (enc_28).plaintext[1] = arbitrary_S_ootway_rees.ootway_rees_S_kab
          (enc_28).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]
        }

      }
    }
  }
}
one sig skeleton_ootway_rees_0 {
  skeleton_ootway_rees_0_a : one name,
  skeleton_ootway_rees_0_b : one name,
  skeleton_ootway_rees_0_s : one name,
  skeleton_ootway_rees_0_m : one text,
  skeleton_ootway_rees_0_na : one text,
  skeleton_ootway_rees_0_nb : one text,
  skeleton_ootway_rees_0_kab : one skey,
  skeleton_ootway_rees_0_A : one ootway_rees_A,
  skeleton_ootway_rees_0_B : one ootway_rees_B,
  skeleton_ootway_rees_0_S : one ootway_rees_S
}
pred constrain_skeleton_ootway_rees_0 {
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_a != skeleton_ootway_rees_0.skeleton_ootway_rees_0_b
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_a != skeleton_ootway_rees_0.skeleton_ootway_rees_0_s
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_b != skeleton_ootway_rees_0.skeleton_ootway_rees_0_s
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_m != skeleton_ootway_rees_0.skeleton_ootway_rees_0_na
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_m != skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb
  skeleton_ootway_rees_0.skeleton_ootway_rees_0_na != skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb
  no aStrand : strand | {
    originates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_a,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]] or generates [aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_a,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
  }
  no aStrand : strand | {
    originates[aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_b,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]] or generates [aStrand,getLTK[skeleton_ootway_rees_0.skeleton_ootway_rees_0_b,skeleton_ootway_rees_0.skeleton_ootway_rees_0_s]]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_m] or generates [aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_m]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_na] or generates [aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_na]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb] or generates [aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_nb]
  }
  one aStrand : strand | {
    originates[aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab] or generates [aStrand,skeleton_ootway_rees_0.skeleton_ootway_rees_0_kab]
  }
}
option run_sterling "../../crypto_viz_seq.js"

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce


new_ootway_prot_run : run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_ootway_rees_0
    let A = ootway_rees_A | { let B = ootway_rees_B | {
    let S = ootway_rees_S | {
        (A.agent != Attacker) and (B.agent != Attacker) and (S.agent != Attacker)
        (A.agent != B.agent) and (A.agent != S.agent) and (B.agent != S.agent)
    let A_a = ootway_rees_A_a | { let A_b = ootway_rees_A_b | {
    let A_s = ootway_rees_A_s | {
        (A.A_a = A.agent) and (A.A_b = B.agent) and (A.A_s = S.agent)
    } } }

    let B_a = ootway_rees_B_a | { let B_b = ootway_rees_B_b | {
    let B_s = ootway_rees_B_s | {
        (B.B_a = A.agent) and (B.B_b = B.agent) and (B.B_s = S.agent)
    } } }

    let S_a = ootway_rees_S_a | { let S_b = ootway_rees_S_b | {
    let S_s = ootway_rees_S_s | {
        (S.S_a = A.agent) and (S.S_b = B.agent) and (S.S_s = S.agent)
    } } }

    } } }
} for
    exactly 8 Timeslot,exactly 24 mesg,exactly 24 text,exactly 24 atomic,
    exactly 7 Key,exactly 0 akey,exactly 7 skey,exactly 0 PrivateKey,exactly 0 PublicKey,
    exactly 4 name,exactly 9 Ciphertext,exactly 4 nonce,exactly 1 KeyPairs,
    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,
    exactly 1 ootway_rees_S
for { next is linear }
