#lang forge
open util/sequences
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
sig tuple extends mesg {
    components: pfunc Int -> mesg
}

abstract sig Key extends mesg {}
abstract sig akey extends Key {} -- asymmetric key
sig skey extends Key {}          -- symmetric key
sig PrivateKey extends akey {}
sig PublicKey extends akey {}

-- Helper to hold relations that match key pairs
one sig KeyPairs {
  pairs: set PrivateKey -> PublicKey,
  owners: func PrivateKey -> name,
  ltks: set name -> name -> skey,

  inv_key_helper: set Key -> Key
}

/** Get a long-term key associated with a pair of agents */
fun getLTK[name_a: name, name_b: name]: lone skey {
    (KeyPairs.ltks)[name_a][name_b] + (KeyPairs.ltks)[name_b][name_a]
}

/** Get the inverse key for a given key (if any). The structure of this predicate 
    is due to Forge's typechecking as of January 2025. The (none & Key) is a workaround
    to give Key type to none, which has univ type by default.  */
/*
fun getInv[k: Key]: one Key {
  (k in PublicKey => ((KeyPairs.pairs).k) else (k.(KeyPairs.pairs)))
  +
  (k in skey => k else (none & Key))
}
*/
fun getInv[k: Key]: one Key {
    (KeyPairs.inv_key_helper).k
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
  data: one mesg, -- may put one mesg instead?
  -- relation is: Tick x Microtick x learned-mesg
  -- Only one agent per tick is receiving, so always know which agent's workspace it is
  workspace: set Microtick -> mesg
}

/** A Microtick represents a step of _learning_ that is part of processing a single 
    message reception. */
sig Microtick {
  -- structure of microticks. (must be rendered linear in every run via `next is linear`)
  -- The `wellformed` predicate below contains constraints that enforce this, in case 
  -- a user forgets the add the linear annotation, but doing so would harm performance. 
  mt_next: lone Microtick
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
   -- NOTE: this means when using enc_no_tpl the message inside would always have
   -- to be a tuple may want to change this to one mesg, does increase scope of solver
   -- though and unclear if using one mesg changes what attacks could be modelled
   plaintext: one tuple
}

sig Hashed extends mesg {
  hash_of: one mesg
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

pred hash_wellformed {
  -- ensures hash_of is acyclic
  all d: mesg | d not in d.^(hash_of)
  -- ensures no two hashed terms are hash of the same term
  all h1: Hashed | all h2:Hashed - h1 | {
    h1.hash_of != h2.hash_of
  }
}

/** Time and micro-time are ordered. 
    (This constraint should be tautologous if the user has given an `is linear` 
    for `next` and `mt_next`.) */
pred timeSafety {
  some firstTimeslot: Timeslot | {
    all ts: Timeslot | ts in firstTimeslot.*next
    no firstTimeslot.~next
    -- field declaration ensures at most one successor
  }
  some firstMicro: Microtick | {
    all ts: Microtick  | ts in firstMicro.*mt_next
    no firstMicro.~mt_next
    -- field declaration ensures at most one successor
  }
}

pred inv_key_helper_constr{
    KeyPairs.inv_key_helper = KeyPairs.pairs + ~(KeyPairs.pairs) + {s1:skey,s2:skey | s1 = s2}
}

/** This (large) predicate contains the vast majority of domain axioms */
pred wellformed {
  hash_wellformed
  inv_key_helper_constr
  -- Design choice: only one message event per timeslot;
  --   assume we have a shared notion of time
  -- all m: Timeslot | isSeqOf[m.data,mesg]
  -- all t: Ciphertext | isSeqOf[t.plaintext,mesg]
  timeSafety
  all t: tuple | isSeqOf[t.components,mesg]
  -- You cannot send a message with no data
  -- all m: Timeslot | some elems[m.data]

  -- someone cannot send a message to themselves
  all m: Timeslot | m.sender.agent not in m.receiver.agent

  -- workspace: workaround to avoid cyclic justification within just deconstructions
  -- AGENT -> TICK -> MICRO-TICK LEARNED_SUBTERM
  all d: mesg | all t: Timeslot, microt: Microtick | let a = t.receiver.agent | d in (workspace[t])[microt] iff {
    -- Base case:
    -- received the data in the clear just now 
    let components_rel = {msg1:tuple,msg2:mesg | {msg2 in elems[msg1.components]}} | {
    {d in (t.data + (t.data).(^components_rel)) and no microt.~mt_next}
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
      d in superterm.plaintext.(^components_rel) and     
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Microtick - microt.*mt_next] + baseKnown[a] and
      getInv[superterm.encryptionKey] in (a.learned_times).(Timeslot - t.*next) + workspace[t][Microtick - microt.*mt_next] + baseKnown[a]
    }}}
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
      d in workspace[t][Microtick] -- derived in any micro-tick in this (reception) timeslot
      -- tuple decomposition is also taken care of in the workspace here
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
    {d in tuple and
     elems[d.components] in (a.learned_times).(Timeslot - t.^next)
     {a not in t.receiver.agent}
    }
    or

    {d in baseKnown[a]}

    or
    -- This was a value generated by the name in this timeslot
    {d in (a.generated_times).t}

    or
    {d in Hashed and
    d.hash_of in (a.learned_times).(Timeslot - t.^next) and
    {a not in t.receiver.agent}
    }    
    }} -- (end big disjunction for learned_times)
  
  -- If you generate something, you do it once only
  all a: name | all d: text | lone t: Timeslot | d in (a.generated_times).t

  -- Messages comprise only values known by the sender
  all m: Timeslot | m.data in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
  -- Always send or receive to the adversary
  all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 

  -- plaintext relation is acyclic  
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  --old_plainw ould be unique so some or all doesn't
--  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
--    all d: mesg | d not in d.^(old_plain)
--  }
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in elems[msg1.components]}} + plaintext + hash_of | {
      all d: mesg | d not in d.^(subterm_rel)
  }
  
  -- Disallow empty ciphertexts
  -- might not need elemes here just some works
  -- all c: Ciphertext | some elems[c.plaintext]

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
  -- let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
  --   supers + supers.^(old_plain) -- union on new subterm relations inside parens
  -- }
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in elems[msg1.components]}} + plaintext + hash_of | {
      supers + supers.(^subterm_rel)
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
    a->m in (learned_times).(Timeslot - t.^next)
}

sig clark_jacob_splice_client extends strand {
  clark_jacob_splice_client_c : one name,
  clark_jacob_splice_client_s : one name,
  clark_jacob_splice_client_as : one name,
  clark_jacob_splice_client_N1 : one text,
  clark_jacob_splice_client_N2 : one text,
  clark_jacob_splice_client_N3 : one text,
  clark_jacob_splice_client_T : one text,
  clark_jacob_splice_client_L : one text
}
pred exec_clark_jacob_splice_client {
  all arbitrary_client_clark_jacob_splice : clark_jacob_splice_client | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c]] or generates [aStrand,getPRIVK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c]]
    }
    (generated_times.Timeslot).(arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1) = arbitrary_client_clark_jacob_splice.agent
    (generated_times.Timeslot).(arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2) = arbitrary_client_clark_jacob_splice.agent
    (generated_times.Timeslot).(arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T) = arbitrary_client_clark_jacob_splice.agent
    (generated_times.Timeslot).(arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L) = arbitrary_client_clark_jacob_splice.agent
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N3
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2
    arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L != arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N3
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      ((arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1)->t0 + (arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2)->t2 + (arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T)->t2 + (arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L)->t2) in (arbitrary_client_clark_jacob_splice.agent).generated_times
      t0+t1+t2+t3 = sender.arbitrary_client_clark_jacob_splice + receiver.arbitrary_client_clark_jacob_splice
      t0.sender = arbitrary_client_clark_jacob_splice
      inds[((t0.data).components)] = 0+1+2
      let name_1  = (((t0.data).components))[0] | {
      let name_2  = (((t0.data).components))[1] | {
      let text_3  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_1 + 1->name_2 + 2->text_3
        name_1 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c
        name_2 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
        text_3 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1
      }}}

      t1.receiver = arbitrary_client_clark_jacob_splice
      inds[((t1.data).components)] = 0+1
      let name_4  = (((t1.data).components))[0] | {
      let enc_5  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_4 + 1->enc_5
        name_4 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as
        learnt_term_by[getPUBK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as],arbitrary_client_clark_jacob_splice.agent,t1]
        inds[(enc_5).plaintext.components] = 0+1+2+3+4
        let name_11  = ((enc_5).plaintext.components)[0] | {
        let name_12  = ((enc_5).plaintext.components)[1] | {
        let text_13  = ((enc_5).plaintext.components)[2] | {
        let name_14  = ((enc_5).plaintext.components)[3] | {
        let pubk_15  = ((enc_5).plaintext.components)[4] | {
          (enc_5).plaintext.components = 0->name_11 + 1->name_12 + 2->text_13 + 3->name_14 + 4->pubk_15
          name_11 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as
          name_12 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c
          text_13 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N1
          name_14 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
          pubk_15 = getPUBK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s]
        }}}}}
        (enc_5).encryptionKey = getPRIVK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_as]
      }}

      t2.sender = arbitrary_client_clark_jacob_splice
      inds[((t2.data).components)] = 0+1+2
      let name_16  = (((t2.data).components))[0] | {
      let name_17  = (((t2.data).components))[1] | {
      let enc_18  = (((t2.data).components))[2] | {
        ((t2.data).components) = 0->name_16 + 1->name_17 + 2->enc_18
        name_16 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c
        name_17 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
        inds[(enc_18).plaintext.components] = 0+1+2
        let text_22  = ((enc_18).plaintext.components)[0] | {
        let text_23  = ((enc_18).plaintext.components)[1] | {
        let enc_24  = ((enc_18).plaintext.components)[2] | {
          (enc_18).plaintext.components = 0->text_22 + 1->text_23 + 2->enc_24
          text_22 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_T
          text_23 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_L
          inds[(enc_24).plaintext.components] = 0+1
          let name_27  = ((enc_24).plaintext.components)[0] | {
          let text_28  = ((enc_24).plaintext.components)[1] | {
            (enc_24).plaintext.components = 0->name_27 + 1->text_28
            name_27 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c
            text_28 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2
          }}
          (enc_24).encryptionKey = getPUBK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s]
        }}}
        (enc_18).encryptionKey = getPRIVK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c]
      }}}

      t3.receiver = arbitrary_client_clark_jacob_splice
      inds[((t3.data).components)] = 0+1+2
      let name_29  = (((t3.data).components))[0] | {
      let name_30  = (((t3.data).components))[1] | {
      let enc_31  = (((t3.data).components))[2] | {
        ((t3.data).components) = 0->name_29 + 1->name_30 + 2->enc_31
        name_29 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_s
        name_30 = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c
        learnt_term_by[getPRIVK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c],arbitrary_client_clark_jacob_splice.agent,t3]
        inds[(enc_31).plaintext.components] = 0
        let hash_33  = ((enc_31).plaintext.components)[0] | {
          (enc_31).plaintext.components = 0->hash_33
          (hash_33).hash_of = arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_N2
        }
        (enc_31).encryptionKey = getPUBK[arbitrary_client_clark_jacob_splice.clark_jacob_splice_client_c]
      }}}

    }}}}
  }
}
sig clark_jacob_splice_authority extends strand {
  clark_jacob_splice_authority_c : one name,
  clark_jacob_splice_authority_s : one name,
  clark_jacob_splice_authority_as : one name,
  clark_jacob_splice_authority_N1 : one text,
  clark_jacob_splice_authority_N2 : one text,
  clark_jacob_splice_authority_N3 : one text,
  clark_jacob_splice_authority_T : one text,
  clark_jacob_splice_authority_L : one text
}
pred exec_clark_jacob_splice_authority {
  all arbitrary_authority_clark_jacob_splice : clark_jacob_splice_authority | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as]] or generates [aStrand,getPRIVK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as]]
    }
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_T != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_L
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_T != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N1
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_T != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N2
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_T != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N3
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_L != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N1
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_L != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N2
    arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_L != arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N3
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      t0+t1+t2+t3 = sender.arbitrary_authority_clark_jacob_splice + receiver.arbitrary_authority_clark_jacob_splice
      t0.receiver = arbitrary_authority_clark_jacob_splice
      inds[((t0.data).components)] = 0+1+2
      let name_34  = (((t0.data).components))[0] | {
      let name_35  = (((t0.data).components))[1] | {
      let text_36  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_34 + 1->name_35 + 2->text_36
        name_34 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c
        name_35 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
        text_36 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N1
      }}}

      t1.sender = arbitrary_authority_clark_jacob_splice
      inds[((t1.data).components)] = 0+1
      let name_37  = (((t1.data).components))[0] | {
      let enc_38  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_37 + 1->enc_38
        name_37 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as
        inds[(enc_38).plaintext.components] = 0+1+2+3+4
        let name_44  = ((enc_38).plaintext.components)[0] | {
        let name_45  = ((enc_38).plaintext.components)[1] | {
        let text_46  = ((enc_38).plaintext.components)[2] | {
        let name_47  = ((enc_38).plaintext.components)[3] | {
        let pubk_48  = ((enc_38).plaintext.components)[4] | {
          (enc_38).plaintext.components = 0->name_44 + 1->name_45 + 2->text_46 + 3->name_47 + 4->pubk_48
          name_44 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as
          name_45 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c
          text_46 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N1
          name_47 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
          pubk_48 = getPUBK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s]
        }}}}}
        (enc_38).encryptionKey = getPRIVK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as]
      }}

      t2.receiver = arbitrary_authority_clark_jacob_splice
      inds[((t2.data).components)] = 0+1+2
      let name_49  = (((t2.data).components))[0] | {
      let name_50  = (((t2.data).components))[1] | {
      let text_51  = (((t2.data).components))[2] | {
        ((t2.data).components) = 0->name_49 + 1->name_50 + 2->text_51
        name_49 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
        name_50 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c
        text_51 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N3
      }}}

      t3.sender = arbitrary_authority_clark_jacob_splice
      inds[((t3.data).components)] = 0+1
      let name_52  = (((t3.data).components))[0] | {
      let enc_53  = (((t3.data).components))[1] | {
        ((t3.data).components) = 0->name_52 + 1->enc_53
        name_52 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as
        inds[(enc_53).plaintext.components] = 0+1+2+3+4
        let name_59  = ((enc_53).plaintext.components)[0] | {
        let name_60  = ((enc_53).plaintext.components)[1] | {
        let text_61  = ((enc_53).plaintext.components)[2] | {
        let name_62  = ((enc_53).plaintext.components)[3] | {
        let pubk_63  = ((enc_53).plaintext.components)[4] | {
          (enc_53).plaintext.components = 0->name_59 + 1->name_60 + 2->text_61 + 3->name_62 + 4->pubk_63
          name_59 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as
          name_60 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_s
          text_61 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_N3
          name_62 = arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c
          pubk_63 = getPUBK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_c]
        }}}}}
        (enc_53).encryptionKey = getPRIVK[arbitrary_authority_clark_jacob_splice.clark_jacob_splice_authority_as]
      }}

    }}}}
  }
}
sig clark_jacob_splice_server extends strand {
  clark_jacob_splice_server_c : one name,
  clark_jacob_splice_server_s : one name,
  clark_jacob_splice_server_as : one name,
  clark_jacob_splice_server_N1 : one text,
  clark_jacob_splice_server_N2 : one text,
  clark_jacob_splice_server_N3 : one text,
  clark_jacob_splice_server_T : one text,
  clark_jacob_splice_server_L : one text
}
pred exec_clark_jacob_splice_server {
  all arbitrary_server_clark_jacob_splice : clark_jacob_splice_server | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s]] or generates [aStrand,getPRIVK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s]]
    }
    (generated_times.Timeslot).(arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3) = arbitrary_server_clark_jacob_splice.agent
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_T != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_L
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_T != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N1
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_T != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N2
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_T != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_L != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N1
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_L != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N2
    arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_L != arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      ((arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3)->t1) in (arbitrary_server_clark_jacob_splice.agent).generated_times
      t0+t1+t2+t3 = sender.arbitrary_server_clark_jacob_splice + receiver.arbitrary_server_clark_jacob_splice
      t0.receiver = arbitrary_server_clark_jacob_splice
      inds[((t0.data).components)] = 0+1+2
      let name_64  = (((t0.data).components))[0] | {
      let name_65  = (((t0.data).components))[1] | {
      let enc_66  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_64 + 1->name_65 + 2->enc_66
        name_64 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c
        name_65 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
        learnt_term_by[getPUBK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c],arbitrary_server_clark_jacob_splice.agent,t0]
        inds[(enc_66).plaintext.components] = 0+1+2
        let text_70  = ((enc_66).plaintext.components)[0] | {
        let text_71  = ((enc_66).plaintext.components)[1] | {
        let enc_72  = ((enc_66).plaintext.components)[2] | {
          (enc_66).plaintext.components = 0->text_70 + 1->text_71 + 2->enc_72
          text_70 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_T
          text_71 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_L
          learnt_term_by[getPRIVK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s],arbitrary_server_clark_jacob_splice.agent,t0]
          inds[(enc_72).plaintext.components] = 0+1
          let name_75  = ((enc_72).plaintext.components)[0] | {
          let text_76  = ((enc_72).plaintext.components)[1] | {
            (enc_72).plaintext.components = 0->name_75 + 1->text_76
            name_75 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c
            text_76 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N2
          }}
          (enc_72).encryptionKey = getPUBK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s]
        }}}
        (enc_66).encryptionKey = getPRIVK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c]
      }}}

      t1.sender = arbitrary_server_clark_jacob_splice
      inds[((t1.data).components)] = 0+1+2
      let name_77  = (((t1.data).components))[0] | {
      let name_78  = (((t1.data).components))[1] | {
      let text_79  = (((t1.data).components))[2] | {
        ((t1.data).components) = 0->name_77 + 1->name_78 + 2->text_79
        name_77 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
        name_78 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c
        text_79 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3
      }}}

      t2.receiver = arbitrary_server_clark_jacob_splice
      inds[((t2.data).components)] = 0+1
      let name_80  = (((t2.data).components))[0] | {
      let enc_81  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->name_80 + 1->enc_81
        name_80 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as
        learnt_term_by[getPUBK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as],arbitrary_server_clark_jacob_splice.agent,t2]
        inds[(enc_81).plaintext.components] = 0+1+2+3+4
        let name_87  = ((enc_81).plaintext.components)[0] | {
        let name_88  = ((enc_81).plaintext.components)[1] | {
        let text_89  = ((enc_81).plaintext.components)[2] | {
        let name_90  = ((enc_81).plaintext.components)[3] | {
        let pubk_91  = ((enc_81).plaintext.components)[4] | {
          (enc_81).plaintext.components = 0->name_87 + 1->name_88 + 2->text_89 + 3->name_90 + 4->pubk_91
          name_87 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as
          name_88 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
          text_89 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N3
          name_90 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c
          pubk_91 = getPUBK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c]
        }}}}}
        (enc_81).encryptionKey = getPRIVK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_as]
      }}

      t3.sender = arbitrary_server_clark_jacob_splice
      inds[((t3.data).components)] = 0+1+2
      let name_92  = (((t3.data).components))[0] | {
      let name_93  = (((t3.data).components))[1] | {
      let enc_94  = (((t3.data).components))[2] | {
        ((t3.data).components) = 0->name_92 + 1->name_93 + 2->enc_94
        name_92 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_s
        name_93 = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c
        inds[(enc_94).plaintext.components] = 0
        let hash_96  = ((enc_94).plaintext.components)[0] | {
          (enc_94).plaintext.components = 0->hash_96
          (hash_96).hash_of = arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_N2
        }
        (enc_94).encryptionKey = getPUBK[arbitrary_server_clark_jacob_splice.clark_jacob_splice_server_c]
      }}}

    }}}}
  }
}
one sig skeleton_clark_jacob_splice_0 {
  skeleton_clark_jacob_splice_0_c : one name,
  skeleton_clark_jacob_splice_0_s : one name,
  skeleton_clark_jacob_splice_0_as : one name,
  skeleton_clark_jacob_splice_0_N1 : one text,
  skeleton_clark_jacob_splice_0_N2 : one text,
  skeleton_clark_jacob_splice_0_N3 : one text,
  skeleton_clark_jacob_splice_0_T : one text,
  skeleton_clark_jacob_splice_0_L : one text
}
pred constrain_skeleton_clark_jacob_splice_0 {
  some skeleton_client_0_strand_0 : clark_jacob_splice_client | {
    skeleton_client_0_strand_0.clark_jacob_splice_client_c = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_c
    skeleton_client_0_strand_0.clark_jacob_splice_client_s = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_s
    skeleton_client_0_strand_0.clark_jacob_splice_client_as = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_as
    skeleton_client_0_strand_0.clark_jacob_splice_client_N1 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N1
    skeleton_client_0_strand_0.clark_jacob_splice_client_N2 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N2
    skeleton_client_0_strand_0.clark_jacob_splice_client_N3 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N3
    skeleton_client_0_strand_0.clark_jacob_splice_client_T = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_T
    skeleton_client_0_strand_0.clark_jacob_splice_client_L = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_L
  }
  some skeleton_authority_0_strand_1 : clark_jacob_splice_authority | {
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_c = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_c
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_s = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_s
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_as = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_as
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_N1 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N1
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_N2 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N2
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_N3 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N3
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_T = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_T
    skeleton_authority_0_strand_1.clark_jacob_splice_authority_L = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_L
  }
  some skeleton_server_0_strand_2 : clark_jacob_splice_server | {
    skeleton_server_0_strand_2.clark_jacob_splice_server_c = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_c
    skeleton_server_0_strand_2.clark_jacob_splice_server_s = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_s
    skeleton_server_0_strand_2.clark_jacob_splice_server_as = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_as
    skeleton_server_0_strand_2.clark_jacob_splice_server_N1 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N1
    skeleton_server_0_strand_2.clark_jacob_splice_server_N2 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N2
    skeleton_server_0_strand_2.clark_jacob_splice_server_N3 = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_N3
    skeleton_server_0_strand_2.clark_jacob_splice_server_T = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_T
    skeleton_server_0_strand_2.clark_jacob_splice_server_L = skeleton_clark_jacob_splice_0.skeleton_clark_jacob_splice_0_L
  }
}
inst honest_run_bounds {
  PublicKey = `PublicKey0 + `PublicKey1 + `PublicKey2 + `PublicKey3
  PrivateKey = `PrivateKey0 + `PrivateKey1 + `PrivateKey2 + `PrivateKey3
  akey = PublicKey + PrivateKey
  no skey
  Key = akey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4
  text = `text0 + `text1 + `text2 + `text3 + `text4
  Hashed = `Hashed0
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10
  mesg = Key + name + Ciphertext + text + Hashed + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7 + `Timeslot8 + `Timeslot9 + `Timeslot10 + `Timeslot11

  components in tuple -> (0+1+2+3+4) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  pairs = KeyPairs -> (`PrivateKey0->`PublicKey0 + `PrivateKey1->`PublicKey1 + `PrivateKey2->`PublicKey2 + `PrivateKey3->`PublicKey3)
  owners = KeyPairs -> (`PrivateKey0->`name0 + `PrivateKey1->`name1 + `PrivateKey2->`name2 + `PrivateKey3->`Attacker0)
  no ltks

  `KeyPairs0.inv_key_helper = `PublicKey0->`PrivateKey0 + `PrivateKey0->`PublicKey0 + `PublicKey1->`PrivateKey1 + `PrivateKey1->`PublicKey1 + `PublicKey2->`PrivateKey2 + `PrivateKey2->`PublicKey2 + `PublicKey3->`PrivateKey3 + `PrivateKey3->`PublicKey3
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7 + `Timeslot7->`Timeslot8 + `Timeslot8->`Timeslot9 + `Timeslot9->`Timeslot10 + `Timeslot10->`Timeslot11
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  clark_jacob_splice_client = `clark_jacob_splice_client0
  clark_jacob_splice_authority = `clark_jacob_splice_authority0
  clark_jacob_splice_server = `clark_jacob_splice_server0
  AttackerStrand = `AttackerStrand0
  strand = clark_jacob_splice_client + clark_jacob_splice_authority + clark_jacob_splice_server + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

clark_jacob_splice_attack: run {
    wellformed

    exec_clark_jacob_splice_client
    exec_clark_jacob_splice_server
    exec_clark_jacob_splice_authority

    constrain_skeleton_clark_jacob_splice_0
    // constrain_skeleton_attack1_1

    no (clark_jacob_splice_client.clark_jacob_splice_client_c & Attacker)
    no (clark_jacob_splice_client.clark_jacob_splice_client_s & Attacker)
    no (clark_jacob_splice_client.clark_jacob_splice_client_as & Attacker)

    no (clark_jacob_splice_server.clark_jacob_splice_server_c & Attacker)
    no (clark_jacob_splice_server.clark_jacob_splice_server_s & Attacker)
    no (clark_jacob_splice_server.clark_jacob_splice_server_as & Attacker)

    no (clark_jacob_splice_authority.clark_jacob_splice_authority_c & Attacker)
    no (clark_jacob_splice_authority.clark_jacob_splice_authority_s & Attacker)
    no (clark_jacob_splice_authority.clark_jacob_splice_authority_as & Attacker)


    no (clark_jacob_splice_client.agent & clark_jacob_splice_server.agent)
    no (clark_jacob_splice_client.agent & clark_jacob_splice_authority.agent)
    no (clark_jacob_splice_server.agent & clark_jacob_splice_authority.agent)

    no (clark_jacob_splice_client.agent & Attacker)
    no (clark_jacob_splice_server.agent & Attacker)
    no (clark_jacob_splice_authority.agent & Attacker)


} for {
    next is linear
    mt_next is linear
    honest_run_bounds
    // attack1_bounds
}