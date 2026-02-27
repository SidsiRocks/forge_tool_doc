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

sig tmn_init extends strand {
  tmn_init_a : one name,
  tmn_init_b : one name,
  tmn_init_s : one name,
  tmn_init_Ka : one skey,
  tmn_init_Kb : one skey
}
pred exec_tmn_init {
  all arbitrary_init_tmn : tmn_init | {
    (generated_times.Timeslot).(arbitrary_init_tmn.tmn_init_Ka) = arbitrary_init_tmn.agent
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_init_tmn.tmn_init_a]] or generates [aStrand,getPRIVK[arbitrary_init_tmn.tmn_init_a]]
    }
    arbitrary_init_tmn.tmn_init_a != arbitrary_init_tmn.tmn_init_b
    arbitrary_init_tmn.tmn_init_a != arbitrary_init_tmn.tmn_init_s
    arbitrary_init_tmn.tmn_init_b != arbitrary_init_tmn.tmn_init_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_init_tmn.tmn_init_Ka)->t0) in (arbitrary_init_tmn.agent).generated_times
      t0+t1 = sender.arbitrary_init_tmn + receiver.arbitrary_init_tmn
      t0.sender = arbitrary_init_tmn
      inds[((t0.data).components)] = 0+1
      let name_1  = (((t0.data).components))[0] | {
      let enc_2  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_1 + 1->enc_2
        name_1 = arbitrary_init_tmn.tmn_init_b
        inds[(enc_2).plaintext.components] = 0
        let skey_4  = ((enc_2).plaintext.components)[0] | {
          (enc_2).plaintext.components = 0->skey_4
          skey_4 = arbitrary_init_tmn.tmn_init_Ka
        }
        (enc_2).encryptionKey = getPUBK[arbitrary_init_tmn.tmn_init_s]
      }}

      t1.receiver = arbitrary_init_tmn
      inds[((t1.data).components)] = 0+1
      let name_5  = (((t1.data).components))[0] | {
      let enc_6  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_5 + 1->enc_6
        name_5 = arbitrary_init_tmn.tmn_init_b
        learnt_term_by[arbitrary_init_tmn.tmn_init_Ka,arbitrary_init_tmn.agent,t1]
        inds[(enc_6).plaintext.components] = 0
        let skey_8  = ((enc_6).plaintext.components)[0] | {
          (enc_6).plaintext.components = 0->skey_8
          skey_8 = arbitrary_init_tmn.tmn_init_Kb
        }
        (enc_6).encryptionKey = arbitrary_init_tmn.tmn_init_Ka
      }}

    }}
  }
}
sig tmn_resp extends strand {
  tmn_resp_a : one name,
  tmn_resp_b : one name,
  tmn_resp_s : one name,
  tmn_resp_Kb : one skey,
  tmn_resp_Ka : one skey
}
pred exec_tmn_resp {
  all arbitrary_resp_tmn : tmn_resp | {
    (generated_times.Timeslot).(arbitrary_resp_tmn.tmn_resp_Kb) = arbitrary_resp_tmn.agent
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_resp_tmn.tmn_resp_b]] or generates [aStrand,getPRIVK[arbitrary_resp_tmn.tmn_resp_b]]
    }
    arbitrary_resp_tmn.tmn_resp_a != arbitrary_resp_tmn.tmn_resp_b
    arbitrary_resp_tmn.tmn_resp_a != arbitrary_resp_tmn.tmn_resp_s
    arbitrary_resp_tmn.tmn_resp_b != arbitrary_resp_tmn.tmn_resp_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_resp_tmn.tmn_resp_Kb)->t1) in (arbitrary_resp_tmn.agent).generated_times
      t0+t1 = sender.arbitrary_resp_tmn + receiver.arbitrary_resp_tmn
      t0.receiver = arbitrary_resp_tmn
      (t0.data) = arbitrary_resp_tmn.tmn_resp_a

      t1.sender = arbitrary_resp_tmn
      inds[((t1.data).components)] = 0+1
      let name_9  = (((t1.data).components))[0] | {
      let enc_10  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_9 + 1->enc_10
        name_9 = arbitrary_resp_tmn.tmn_resp_a
        inds[(enc_10).plaintext.components] = 0
        let skey_12  = ((enc_10).plaintext.components)[0] | {
          (enc_10).plaintext.components = 0->skey_12
          skey_12 = arbitrary_resp_tmn.tmn_resp_Kb
        }
        (enc_10).encryptionKey = getPUBK[arbitrary_resp_tmn.tmn_resp_s]
      }}

    }}
  }
}
sig tmn_server extends strand {
  tmn_server_a : one name,
  tmn_server_b : one name,
  tmn_server_s : one name,
  tmn_server_Ka : one skey,
  tmn_server_Kb : one skey
}
pred exec_tmn_server {
  all arbitrary_server_tmn : tmn_server | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_server_tmn.tmn_server_s]] or generates [aStrand,getPRIVK[arbitrary_server_tmn.tmn_server_s]]
    }
    arbitrary_server_tmn.tmn_server_a != arbitrary_server_tmn.tmn_server_b
    arbitrary_server_tmn.tmn_server_a != arbitrary_server_tmn.tmn_server_s
    arbitrary_server_tmn.tmn_server_b != arbitrary_server_tmn.tmn_server_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      t0+t1+t2+t3 = sender.arbitrary_server_tmn + receiver.arbitrary_server_tmn
      t0.receiver = arbitrary_server_tmn
      inds[((t0.data).components)] = 0+1
      let name_13  = (((t0.data).components))[0] | {
      let enc_14  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_13 + 1->enc_14
        name_13 = arbitrary_server_tmn.tmn_server_b
        learnt_term_by[getPRIVK[arbitrary_server_tmn.tmn_server_s],arbitrary_server_tmn.agent,t0]
        inds[(enc_14).plaintext.components] = 0
        let skey_16  = ((enc_14).plaintext.components)[0] | {
          (enc_14).plaintext.components = 0->skey_16
          skey_16 = arbitrary_server_tmn.tmn_server_Ka
        }
        (enc_14).encryptionKey = getPUBK[arbitrary_server_tmn.tmn_server_s]
      }}

      t1.sender = arbitrary_server_tmn
      (t1.data) = arbitrary_server_tmn.tmn_server_a

      t2.receiver = arbitrary_server_tmn
      inds[((t2.data).components)] = 0+1
      let name_17  = (((t2.data).components))[0] | {
      let enc_18  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->name_17 + 1->enc_18
        name_17 = arbitrary_server_tmn.tmn_server_a
        learnt_term_by[getPRIVK[arbitrary_server_tmn.tmn_server_s],arbitrary_server_tmn.agent,t2]
        inds[(enc_18).plaintext.components] = 0
        let skey_20  = ((enc_18).plaintext.components)[0] | {
          (enc_18).plaintext.components = 0->skey_20
          skey_20 = arbitrary_server_tmn.tmn_server_Kb
        }
        (enc_18).encryptionKey = getPUBK[arbitrary_server_tmn.tmn_server_s]
      }}

      t3.sender = arbitrary_server_tmn
      inds[((t3.data).components)] = 0+1
      let name_21  = (((t3.data).components))[0] | {
      let enc_22  = (((t3.data).components))[1] | {
        ((t3.data).components) = 0->name_21 + 1->enc_22
        name_21 = arbitrary_server_tmn.tmn_server_b
        inds[(enc_22).plaintext.components] = 0
        let skey_24  = ((enc_22).plaintext.components)[0] | {
          (enc_22).plaintext.components = 0->skey_24
          skey_24 = arbitrary_server_tmn.tmn_server_Kb
        }
        (enc_22).encryptionKey = arbitrary_server_tmn.tmn_server_Ka
      }}

    }}}}
  }
}
one sig skeleton_tmn_0 {
  skeleton_tmn_0_a : one name,
  skeleton_tmn_0_b : one name,
  skeleton_tmn_0_s : one name,
  skeleton_tmn_0_Ka : one skey,
  skeleton_tmn_0_Kb : one skey
}
pred constrain_skeleton_tmn_0 {
  some skeleton_init_0_strand_0 : tmn_init | {
    skeleton_init_0_strand_0.tmn_init_a = skeleton_tmn_0.skeleton_tmn_0_a
    skeleton_init_0_strand_0.tmn_init_b = skeleton_tmn_0.skeleton_tmn_0_b
    skeleton_init_0_strand_0.tmn_init_s = skeleton_tmn_0.skeleton_tmn_0_s
    skeleton_init_0_strand_0.tmn_init_Ka = skeleton_tmn_0.skeleton_tmn_0_Ka
    skeleton_init_0_strand_0.tmn_init_Kb = skeleton_tmn_0.skeleton_tmn_0_Kb
  }
  some skeleton_resp_0_strand_1 : tmn_resp | {
    skeleton_resp_0_strand_1.tmn_resp_a = skeleton_tmn_0.skeleton_tmn_0_a
    skeleton_resp_0_strand_1.tmn_resp_b = skeleton_tmn_0.skeleton_tmn_0_b
    skeleton_resp_0_strand_1.tmn_resp_s = skeleton_tmn_0.skeleton_tmn_0_s
    skeleton_resp_0_strand_1.tmn_resp_Ka = skeleton_tmn_0.skeleton_tmn_0_Ka
    skeleton_resp_0_strand_1.tmn_resp_Kb = skeleton_tmn_0.skeleton_tmn_0_Kb
  }
  some skeleton_server_0_strand_2 : tmn_server | {
    skeleton_server_0_strand_2.tmn_server_a = skeleton_tmn_0.skeleton_tmn_0_a
    skeleton_server_0_strand_2.tmn_server_b = skeleton_tmn_0.skeleton_tmn_0_b
    skeleton_server_0_strand_2.tmn_server_s = skeleton_tmn_0.skeleton_tmn_0_s
    skeleton_server_0_strand_2.tmn_server_Ka = skeleton_tmn_0.skeleton_tmn_0_Ka
    skeleton_server_0_strand_2.tmn_server_Kb = skeleton_tmn_0.skeleton_tmn_0_Kb
  }
}
inst alt_tmn_small {
  PublicKey = `PublicKey0 + `PublicKey1 + `PublicKey2 + `PublicKey3
  PrivateKey = `PrivateKey0 + `PrivateKey1 + `PrivateKey2 + `PrivateKey3
  akey = PublicKey + PrivateKey
  skey = `skey0 + `skey1 + `skey2
  Key = akey + skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2 + `text3
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  pairs = KeyPairs -> (`PrivateKey0->`PublicKey0 + `PrivateKey1->`PublicKey1 + `PrivateKey2->`PublicKey2 + `PrivateKey3->`PublicKey3)
  owners = KeyPairs -> (`PrivateKey0->`name0 + `PrivateKey1->`name1 + `PrivateKey2->`name2 + `PrivateKey3->`Attacker0)
  no ltks

  `KeyPairs0.inv_key_helper = `PublicKey0->`PrivateKey0 + `PrivateKey0->`PublicKey0 + `PublicKey1->`PrivateKey1 + `PrivateKey1->`PublicKey1 + `PublicKey2->`PrivateKey2 + `PrivateKey2->`PublicKey2 + `PublicKey3->`PrivateKey3 + `PrivateKey3->`PublicKey3 + `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  tmn_init = `tmn_init0
  tmn_resp = `tmn_resp0
  tmn_server = `tmn_server0
  AttackerStrand = `AttackerStrand0
  strand = tmn_init + tmn_resp + tmn_server + AttackerStrand
}
inst alt_tmn_attack {
  PublicKey = `PublicKey0 + `PublicKey1 + `PublicKey2 + `PublicKey3
  PrivateKey = `PrivateKey0 + `PrivateKey1 + `PrivateKey2 + `PrivateKey3
  akey = PublicKey + PrivateKey
  skey = `skey0 + `skey1 + `skey2
  Key = akey + skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2 + `text3
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  pairs = KeyPairs -> (`PrivateKey0->`PublicKey0 + `PrivateKey1->`PublicKey1 + `PrivateKey2->`PublicKey2 + `PrivateKey3->`PublicKey3)
  owners = KeyPairs -> (`PrivateKey0->`name0 + `PrivateKey1->`name1 + `PrivateKey2->`name2 + `PrivateKey3->`Attacker0)
  no ltks

  `KeyPairs0.inv_key_helper = `PublicKey0->`PrivateKey0 + `PrivateKey0->`PublicKey0 + `PublicKey1->`PrivateKey1 + `PrivateKey1->`PublicKey1 + `PublicKey2->`PrivateKey2 + `PrivateKey2->`PublicKey2 + `PublicKey3->`PrivateKey3 + `PrivateKey3->`PublicKey3 + `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  tmn_init = `tmn_init0
  tmn_resp = `tmn_resp0
  tmn_server = `tmn_server0
  AttackerStrand = `AttackerStrand0
  strand = tmn_init + tmn_resp + tmn_server + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

pred attacker_learns2[d: mesg] {
  d in Attacker.learned_times.Timeslot
}

pred self_names_constraint{
    all arbitrary_init_tmn : tmn_init | {
        arbitrary_init_tmn.tmn_init_a = arbitrary_init_tmn.agent
    }
    all arbitrary_resp_tmn : tmn_resp | {
        arbitrary_resp_tmn.tmn_resp_b = arbitrary_resp_tmn.agent
    }
    all arbitrary_server_tmn : tmn_server | {
        arbitrary_server_tmn.tmn_server_s = arbitrary_server_tmn.agent
    }
}
pred not_talking_with_attacker{
    all arbitrary_init_tmn : tmn_init | {
        arbitrary_init_tmn.tmn_init_a != Attacker
        arbitrary_init_tmn.tmn_init_b != Attacker
        arbitrary_init_tmn.tmn_init_s != Attacker
    }
    all arbitrary_resp_tmn : tmn_resp | {
        arbitrary_resp_tmn.tmn_resp_a != Attacker
        arbitrary_resp_tmn.tmn_resp_b != Attacker
        arbitrary_resp_tmn.tmn_resp_s != Attacker
    }
    all arbitrary_server_tmn : tmn_server | {
        arbitrary_server_tmn.tmn_server_a != Attacker
        arbitrary_server_tmn.tmn_server_b != Attacker
        arbitrary_server_tmn.tmn_server_s != Attacker
    }
}

pred all_distinct_agents{
    no (tmn_init.agent & tmn_resp.agent)
    no (tmn_resp.agent & tmn_server.agent)
    no (tmn_server.agent & tmn_init.agent)
}
pred gen_honest_run{
    self_names_constraint
    not_talking_with_attacker
    all_distinct_agents
}
pred cannot_gen_privk{
    -- no private key can be generated
    no (PrivateKey & ((name.generated_times).Timeslot))
}
pred gen_attack{
    self_names_constraint
    cannot_gen_privk
    tmn_resp.tmn_resp_a != Attacker
    tmn_resp.tmn_resp_s != Attacker
    attacker_learns2[tmn_resp.tmn_resp_Kb]
}

tmn_attack : run {

  wellformed

  exec_tmn_init
  exec_tmn_resp
  exec_tmn_server

  -- constrain_skeleton_tmn_0

  -- honest participants
  tmn_init.agent != Attacker
  tmn_resp.agent != Attacker
  tmn_server.agent != Attacker

  -- tmn_init.tmn_init_a != tmn_init.tmn_init_b
  -- tmn_init.tmn_init_a != tmn_init.tmn_init_s
  -- tmn_init.tmn_init_b != tmn_init.tmn_init_s

  -- gen_honest_run
  -- secrecy violation
  gen_attack
} for {
  next is linear
  alt_tmn_small
}