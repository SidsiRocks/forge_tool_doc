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

sig andrew_secure_rpc_A extends strand {
  andrew_secure_rpc_A_a : one name,
  andrew_secure_rpc_A_b : one name,
  andrew_secure_rpc_A_kab_ : one skey,
  andrew_secure_rpc_A_na : one text,
  andrew_secure_rpc_A_nb : one text,
  andrew_secure_rpc_A_nb_ : one text
}
pred exec_andrew_secure_rpc_A {
  all arbitrary_A_andrew_secure_rpc : andrew_secure_rpc_A | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]] or generates [aStrand,getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]]
    }
    (generated_times.Timeslot).(arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_na) = arbitrary_A_andrew_secure_rpc.agent
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      ((arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_na)->t0) in (arbitrary_A_andrew_secure_rpc.agent).generated_times
      t0+t1+t2+t3 = sender.arbitrary_A_andrew_secure_rpc + receiver.arbitrary_A_andrew_secure_rpc
      t0.sender = arbitrary_A_andrew_secure_rpc
      inds[((t0.data).components)] = 0+1
      let name_1  = (((t0.data).components))[0] | {
      let enc_2  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_1 + 1->enc_2
        name_1 = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a
        inds[(enc_2).plaintext.components] = 0
        let text_4  = ((enc_2).plaintext.components)[0] | {
          (enc_2).plaintext.components = 0->text_4
          text_4 = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_na
        }
        (enc_2).encryptionKey = getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]
      }}

      t1.receiver = arbitrary_A_andrew_secure_rpc
      learnt_term_by[getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b],arbitrary_A_andrew_secure_rpc.agent,t1]
      inds[((t1.data)).plaintext.components] = 0+1
      let hash_7  = (((t1.data)).plaintext.components)[0] | {
      let text_8  = (((t1.data)).plaintext.components)[1] | {
        ((t1.data)).plaintext.components = 0->hash_7 + 1->text_8
        (hash_7).hash_of = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_na
        text_8 = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_nb
      }}
      ((t1.data)).encryptionKey = getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]

      t2.sender = arbitrary_A_andrew_secure_rpc
      inds[((t2.data)).plaintext.components] = 0
      let hash_10  = (((t2.data)).plaintext.components)[0] | {
        ((t2.data)).plaintext.components = 0->hash_10
        (hash_10).hash_of = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_nb
      }
      ((t2.data)).encryptionKey = getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]

      t3.receiver = arbitrary_A_andrew_secure_rpc
      learnt_term_by[getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b],arbitrary_A_andrew_secure_rpc.agent,t3]
      inds[((t3.data)).plaintext.components] = 0+1
      let skey_13  = (((t3.data)).plaintext.components)[0] | {
      let text_14  = (((t3.data)).plaintext.components)[1] | {
        ((t3.data)).plaintext.components = 0->skey_13 + 1->text_14
        skey_13 = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_kab_
        text_14 = arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_nb_
      }}
      ((t3.data)).encryptionKey = getLTK[arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_a,arbitrary_A_andrew_secure_rpc.andrew_secure_rpc_A_b]

    }}}}
  }
}
sig andrew_secure_rpc_B extends strand {
  andrew_secure_rpc_B_a : one name,
  andrew_secure_rpc_B_b : one name,
  andrew_secure_rpc_B_kab_ : one skey,
  andrew_secure_rpc_B_na : one text,
  andrew_secure_rpc_B_nb : one text,
  andrew_secure_rpc_B_nb_ : one text
}
pred exec_andrew_secure_rpc_B {
  all arbitrary_B_andrew_secure_rpc : andrew_secure_rpc_B | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]] or generates [aStrand,getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]]
    }
    (generated_times.Timeslot).(arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb) = arbitrary_B_andrew_secure_rpc.agent
    (generated_times.Timeslot).(arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb_) = arbitrary_B_andrew_secure_rpc.agent
    (generated_times.Timeslot).(arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_kab_) = arbitrary_B_andrew_secure_rpc.agent
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      ((arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb)->t1 + (arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb_)->t3 + (arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_kab_)->t3) in (arbitrary_B_andrew_secure_rpc.agent).generated_times
      t0+t1+t2+t3 = sender.arbitrary_B_andrew_secure_rpc + receiver.arbitrary_B_andrew_secure_rpc
      t0.receiver = arbitrary_B_andrew_secure_rpc
      inds[((t0.data).components)] = 0+1
      let name_15  = (((t0.data).components))[0] | {
      let enc_16  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_15 + 1->enc_16
        name_15 = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a
        learnt_term_by[getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b],arbitrary_B_andrew_secure_rpc.agent,t0]
        inds[(enc_16).plaintext.components] = 0
        let text_18  = ((enc_16).plaintext.components)[0] | {
          (enc_16).plaintext.components = 0->text_18
          text_18 = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_na
        }
        (enc_16).encryptionKey = getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]
      }}

      t1.sender = arbitrary_B_andrew_secure_rpc
      inds[((t1.data)).plaintext.components] = 0+1
      let hash_21  = (((t1.data)).plaintext.components)[0] | {
      let text_22  = (((t1.data)).plaintext.components)[1] | {
        ((t1.data)).plaintext.components = 0->hash_21 + 1->text_22
        (hash_21).hash_of = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_na
        text_22 = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb
      }}
      ((t1.data)).encryptionKey = getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]

      t2.receiver = arbitrary_B_andrew_secure_rpc
      learnt_term_by[getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b],arbitrary_B_andrew_secure_rpc.agent,t2]
      inds[((t2.data)).plaintext.components] = 0
      let hash_24  = (((t2.data)).plaintext.components)[0] | {
        ((t2.data)).plaintext.components = 0->hash_24
        (hash_24).hash_of = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb
      }
      ((t2.data)).encryptionKey = getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]

      t3.sender = arbitrary_B_andrew_secure_rpc
      inds[((t3.data)).plaintext.components] = 0+1
      let skey_27  = (((t3.data)).plaintext.components)[0] | {
      let text_28  = (((t3.data)).plaintext.components)[1] | {
        ((t3.data)).plaintext.components = 0->skey_27 + 1->text_28
        skey_27 = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_kab_
        text_28 = arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_nb_
      }}
      ((t3.data)).encryptionKey = getLTK[arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_a,arbitrary_B_andrew_secure_rpc.andrew_secure_rpc_B_b]

    }}}}
  }
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2 + `text3 + `text4 + `text5
  Hashed = `Hashed0 + `Hashed1 + `Hashed2 + `Hashed3
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9
  mesg = Key + name + Ciphertext + text + Hashed + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`Attacker0->`skey1 + `name1->`Attacker0->`skey2
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  andrew_secure_rpc_A = `andrew_secure_rpc_A0
  andrew_secure_rpc_B = `andrew_secure_rpc_B0
  AttackerStrand = `AttackerStrand0
  strand = andrew_secure_rpc_A + andrew_secure_rpc_B + AttackerStrand
}
inst attack_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2 + `text3 + `text4 + `text5
  Hashed = `Hashed0 + `Hashed1 + `Hashed2 + `Hashed3
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9
  mesg = Key + name + Ciphertext + text + Hashed + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7 + `Timeslot8 + `Timeslot9 + `Timeslot10 + `Timeslot11 + `Timeslot12 + `Timeslot13 + `Timeslot14 + `Timeslot15

  components in tuple -> (0+1) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`Attacker0->`skey1 + `name1->`Attacker0->`skey2
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7 + `Timeslot7->`Timeslot8 + `Timeslot8->`Timeslot9 + `Timeslot9->`Timeslot10 + `Timeslot10->`Timeslot11 + `Timeslot11->`Timeslot12 + `Timeslot12->`Timeslot13 + `Timeslot13->`Timeslot14 + `Timeslot14->`Timeslot15
  mt_next = `Microtick0 -> `Microtick1

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  andrew_secure_rpc_A = `andrew_secure_rpc_A0 + `andrew_secure_rpc_A1
  andrew_secure_rpc_B = `andrew_secure_rpc_B0 + `andrew_secure_rpc_B1
  AttackerStrand = `AttackerStrand0
  strand = andrew_secure_rpc_A + andrew_secure_rpc_B + AttackerStrand
}
one sig skeleton_andrew_secure_rpc_0 {
  skeleton_andrew_secure_rpc_0_a : one name,
  skeleton_andrew_secure_rpc_0_b : one name,
  skeleton_andrew_secure_rpc_0_kab_ : one skey,
  skeleton_andrew_secure_rpc_0_na : one text,
  skeleton_andrew_secure_rpc_0_nb : one text,
  skeleton_andrew_secure_rpc_0_nb_ : one text,
  skeleton_andrew_secure_rpc_0_kab_1 : one skey,
  skeleton_andrew_secure_rpc_0_na1 : one text,
  skeleton_andrew_secure_rpc_0_nb1 : one text,
  skeleton_andrew_secure_rpc_0_nb_1 : one text,
  skeleton_andrew_secure_rpc_0_A : one andrew_secure_rpc_A,
  skeleton_andrew_secure_rpc_0_A1 : one andrew_secure_rpc_A,
  skeleton_andrew_secure_rpc_0_B : one andrew_secure_rpc_B,
  skeleton_andrew_secure_rpc_0_B1 : one andrew_secure_rpc_B
}
pred constrain_skeleton_andrew_secure_rpc_0_large_honest_run {
  some t_0 : Timeslot {
  some t_1 : t_0.(^next) {
  some t_2 : t_1.(^next) {
  some t_3 : t_2.(^next) {
  some t_4 : t_3.(^next) {
  some t_5 : t_4.(^next) {
  some t_6 : t_5.(^next) {
  some t_7 : t_6.(^next) {
  some t_8 : t_7.(^next) {
  some t_9 : t_8.(^next) {
  some t_10 : t_9.(^next) {
  some t_11 : t_10.(^next) {
  some t_12 : t_11.(^next) {
  some t_13 : t_12.(^next) {
  some t_14 : t_13.(^next) {
  some t_15 : t_14.(^next) {
    t_0.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A
    inds[(t_0.data.components)] = 0+1
    let name_29  = ((t_0.data.components))[0] | {
    let enc_30  = ((t_0.data.components))[1] | {
      (t_0.data.components) = 0->name_29 + 1->enc_30
      name_29 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a
      inds[(enc_30).plaintext.components] = 0
      let text_32  = ((enc_30).plaintext.components)[0] | {
        (enc_30).plaintext.components = 0->text_32
        text_32 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na
      }
      (enc_30).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]
    }}

    t_1.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B
    inds[(t_1.data.components)] = 0+1
    let name_33  = ((t_1.data.components))[0] | {
    let enc_34  = ((t_1.data.components))[1] | {
      (t_1.data.components) = 0->name_33 + 1->enc_34
      name_33 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a
      inds[(enc_34).plaintext.components] = 0
      let text_36  = ((enc_34).plaintext.components)[0] | {
        (enc_34).plaintext.components = 0->text_36
        text_36 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na
      }
      (enc_34).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]
    }}

    t_2.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B
    inds[((t_2.data)).plaintext.components] = 0+1
    let hash_39  = (((t_2.data)).plaintext.components)[0] | {
    let text_40  = (((t_2.data)).plaintext.components)[1] | {
      ((t_2.data)).plaintext.components = 0->hash_39 + 1->text_40
      (hash_39).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na
      text_40 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb
    }}
    ((t_2.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_3.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A
    inds[((t_3.data)).plaintext.components] = 0+1
    let hash_43  = (((t_3.data)).plaintext.components)[0] | {
    let text_44  = (((t_3.data)).plaintext.components)[1] | {
      ((t_3.data)).plaintext.components = 0->hash_43 + 1->text_44
      (hash_43).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na
      text_44 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb
    }}
    ((t_3.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_4.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A
    inds[((t_4.data)).plaintext.components] = 0
    let hash_46  = (((t_4.data)).plaintext.components)[0] | {
      ((t_4.data)).plaintext.components = 0->hash_46
      (hash_46).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb
    }
    ((t_4.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_5.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B
    inds[((t_5.data)).plaintext.components] = 0
    let hash_48  = (((t_5.data)).plaintext.components)[0] | {
      ((t_5.data)).plaintext.components = 0->hash_48
      (hash_48).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb
    }
    ((t_5.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_6.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B
    inds[((t_6.data)).plaintext.components] = 0+1
    let skey_51  = (((t_6.data)).plaintext.components)[0] | {
    let text_52  = (((t_6.data)).plaintext.components)[1] | {
      ((t_6.data)).plaintext.components = 0->skey_51 + 1->text_52
      skey_51 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_kab_
      text_52 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb_
    }}
    ((t_6.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_7.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A
    inds[((t_7.data)).plaintext.components] = 0+1
    let skey_55  = (((t_7.data)).plaintext.components)[0] | {
    let text_56  = (((t_7.data)).plaintext.components)[1] | {
      ((t_7.data)).plaintext.components = 0->skey_55 + 1->text_56
      skey_55 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_kab_
      text_56 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb_
    }}
    ((t_7.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_8.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A1
    inds[(t_8.data.components)] = 0+1
    let name_57  = ((t_8.data.components))[0] | {
    let enc_58  = ((t_8.data.components))[1] | {
      (t_8.data.components) = 0->name_57 + 1->enc_58
      name_57 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a
      inds[(enc_58).plaintext.components] = 0
      let text_60  = ((enc_58).plaintext.components)[0] | {
        (enc_58).plaintext.components = 0->text_60
        text_60 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na1
      }
      (enc_58).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]
    }}

    t_9.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B1
    inds[(t_9.data.components)] = 0+1
    let name_61  = ((t_9.data.components))[0] | {
    let enc_62  = ((t_9.data.components))[1] | {
      (t_9.data.components) = 0->name_61 + 1->enc_62
      name_61 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a
      inds[(enc_62).plaintext.components] = 0
      let text_64  = ((enc_62).plaintext.components)[0] | {
        (enc_62).plaintext.components = 0->text_64
        text_64 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na1
      }
      (enc_62).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]
    }}

    t_10.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B1
    inds[((t_10.data)).plaintext.components] = 0+1
    let hash_67  = (((t_10.data)).plaintext.components)[0] | {
    let text_68  = (((t_10.data)).plaintext.components)[1] | {
      ((t_10.data)).plaintext.components = 0->hash_67 + 1->text_68
      (hash_67).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na1
      text_68 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb1
    }}
    ((t_10.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_11.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A1
    inds[((t_11.data)).plaintext.components] = 0+1
    let hash_71  = (((t_11.data)).plaintext.components)[0] | {
    let text_72  = (((t_11.data)).plaintext.components)[1] | {
      ((t_11.data)).plaintext.components = 0->hash_71 + 1->text_72
      (hash_71).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_na1
      text_72 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb1
    }}
    ((t_11.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_12.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A1
    inds[((t_12.data)).plaintext.components] = 0
    let hash_74  = (((t_12.data)).plaintext.components)[0] | {
      ((t_12.data)).plaintext.components = 0->hash_74
      (hash_74).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb1
    }
    ((t_12.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_13.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B1
    inds[((t_13.data)).plaintext.components] = 0
    let hash_76  = (((t_13.data)).plaintext.components)[0] | {
      ((t_13.data)).plaintext.components = 0->hash_76
      (hash_76).hash_of = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb1
    }
    ((t_13.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_14.sender = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B1
    inds[((t_14.data)).plaintext.components] = 0+1
    let skey_79  = (((t_14.data)).plaintext.components)[0] | {
    let text_80  = (((t_14.data)).plaintext.components)[1] | {
      ((t_14.data)).plaintext.components = 0->skey_79 + 1->text_80
      skey_79 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_kab_1
      text_80 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb_1
    }}
    ((t_14.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

    t_15.receiver = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A1
    inds[((t_15.data)).plaintext.components] = 0+1
    let skey_83  = (((t_15.data)).plaintext.components)[0] | {
    let text_84  = (((t_15.data)).plaintext.components)[1] | {
      ((t_15.data)).plaintext.components = 0->skey_83 + 1->text_84
      skey_83 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_kab_1
      text_84 = skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_nb_1
    }}
    ((t_15.data)).encryptionKey = getLTK[skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_a,skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_b]

  }}}}}}}}}}}}}}}}
}
pred constrain_skeleton_andrew_secure_rpc_0 {
  constrain_skeleton_andrew_secure_rpc_0_large_honest_run
}
option run_sterling "../../crypto_viz_seq_tuple.js"

pred uniq_orig[d:mesg]{
    one aStrand:strand | {
        originates[aStrand,d] or generates[aStrand,d]
    }
}
pred uniq_orig_strand[s:strand,d:mesg]{
    originates[s,d] or generates[s,d]
}
pred non_orig[d:mesg]{
    no aStrand:strand | {
        originates[aStrand,d] or generates[aStrand,d]
    }
}

--andrew_rpc_term_test : run {
--    wellformed
--    exec_andrew_secure_rpc_A
--    exec_andrew_secure_rpc_B
--    constrain_skeleton_andrew_secure_rpc_0

--    andrew_secure_rpc_A.agent != Attacker
--    andrew_secure_rpc_B.agent != Attacker


--    let a_name = andrew_secure_rpc_A.agent | {
--    let b_name = andrew_secure_rpc_B.agent | {
--        (one a_name) and (one b_name) and (a_name != b_name)
--        all arbitrary_A_andrew_secure_rpc : andrew_secure_rpc_A | {
--        let A0 = arbitrary_A_andrew_secure_rpc | {
--        let na = andrew_secure_rpc_A_na | {
--        let kab_ = andrew_secure_rpc_A_kab_ | {
--            A0.andrew_secure_rpc_A_a = A0.agent
--            -- next line constraint only for generating honest run
--            A0.andrew_secure_rpc_A_b != Attacker and A0.andrew_secure_rpc_A_b != A0.agent

--            uniq_orig_strand[A0,A0.na] and uniq_orig_strand[A0,A0.kab_]
--            A0.kab_ != getLTK[a_name,b_name]
--            not ( A0.na in andrew_secure_rpc_B.(andrew_secure_rpc_B_nb + andrew_secure_rpc_B_nb_) )
--         }}}}

--        all arbitrary_B_andrew_secure_rpc : andrew_secure_rpc_B | {
--        let B0 = arbitrary_B_andrew_secure_rpc | {
--        let nb = andrew_secure_rpc_B_nb | {
--        let nb_ = andrew_secure_rpc_B_nb_ | {
--            B0.andrew_secure_rpc_B_b = B0.agent
--            -- next line constraint only for generating honest run
--            B0.andrew_secure_rpc_B_a != Attacker and B0.andrew_secure_rpc_B_a != B0.agent

--            uniq_orig_strand[B0,B0.nb] and uniq_orig_strand[B0,B0.nb_]
--            B0.nb != B0.nb_
--            not ( B0.nb in andrew_secure_rpc_A.andrew_secure_rpc_A_na )
--            not ( B0.nb_ in andrew_secure_rpc_A.andrew_secure_rpc_A_na )
--        }}}}

--        non_orig[getLTK[a_name,b_name]]
--    }}

--    // all disj arbitrary_B_andrew_secure_rpc_0,arbitrary_B_andrew_secure_rpc_1 : andrew_secure_rpc_B | {
--    //     let B0 = arbitrary_B_andrew_secure_rpc_0 | {
--    //     let B1 = arbitrary_B_andrew_secure_rpc_1 | {
--    //     let nb = andrew_secure_rpc_B_nb | {
--    //     let nb_ = andrew_secure_rpc_B_nb_ | {
--    //         no (B0.(nb + nb_ + kab_) & B1.(nb + nb_ + kab_))
--    //     }}}}
--    // }

--    // all disj arbitrary_A_andrew_secure_rpc_0,arbitrary_A_andrew_secure_rpc_1 : andrew_secure_rpc_A | {
--    //     let A0 = arbitrary_A_andrew_secure_rpc_0 | {
--    //     let A1 = arbitrary_A_andrew_secure_rpc_1 | {
--    //     let na = andrew_secure_rpc_A_na | {
--    //     let kab_ = andrew_secure_rpc_A_kab_ | {
--    //         (A0.na != A1.na)
--    //     }}}}
--    // }
--}for
--    exactly 8 Timeslot,22 mesg,
--    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,3 skey,
--    exactly 0 PrivateKey,exactly 0 PublicKey,
--    exactly 3 name,exactly 6 text,exactly 6 Ciphertext,
--    exactly 1 andrew_secure_rpc_A,exactly 1 andrew_secure_rpc_B,
--    exactly 3 Microtick,
--    3 Int

--    exactly 8 Timeslot,14 mesg,
--    exactly 1 KeyPairs,exactly 2 Key,exactly 0 akey,2 skey,
--    exactly 0 PrivateKey,exactly 0 PublicKey,
--    exactly 3 name,exactly 3 text,exactly 4 Ciphertext,
--    exactly 1 andrew_secure_rpc_A,exactly 1 andrew_secure_rpc_B,
--    exactly 3 Microtick,
--   3 Int


--    exactly 16 Timeslot,38 mesg,
--    exactly 1 KeyPairs,exactly 3 Key,exactly 0 akey,3 skey,
--    exactly 0 PrivateKey,exactly 0 PublicKey,
--    exactly 3 name,exactly 12 text,exactly 12 Ciphertext,
--    exactly 2 andrew_secure_rpc_A,exactly 2 andrew_secure_rpc_B,
--    exactly 3 Microtick,
--    3 Int

--    exactly 16 Timeslot,25 mesg,
--    exactly 1 KeyPairs,exactly 4 Key,exactly 0 akey,4 skey,
--    exactly 0 PrivateKey,exactly 0 PublicKey,
--    exactly 3 name,exactly 6 text,exactly 8 Ciphertext,
--    exactly 4 Hashed,
--    exactly 2 andrew_secure_rpc_A,exactly 2 andrew_secure_rpc_B,
--    exactly 3 Microtick,
--   4 Int

--for {next is linear}

--option solver MiniSatProver
--option logtranslation 1
--option core_minimization rce

option solver Glucose
option logtranslation 1

andrew_rpc_term_test: run {
    wellformed
    exec_andrew_secure_rpc_A
    exec_andrew_secure_rpc_B
    constrain_skeleton_andrew_secure_rpc_0

    not (Attacker in andrew_secure_rpc_A.agent)
    not (Attacker in andrew_secure_rpc_B.agent)

    no (andrew_secure_rpc_A.agent & andrew_secure_rpc_B.agent)
    one andrew_secure_rpc_A.agent
    one andrew_secure_rpc_B.agent

    andrew_secure_rpc_A.andrew_secure_rpc_A_b != Attacker
    andrew_secure_rpc_B.andrew_secure_rpc_B_a != Attacker

    skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A != skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_A1
    skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B != skeleton_andrew_secure_rpc_0.skeleton_andrew_secure_rpc_0_B1
}for
  exactly 3 Int
  for{
      next is linear
      mt_next is linear
--      honest_run_bounds
      attack_run_bounds
  }
