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

sig needham_schroeder_sym_key_init extends strand {
  needham_schroeder_sym_key_init_a : one name,
  needham_schroeder_sym_key_init_b : one name,
  needham_schroeder_sym_key_init_s : one name,
  needham_schroeder_sym_key_init_Na : one text,
  needham_schroeder_sym_key_init_Nb : one text,
  needham_schroeder_sym_key_init_Kab : one skey,
  needham_schroeder_sym_key_init_msg : one mesg
}
pred exec_needham_schroeder_sym_key_init {
  all arbitrary_init_needham_schroeder_sym_key : needham_schroeder_sym_key_init | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a,arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s]] or generates [aStrand,getLTK[arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a,arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s]]
    }
    (generated_times.Timeslot).(arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Na) = arbitrary_init_needham_schroeder_sym_key.agent
    arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a != arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_b
    arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a != arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s
    arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_b != arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
    some t4 : t3.(^next) {
      ((arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Na)->t0) in (arbitrary_init_needham_schroeder_sym_key.agent).generated_times
      t0+t1+t2+t3+t4 = sender.arbitrary_init_needham_schroeder_sym_key + receiver.arbitrary_init_needham_schroeder_sym_key
      t0.sender = arbitrary_init_needham_schroeder_sym_key
      inds[((t0.data).components)] = 0+1+2
      let name_1  = (((t0.data).components))[0] | {
      let name_2  = (((t0.data).components))[1] | {
      let text_3  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_1 + 1->name_2 + 2->text_3
        name_1 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a
        name_2 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_b
        text_3 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Na
      }}}

      t1.receiver = arbitrary_init_needham_schroeder_sym_key
      learnt_term_by[getLTK[arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a,arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s],arbitrary_init_needham_schroeder_sym_key.agent,t1]
      inds[((t1.data)).plaintext.components] = 0+1+2+3
      let text_8  = (((t1.data)).plaintext.components)[0] | {
      let name_9  = (((t1.data)).plaintext.components)[1] | {
      let skey_10  = (((t1.data)).plaintext.components)[2] | {
      let mesg_11  = (((t1.data)).plaintext.components)[3] | {
        ((t1.data)).plaintext.components = 0->text_8 + 1->name_9 + 2->skey_10 + 3->mesg_11
        text_8 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Na
        name_9 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_b
        skey_10 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Kab
        mesg_11 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_msg
      }}}}
      ((t1.data)).encryptionKey = getLTK[arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_a,arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_s]

      t2.sender = arbitrary_init_needham_schroeder_sym_key
      (t2.data) = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_msg

      t3.receiver = arbitrary_init_needham_schroeder_sym_key
      learnt_term_by[arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Kab,arbitrary_init_needham_schroeder_sym_key.agent,t3]
      inds[((t3.data)).plaintext.components] = 0
      let text_13  = (((t3.data)).plaintext.components)[0] | {
        ((t3.data)).plaintext.components = 0->text_13
        text_13 = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Nb
      }
      ((t3.data)).encryptionKey = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Kab

      t4.sender = arbitrary_init_needham_schroeder_sym_key
      inds[((t4.data)).plaintext.components] = 0
      let hash_15  = (((t4.data)).plaintext.components)[0] | {
        ((t4.data)).plaintext.components = 0->hash_15
        (hash_15).hash_of = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Nb
      }
      ((t4.data)).encryptionKey = arbitrary_init_needham_schroeder_sym_key.needham_schroeder_sym_key_init_Kab

    }}}}}
  }
}
sig needham_schroeder_sym_key_server extends strand {
  needham_schroeder_sym_key_server_a : one name,
  needham_schroeder_sym_key_server_b : one name,
  needham_schroeder_sym_key_server_s : one name,
  needham_schroeder_sym_key_server_Na : one text,
  needham_schroeder_sym_key_server_Kab : one skey
}
pred exec_needham_schroeder_sym_key_server {
  all arbitrary_server_needham_schroeder_sym_key : needham_schroeder_sym_key_server | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]] or generates [aStrand,getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]] or generates [aStrand,getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]]
    }
    (generated_times.Timeslot).(arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Kab) = arbitrary_server_needham_schroeder_sym_key.agent
    arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a != arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b
    arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a != arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s
    arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b != arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Kab)->t1) in (arbitrary_server_needham_schroeder_sym_key.agent).generated_times
      t0+t1 = sender.arbitrary_server_needham_schroeder_sym_key + receiver.arbitrary_server_needham_schroeder_sym_key
      t0.receiver = arbitrary_server_needham_schroeder_sym_key
      inds[((t0.data).components)] = 0+1+2
      let name_16  = (((t0.data).components))[0] | {
      let name_17  = (((t0.data).components))[1] | {
      let text_18  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_16 + 1->name_17 + 2->text_18
        name_16 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a
        name_17 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b
        text_18 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Na
      }}}

      t1.sender = arbitrary_server_needham_schroeder_sym_key
      inds[((t1.data)).plaintext.components] = 0+1+2+3
      let text_23  = (((t1.data)).plaintext.components)[0] | {
      let name_24  = (((t1.data)).plaintext.components)[1] | {
      let skey_25  = (((t1.data)).plaintext.components)[2] | {
      let enc_26  = (((t1.data)).plaintext.components)[3] | {
        ((t1.data)).plaintext.components = 0->text_23 + 1->name_24 + 2->skey_25 + 3->enc_26
        text_23 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Na
        name_24 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b
        skey_25 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Kab
        inds[(enc_26).plaintext.components] = 0+1
        let skey_29  = ((enc_26).plaintext.components)[0] | {
        let name_30  = ((enc_26).plaintext.components)[1] | {
          (enc_26).plaintext.components = 0->skey_29 + 1->name_30
          skey_29 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_Kab
          name_30 = arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a
        }}
        (enc_26).encryptionKey = getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_b,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]
      }}}}
      ((t1.data)).encryptionKey = getLTK[arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_a,arbitrary_server_needham_schroeder_sym_key.needham_schroeder_sym_key_server_s]

    }}
  }
}
sig needham_schroeder_sym_key_resp extends strand {
  needham_schroeder_sym_key_resp_a : one name,
  needham_schroeder_sym_key_resp_b : one name,
  needham_schroeder_sym_key_resp_s : one name,
  needham_schroeder_sym_key_resp_Nb : one text,
  needham_schroeder_sym_key_resp_Kab : one skey
}
pred exec_needham_schroeder_sym_key_resp {
  all arbitrary_resp_needham_schroeder_sym_key : needham_schroeder_sym_key_resp | {
    (generated_times.Timeslot).(arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Nb) = arbitrary_resp_needham_schroeder_sym_key.agent
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b,arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s]] or generates [aStrand,getLTK[arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b,arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s]]
    }
    arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_a != arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b
    arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_a != arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s
    arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b != arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Nb)->t1) in (arbitrary_resp_needham_schroeder_sym_key.agent).generated_times
      t0+t1+t2 = sender.arbitrary_resp_needham_schroeder_sym_key + receiver.arbitrary_resp_needham_schroeder_sym_key
      t0.receiver = arbitrary_resp_needham_schroeder_sym_key
      learnt_term_by[getLTK[arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b,arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s],arbitrary_resp_needham_schroeder_sym_key.agent,t0]
      inds[((t0.data)).plaintext.components] = 0+1
      let skey_33  = (((t0.data)).plaintext.components)[0] | {
      let name_34  = (((t0.data)).plaintext.components)[1] | {
        ((t0.data)).plaintext.components = 0->skey_33 + 1->name_34
        skey_33 = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Kab
        name_34 = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_a
      }}
      ((t0.data)).encryptionKey = getLTK[arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_b,arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_s]

      t1.sender = arbitrary_resp_needham_schroeder_sym_key
      inds[((t1.data)).plaintext.components] = 0
      let text_36  = (((t1.data)).plaintext.components)[0] | {
        ((t1.data)).plaintext.components = 0->text_36
        text_36 = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Nb
      }
      ((t1.data)).encryptionKey = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Kab

      t2.receiver = arbitrary_resp_needham_schroeder_sym_key
      learnt_term_by[arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Kab,arbitrary_resp_needham_schroeder_sym_key.agent,t2]
      inds[((t2.data)).plaintext.components] = 0
      let hash_38  = (((t2.data)).plaintext.components)[0] | {
        ((t2.data)).plaintext.components = 0->hash_38
        (hash_38).hash_of = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Nb
      }
      ((t2.data)).encryptionKey = arbitrary_resp_needham_schroeder_sym_key.needham_schroeder_sym_key_resp_Kab

    }}}
  }
}
one sig skeleton_needham_schroeder_sym_key_0 {
  skeleton_needham_schroeder_sym_key_0_a : one name,
  skeleton_needham_schroeder_sym_key_0_b : one name,
  skeleton_needham_schroeder_sym_key_0_s : one name,
  skeleton_needham_schroeder_sym_key_0_Na : one text,
  skeleton_needham_schroeder_sym_key_0_Kab : one skey
}
pred constrain_skeleton_needham_schroeder_sym_key_0 {
  some skeleton_init_0_strand_0 : needham_schroeder_sym_key_init | {
    skeleton_init_0_strand_0.needham_schroeder_sym_key_init_a = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_a
    skeleton_init_0_strand_0.needham_schroeder_sym_key_init_b = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_b
    skeleton_init_0_strand_0.needham_schroeder_sym_key_init_s = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_s
    skeleton_init_0_strand_0.needham_schroeder_sym_key_init_Kab = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_Kab
    skeleton_init_0_strand_0.needham_schroeder_sym_key_init_Na = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_Na
  }
  some skeleton_server_0_strand_1 : needham_schroeder_sym_key_server | {
    skeleton_server_0_strand_1.needham_schroeder_sym_key_server_a = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_a
    skeleton_server_0_strand_1.needham_schroeder_sym_key_server_b = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_b
    skeleton_server_0_strand_1.needham_schroeder_sym_key_server_s = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_s
    skeleton_server_0_strand_1.needham_schroeder_sym_key_server_Kab = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_Kab
    skeleton_server_0_strand_1.needham_schroeder_sym_key_server_Na = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_Na
  }
  some skeleton_resp_0_strand_2 : needham_schroeder_sym_key_resp | {
    skeleton_resp_0_strand_2.needham_schroeder_sym_key_resp_a = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_a
    skeleton_resp_0_strand_2.needham_schroeder_sym_key_resp_b = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_b
    skeleton_resp_0_strand_2.needham_schroeder_sym_key_resp_s = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_s
    skeleton_resp_0_strand_2.needham_schroeder_sym_key_resp_Kab = skeleton_needham_schroeder_sym_key_0.skeleton_needham_schroeder_sym_key_0_Kab
  }
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5
  text = `text0 + `text1
  Hashed = `Hashed0
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5
  mesg = Key + name + Ciphertext + text + Hashed + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7 + `Timeslot8 + `Timeslot9

  components in tuple -> (0+1+2+3+4) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2 + `Microtick3
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7 + `Timeslot7->`Timeslot8 + `Timeslot8->`Timeslot9
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2 + `Microtick2 -> `Microtick3

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  needham_schroeder_sym_key_init = `needham_schroeder_sym_key_init0
  needham_schroeder_sym_key_server = `needham_schroeder_sym_key_server0
  needham_schroeder_sym_key_resp = `needham_schroeder_sym_key_resp0
  AttackerStrand = `AttackerStrand0
  strand = needham_schroeder_sym_key_init + needham_schroeder_sym_key_server + needham_schroeder_sym_key_resp + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

needham_schroeder_sym_key_honest_run: run {
    wellformed

    exec_needham_schroeder_sym_key_init
    exec_needham_schroeder_sym_key_server
    exec_needham_schroeder_sym_key_resp

    constrain_skeleton_needham_schroeder_sym_key_0

    // no (needham_schroeder_sym_key_init.agent & needham_schroeder_sym_key_server.agent)

    // needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_a != needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_b

    needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_b != Attacker
    needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_s != Attacker
    needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_a != Attacker

    needham_schroeder_sym_key_server.needham_schroeder_sym_key_server_a != Attacker
    needham_schroeder_sym_key_server.needham_schroeder_sym_key_server_b != Attacker
    needham_schroeder_sym_key_server.needham_schroeder_sym_key_server_s != Attacker

    needham_schroeder_sym_key_resp.needham_schroeder_sym_key_resp_a != Attacker
    needham_schroeder_sym_key_resp.needham_schroeder_sym_key_resp_b != Attacker
    needham_schroeder_sym_key_resp.needham_schroeder_sym_key_resp_s != Attacker

    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_server.agent
    needham_schroeder_sym_key_init.agent != needham_schroeder_sym_key_resp.agent
    needham_schroeder_sym_key_server.agent != needham_schroeder_sym_key_resp.agent

    not Attacker in (needham_schroeder_sym_key_init + needham_schroeder_sym_key_server + needham_schroeder_sym_key_resp).agent

    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

    // needham_schroeder_sym_key_init.needham_schroeder_sym_key_init_Kab in Attacker.learned_times.Timeslot

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}