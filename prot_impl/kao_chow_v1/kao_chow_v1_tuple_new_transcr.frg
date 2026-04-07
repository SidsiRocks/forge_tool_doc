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

sig kao_chow_v1_init extends strand {
  kao_chow_v1_init_a : one name,
  kao_chow_v1_init_b : one name,
  kao_chow_v1_init_s : one name,
  kao_chow_v1_init_Kab : one skey,
  kao_chow_v1_init_Na : one text,
  kao_chow_v1_init_Nb : one text
}
pred exec_kao_chow_v1_init {
  all arbitrary_init_kao_chow_v1 : kao_chow_v1_init | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_init_kao_chow_v1.kao_chow_v1_init_a,arbitrary_init_kao_chow_v1.kao_chow_v1_init_s]] or generates [aStrand,getLTK[arbitrary_init_kao_chow_v1.kao_chow_v1_init_a,arbitrary_init_kao_chow_v1.kao_chow_v1_init_s]]
    }
    (generated_times.Timeslot).(arbitrary_init_kao_chow_v1.kao_chow_v1_init_Na) = arbitrary_init_kao_chow_v1.agent
    arbitrary_init_kao_chow_v1.kao_chow_v1_init_a != arbitrary_init_kao_chow_v1.kao_chow_v1_init_b
    arbitrary_init_kao_chow_v1.kao_chow_v1_init_a != arbitrary_init_kao_chow_v1.kao_chow_v1_init_s
    arbitrary_init_kao_chow_v1.kao_chow_v1_init_b != arbitrary_init_kao_chow_v1.kao_chow_v1_init_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_init_kao_chow_v1.kao_chow_v1_init_Na)->t0) in (arbitrary_init_kao_chow_v1.agent).generated_times
      t0+t1+t2 = sender.arbitrary_init_kao_chow_v1 + receiver.arbitrary_init_kao_chow_v1
      t0.sender = arbitrary_init_kao_chow_v1
      inds[((t0.data).components)] = 0+1+2
      let name_1  = (((t0.data).components))[0] | {
      let name_2  = (((t0.data).components))[1] | {
      let text_3  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_1 + 1->name_2 + 2->text_3
        name_1 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_a
        name_2 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_b
        text_3 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Na
      }}}

      t1.receiver = arbitrary_init_kao_chow_v1
      inds[((t1.data).components)] = 0+1+2
      let enc_4  = (((t1.data).components))[0] | {
      let enc_5  = (((t1.data).components))[1] | {
      let text_6  = (((t1.data).components))[2] | {
        ((t1.data).components) = 0->enc_4 + 1->enc_5 + 2->text_6
        learnt_term_by[getLTK[arbitrary_init_kao_chow_v1.kao_chow_v1_init_a,arbitrary_init_kao_chow_v1.kao_chow_v1_init_s],arbitrary_init_kao_chow_v1.agent,t1]
        inds[(enc_4).plaintext.components] = 0+1+2+3
        let name_11  = ((enc_4).plaintext.components)[0] | {
        let name_12  = ((enc_4).plaintext.components)[1] | {
        let text_13  = ((enc_4).plaintext.components)[2] | {
        let skey_14  = ((enc_4).plaintext.components)[3] | {
          (enc_4).plaintext.components = 0->name_11 + 1->name_12 + 2->text_13 + 3->skey_14
          name_11 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_a
          name_12 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_b
          text_13 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Na
          skey_14 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Kab
        }}}}
        (enc_4).encryptionKey = getLTK[arbitrary_init_kao_chow_v1.kao_chow_v1_init_a,arbitrary_init_kao_chow_v1.kao_chow_v1_init_s]
        learnt_term_by[arbitrary_init_kao_chow_v1.kao_chow_v1_init_Kab,arbitrary_init_kao_chow_v1.agent,t1]
        inds[(enc_5).plaintext.components] = 0
        let text_16  = ((enc_5).plaintext.components)[0] | {
          (enc_5).plaintext.components = 0->text_16
          text_16 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Na
        }
        (enc_5).encryptionKey = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Kab
        text_6 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Nb
      }}}

      t2.sender = arbitrary_init_kao_chow_v1
      inds[((t2.data)).plaintext.components] = 0
      let text_18  = (((t2.data)).plaintext.components)[0] | {
        ((t2.data)).plaintext.components = 0->text_18
        text_18 = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Nb
      }
      ((t2.data)).encryptionKey = arbitrary_init_kao_chow_v1.kao_chow_v1_init_Kab

    }}}
  }
}
sig kao_chow_v1_server extends strand {
  kao_chow_v1_server_a : one name,
  kao_chow_v1_server_b : one name,
  kao_chow_v1_server_s : one name,
  kao_chow_v1_server_Kab : one skey,
  kao_chow_v1_server_Na : one text,
  kao_chow_v1_server_Nb : one text
}
pred exec_kao_chow_v1_server {
  all arbitrary_server_kao_chow_v1 : kao_chow_v1_server | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_a,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]] or generates [aStrand,getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_a,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_b,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]] or generates [aStrand,getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_b,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]]
    }
    arbitrary_server_kao_chow_v1.kao_chow_v1_server_a != arbitrary_server_kao_chow_v1.kao_chow_v1_server_b
    arbitrary_server_kao_chow_v1.kao_chow_v1_server_a != arbitrary_server_kao_chow_v1.kao_chow_v1_server_s
    arbitrary_server_kao_chow_v1.kao_chow_v1_server_b != arbitrary_server_kao_chow_v1.kao_chow_v1_server_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_server_kao_chow_v1.kao_chow_v1_server_Kab)->t1) in (arbitrary_server_kao_chow_v1.agent).generated_times
      t0+t1 = sender.arbitrary_server_kao_chow_v1 + receiver.arbitrary_server_kao_chow_v1
      t0.receiver = arbitrary_server_kao_chow_v1
      inds[((t0.data).components)] = 0+1+2
      let name_19  = (((t0.data).components))[0] | {
      let name_20  = (((t0.data).components))[1] | {
      let text_21  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_19 + 1->name_20 + 2->text_21
        name_19 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_a
        name_20 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_b
        text_21 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_Na
      }}}

      t1.sender = arbitrary_server_kao_chow_v1
      inds[((t1.data).components)] = 0+1
      let enc_22  = (((t1.data).components))[0] | {
      let enc_23  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->enc_22 + 1->enc_23
        inds[(enc_22).plaintext.components] = 0+1+2+3
        let name_28  = ((enc_22).plaintext.components)[0] | {
        let name_29  = ((enc_22).plaintext.components)[1] | {
        let text_30  = ((enc_22).plaintext.components)[2] | {
        let skey_31  = ((enc_22).plaintext.components)[3] | {
          (enc_22).plaintext.components = 0->name_28 + 1->name_29 + 2->text_30 + 3->skey_31
          name_28 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_a
          name_29 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_b
          text_30 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_Na
          skey_31 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_Kab
        }}}}
        (enc_22).encryptionKey = getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_a,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]
        inds[(enc_23).plaintext.components] = 0+1+2+3
        let name_36  = ((enc_23).plaintext.components)[0] | {
        let name_37  = ((enc_23).plaintext.components)[1] | {
        let text_38  = ((enc_23).plaintext.components)[2] | {
        let skey_39  = ((enc_23).plaintext.components)[3] | {
          (enc_23).plaintext.components = 0->name_36 + 1->name_37 + 2->text_38 + 3->skey_39
          name_36 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_a
          name_37 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_b
          text_38 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_Na
          skey_39 = arbitrary_server_kao_chow_v1.kao_chow_v1_server_Kab
        }}}}
        (enc_23).encryptionKey = getLTK[arbitrary_server_kao_chow_v1.kao_chow_v1_server_b,arbitrary_server_kao_chow_v1.kao_chow_v1_server_s]
      }}

    }}
  }
}
sig kao_chow_v1_resp extends strand {
  kao_chow_v1_resp_a : one name,
  kao_chow_v1_resp_b : one name,
  kao_chow_v1_resp_s : one name,
  kao_chow_v1_resp_Kab : one skey,
  kao_chow_v1_resp_Na : one text,
  kao_chow_v1_resp_Nb : one text,
  kao_chow_v1_resp_msg : one mesg
}
pred exec_kao_chow_v1_resp {
  all arbitrary_resp_kao_chow_v1 : kao_chow_v1_resp | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b,arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s]] or generates [aStrand,getLTK[arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b,arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s]]
    }
    (generated_times.Timeslot).(arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Nb) = arbitrary_resp_kao_chow_v1.agent
    arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_a != arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b
    arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_a != arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s
    arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b != arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Nb)->t1) in (arbitrary_resp_kao_chow_v1.agent).generated_times
      t0+t1+t2 = sender.arbitrary_resp_kao_chow_v1 + receiver.arbitrary_resp_kao_chow_v1
      t0.receiver = arbitrary_resp_kao_chow_v1
      inds[((t0.data).components)] = 0+1
      let mesg_40  = (((t0.data).components))[0] | {
      let enc_41  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->mesg_40 + 1->enc_41
        mesg_40 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_msg
        learnt_term_by[getLTK[arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b,arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s],arbitrary_resp_kao_chow_v1.agent,t0]
        inds[(enc_41).plaintext.components] = 0+1+2+3
        let name_46  = ((enc_41).plaintext.components)[0] | {
        let name_47  = ((enc_41).plaintext.components)[1] | {
        let text_48  = ((enc_41).plaintext.components)[2] | {
        let skey_49  = ((enc_41).plaintext.components)[3] | {
          (enc_41).plaintext.components = 0->name_46 + 1->name_47 + 2->text_48 + 3->skey_49
          name_46 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_a
          name_47 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b
          text_48 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Na
          skey_49 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Kab
        }}}}
        (enc_41).encryptionKey = getLTK[arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_b,arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_s]
      }}

      t1.sender = arbitrary_resp_kao_chow_v1
      inds[((t1.data).components)] = 0+1+2
      let mesg_50  = (((t1.data).components))[0] | {
      let enc_51  = (((t1.data).components))[1] | {
      let text_52  = (((t1.data).components))[2] | {
        ((t1.data).components) = 0->mesg_50 + 1->enc_51 + 2->text_52
        mesg_50 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_msg
        inds[(enc_51).plaintext.components] = 0
        let text_54  = ((enc_51).plaintext.components)[0] | {
          (enc_51).plaintext.components = 0->text_54
          text_54 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Na
        }
        (enc_51).encryptionKey = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Kab
        text_52 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Nb
      }}}

      t2.receiver = arbitrary_resp_kao_chow_v1
      learnt_term_by[arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Kab,arbitrary_resp_kao_chow_v1.agent,t2]
      inds[((t2.data)).plaintext.components] = 0
      let text_56  = (((t2.data)).plaintext.components)[0] | {
        ((t2.data)).plaintext.components = 0->text_56
        text_56 = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Nb
      }
      ((t2.data)).encryptionKey = arbitrary_resp_kao_chow_v1.kao_chow_v1_resp_Kab

    }}}
  }
}
one sig skeleton_kao_chow_v1_0 {
  skeleton_kao_chow_v1_0_a : one name,
  skeleton_kao_chow_v1_0_b : one name,
  skeleton_kao_chow_v1_0_s : one name,
  skeleton_kao_chow_v1_0_Kab : one skey,
  skeleton_kao_chow_v1_0_Na : one text,
  skeleton_kao_chow_v1_0_Nb : one text
}
pred constrain_skeleton_kao_chow_v1_0 {
  some skeleton_init_0_strand_0 : kao_chow_v1_init | {
    skeleton_init_0_strand_0.kao_chow_v1_init_a = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_a
    skeleton_init_0_strand_0.kao_chow_v1_init_b = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_b
    skeleton_init_0_strand_0.kao_chow_v1_init_s = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_s
    skeleton_init_0_strand_0.kao_chow_v1_init_Kab = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Kab
    skeleton_init_0_strand_0.kao_chow_v1_init_Na = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Na
    skeleton_init_0_strand_0.kao_chow_v1_init_Nb = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Nb
  }
  some skeleton_server_0_strand_1 : kao_chow_v1_server | {
    skeleton_server_0_strand_1.kao_chow_v1_server_a = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_a
    skeleton_server_0_strand_1.kao_chow_v1_server_b = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_b
    skeleton_server_0_strand_1.kao_chow_v1_server_s = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_s
    skeleton_server_0_strand_1.kao_chow_v1_server_Kab = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Kab
    skeleton_server_0_strand_1.kao_chow_v1_server_Na = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Na
  }
  some skeleton_resp_0_strand_2 : kao_chow_v1_resp | {
    skeleton_resp_0_strand_2.kao_chow_v1_resp_a = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_a
    skeleton_resp_0_strand_2.kao_chow_v1_resp_b = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_b
    skeleton_resp_0_strand_2.kao_chow_v1_resp_s = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_s
    skeleton_resp_0_strand_2.kao_chow_v1_resp_Kab = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Kab
    skeleton_resp_0_strand_2.kao_chow_v1_resp_Na = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Na
    skeleton_resp_0_strand_2.kao_chow_v1_resp_Nb = skeleton_kao_chow_v1_0.skeleton_kao_chow_v1_0_Nb
  }
}
one sig skeleton_attack_1 {
  skeleton_attack_1_a : one name,
  skeleton_attack_1_b : one name,
  skeleton_attack_1_s : one name,
  skeleton_attack_1_Kab : one skey,
  skeleton_attack_1_Na : one text,
  skeleton_attack_1_Nb1 : one text,
  skeleton_attack_1_Nb2 : one text,
  skeleton_attack_1_msg : one mesg,
  skeleton_attack_1_init_strand : one kao_chow_v1_init,
  skeleton_attack_1_server_strand : one kao_chow_v1_server,
  skeleton_attack_1_resp1_strand : one kao_chow_v1_resp,
  skeleton_attack_1_resp2_strand : one kao_chow_v1_resp
}
pred constrain_skeleton_attack_1_attack_run {
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
    t_0.sender = skeleton_attack_1.skeleton_attack_1_init_strand
    inds[(t_0.data.components)] = 0+1+2
    let name_57  = ((t_0.data.components))[0] | {
    let name_58  = ((t_0.data.components))[1] | {
    let text_59  = ((t_0.data.components))[2] | {
      (t_0.data.components) = 0->name_57 + 1->name_58 + 2->text_59
      name_57 = skeleton_attack_1.skeleton_attack_1_a
      name_58 = skeleton_attack_1.skeleton_attack_1_b
      text_59 = skeleton_attack_1.skeleton_attack_1_Na
    }}}

    t_1.receiver = skeleton_attack_1.skeleton_attack_1_server_strand
    inds[(t_1.data.components)] = 0+1+2
    let name_60  = ((t_1.data.components))[0] | {
    let name_61  = ((t_1.data.components))[1] | {
    let text_62  = ((t_1.data.components))[2] | {
      (t_1.data.components) = 0->name_60 + 1->name_61 + 2->text_62
      name_60 = skeleton_attack_1.skeleton_attack_1_a
      name_61 = skeleton_attack_1.skeleton_attack_1_b
      text_62 = skeleton_attack_1.skeleton_attack_1_Na
    }}}

    t_2.sender = skeleton_attack_1.skeleton_attack_1_server_strand
    inds[(t_2.data.components)] = 0+1
    let enc_63  = ((t_2.data.components))[0] | {
    let enc_64  = ((t_2.data.components))[1] | {
      (t_2.data.components) = 0->enc_63 + 1->enc_64
      inds[(enc_63).plaintext.components] = 0+1+2+3
      let name_69  = ((enc_63).plaintext.components)[0] | {
      let name_70  = ((enc_63).plaintext.components)[1] | {
      let text_71  = ((enc_63).plaintext.components)[2] | {
      let skey_72  = ((enc_63).plaintext.components)[3] | {
        (enc_63).plaintext.components = 0->name_69 + 1->name_70 + 2->text_71 + 3->skey_72
        name_69 = skeleton_attack_1.skeleton_attack_1_a
        name_70 = skeleton_attack_1.skeleton_attack_1_b
        text_71 = skeleton_attack_1.skeleton_attack_1_Na
        skey_72 = skeleton_attack_1.skeleton_attack_1_Kab
      }}}}
      (enc_63).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
      inds[(enc_64).plaintext.components] = 0+1+2+3
      let name_77  = ((enc_64).plaintext.components)[0] | {
      let name_78  = ((enc_64).plaintext.components)[1] | {
      let text_79  = ((enc_64).plaintext.components)[2] | {
      let skey_80  = ((enc_64).plaintext.components)[3] | {
        (enc_64).plaintext.components = 0->name_77 + 1->name_78 + 2->text_79 + 3->skey_80
        name_77 = skeleton_attack_1.skeleton_attack_1_a
        name_78 = skeleton_attack_1.skeleton_attack_1_b
        text_79 = skeleton_attack_1.skeleton_attack_1_Na
        skey_80 = skeleton_attack_1.skeleton_attack_1_Kab
      }}}}
      (enc_64).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
    }}

    t_3.receiver = skeleton_attack_1.skeleton_attack_1_resp1_strand
    inds[(t_3.data.components)] = 0+1
    let mesg_81  = ((t_3.data.components))[0] | {
    let enc_82  = ((t_3.data.components))[1] | {
      (t_3.data.components) = 0->mesg_81 + 1->enc_82
      mesg_81 = skeleton_attack_1.skeleton_attack_1_msg
      inds[(enc_82).plaintext.components] = 0+1+2+3
      let name_87  = ((enc_82).plaintext.components)[0] | {
      let name_88  = ((enc_82).plaintext.components)[1] | {
      let text_89  = ((enc_82).plaintext.components)[2] | {
      let skey_90  = ((enc_82).plaintext.components)[3] | {
        (enc_82).plaintext.components = 0->name_87 + 1->name_88 + 2->text_89 + 3->skey_90
        name_87 = skeleton_attack_1.skeleton_attack_1_a
        name_88 = skeleton_attack_1.skeleton_attack_1_b
        text_89 = skeleton_attack_1.skeleton_attack_1_Na
        skey_90 = skeleton_attack_1.skeleton_attack_1_Kab
      }}}}
      (enc_82).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
    }}

    t_4.sender = skeleton_attack_1.skeleton_attack_1_resp1_strand
    inds[(t_4.data.components)] = 0+1+2
    let mesg_91  = ((t_4.data.components))[0] | {
    let enc_92  = ((t_4.data.components))[1] | {
    let text_93  = ((t_4.data.components))[2] | {
      (t_4.data.components) = 0->mesg_91 + 1->enc_92 + 2->text_93
      mesg_91 = skeleton_attack_1.skeleton_attack_1_msg
      inds[(enc_92).plaintext.components] = 0
      let text_95  = ((enc_92).plaintext.components)[0] | {
        (enc_92).plaintext.components = 0->text_95
        text_95 = skeleton_attack_1.skeleton_attack_1_Na
      }
      (enc_92).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab
      text_93 = skeleton_attack_1.skeleton_attack_1_Nb1
    }}}

    t_5.receiver = skeleton_attack_1.skeleton_attack_1_init_strand
    inds[(t_5.data.components)] = 0+1+2
    let enc_96  = ((t_5.data.components))[0] | {
    let enc_97  = ((t_5.data.components))[1] | {
    let text_98  = ((t_5.data.components))[2] | {
      (t_5.data.components) = 0->enc_96 + 1->enc_97 + 2->text_98
      inds[(enc_96).plaintext.components] = 0+1+2+3
      let name_103  = ((enc_96).plaintext.components)[0] | {
      let name_104  = ((enc_96).plaintext.components)[1] | {
      let text_105  = ((enc_96).plaintext.components)[2] | {
      let skey_106  = ((enc_96).plaintext.components)[3] | {
        (enc_96).plaintext.components = 0->name_103 + 1->name_104 + 2->text_105 + 3->skey_106
        name_103 = skeleton_attack_1.skeleton_attack_1_a
        name_104 = skeleton_attack_1.skeleton_attack_1_b
        text_105 = skeleton_attack_1.skeleton_attack_1_Na
        skey_106 = skeleton_attack_1.skeleton_attack_1_Kab
      }}}}
      (enc_96).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
      inds[(enc_97).plaintext.components] = 0
      let text_108  = ((enc_97).plaintext.components)[0] | {
        (enc_97).plaintext.components = 0->text_108
        text_108 = skeleton_attack_1.skeleton_attack_1_Na
      }
      (enc_97).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab
      text_98 = skeleton_attack_1.skeleton_attack_1_Nb1
    }}}

    t_6.sender = skeleton_attack_1.skeleton_attack_1_init_strand
    inds[((t_6.data)).plaintext.components] = 0
    let text_110  = (((t_6.data)).plaintext.components)[0] | {
      ((t_6.data)).plaintext.components = 0->text_110
      text_110 = skeleton_attack_1.skeleton_attack_1_Nb1
    }
    ((t_6.data)).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab

    t_7.receiver = skeleton_attack_1.skeleton_attack_1_resp1_strand
    inds[((t_7.data)).plaintext.components] = 0
    let text_112  = (((t_7.data)).plaintext.components)[0] | {
      ((t_7.data)).plaintext.components = 0->text_112
      text_112 = skeleton_attack_1.skeleton_attack_1_Nb1
    }
    ((t_7.data)).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab

    t_8.receiver = skeleton_attack_1.skeleton_attack_1_resp2_strand
    inds[(t_8.data.components)] = 0+1
    let mesg_113  = ((t_8.data.components))[0] | {
    let enc_114  = ((t_8.data.components))[1] | {
      (t_8.data.components) = 0->mesg_113 + 1->enc_114
      mesg_113 = skeleton_attack_1.skeleton_attack_1_msg
      inds[(enc_114).plaintext.components] = 0+1+2+3
      let name_119  = ((enc_114).plaintext.components)[0] | {
      let name_120  = ((enc_114).plaintext.components)[1] | {
      let text_121  = ((enc_114).plaintext.components)[2] | {
      let skey_122  = ((enc_114).plaintext.components)[3] | {
        (enc_114).plaintext.components = 0->name_119 + 1->name_120 + 2->text_121 + 3->skey_122
        name_119 = skeleton_attack_1.skeleton_attack_1_a
        name_120 = skeleton_attack_1.skeleton_attack_1_b
        text_121 = skeleton_attack_1.skeleton_attack_1_Na
        skey_122 = skeleton_attack_1.skeleton_attack_1_Kab
      }}}}
      (enc_114).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
    }}

    t_9.sender = skeleton_attack_1.skeleton_attack_1_resp2_strand
    inds[(t_9.data.components)] = 0+1+2
    let mesg_123  = ((t_9.data.components))[0] | {
    let enc_124  = ((t_9.data.components))[1] | {
    let text_125  = ((t_9.data.components))[2] | {
      (t_9.data.components) = 0->mesg_123 + 1->enc_124 + 2->text_125
      mesg_123 = skeleton_attack_1.skeleton_attack_1_msg
      inds[(enc_124).plaintext.components] = 0
      let text_127  = ((enc_124).plaintext.components)[0] | {
        (enc_124).plaintext.components = 0->text_127
        text_127 = skeleton_attack_1.skeleton_attack_1_Na
      }
      (enc_124).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab
      text_125 = skeleton_attack_1.skeleton_attack_1_Nb2
    }}}

    t_10.receiver = skeleton_attack_1.skeleton_attack_1_resp2_strand
    inds[((t_10.data)).plaintext.components] = 0
    let text_129  = (((t_10.data)).plaintext.components)[0] | {
      ((t_10.data)).plaintext.components = 0->text_129
      text_129 = skeleton_attack_1.skeleton_attack_1_Nb2
    }
    ((t_10.data)).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab

  }}}}}}}}}}}
}
pred constrain_skeleton_attack_1 {
  some skeleton_init_1_strand_0 : kao_chow_v1_init | {
    skeleton_init_1_strand_0.kao_chow_v1_init_a = skeleton_attack_1.skeleton_attack_1_a
    skeleton_init_1_strand_0.kao_chow_v1_init_b = skeleton_attack_1.skeleton_attack_1_b
    skeleton_init_1_strand_0.kao_chow_v1_init_s = skeleton_attack_1.skeleton_attack_1_s
    skeleton_init_1_strand_0.kao_chow_v1_init_Kab = skeleton_attack_1.skeleton_attack_1_Kab
    skeleton_init_1_strand_0.kao_chow_v1_init_Na = skeleton_attack_1.skeleton_attack_1_Na
    skeleton_init_1_strand_0.kao_chow_v1_init_Nb = skeleton_attack_1.skeleton_attack_1_Nb1
  }
  some skeleton_server_1_strand_1 : kao_chow_v1_server | {
    skeleton_server_1_strand_1.kao_chow_v1_server_a = skeleton_attack_1.skeleton_attack_1_a
    skeleton_server_1_strand_1.kao_chow_v1_server_b = skeleton_attack_1.skeleton_attack_1_b
    skeleton_server_1_strand_1.kao_chow_v1_server_s = skeleton_attack_1.skeleton_attack_1_s
    skeleton_server_1_strand_1.kao_chow_v1_server_Kab = skeleton_attack_1.skeleton_attack_1_Kab
    skeleton_server_1_strand_1.kao_chow_v1_server_Na = skeleton_attack_1.skeleton_attack_1_Na
  }
  some skeleton_resp_1_strand_2 : kao_chow_v1_resp | {
    skeleton_resp_1_strand_2.kao_chow_v1_resp_a = skeleton_attack_1.skeleton_attack_1_a
    skeleton_resp_1_strand_2.kao_chow_v1_resp_b = skeleton_attack_1.skeleton_attack_1_b
    skeleton_resp_1_strand_2.kao_chow_v1_resp_s = skeleton_attack_1.skeleton_attack_1_s
    skeleton_resp_1_strand_2.kao_chow_v1_resp_Kab = skeleton_attack_1.skeleton_attack_1_Kab
    skeleton_resp_1_strand_2.kao_chow_v1_resp_Na = skeleton_attack_1.skeleton_attack_1_Na
    skeleton_resp_1_strand_2.kao_chow_v1_resp_Nb = skeleton_attack_1.skeleton_attack_1_Nb1
  }
  some skeleton_resp_1_strand_3 : kao_chow_v1_resp | {
    skeleton_resp_1_strand_3.kao_chow_v1_resp_a = skeleton_attack_1.skeleton_attack_1_a
    skeleton_resp_1_strand_3.kao_chow_v1_resp_b = skeleton_attack_1.skeleton_attack_1_b
    skeleton_resp_1_strand_3.kao_chow_v1_resp_s = skeleton_attack_1.skeleton_attack_1_s
    skeleton_resp_1_strand_3.kao_chow_v1_resp_Kab = skeleton_attack_1.skeleton_attack_1_Kab
    skeleton_resp_1_strand_3.kao_chow_v1_resp_Na = skeleton_attack_1.skeleton_attack_1_Na
    skeleton_resp_1_strand_3.kao_chow_v1_resp_Nb = skeleton_attack_1.skeleton_attack_1_Nb2
  }
  constrain_skeleton_attack_1_attack_run
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5
  text = `text0 + `text1
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1+2+3+4+5) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  kao_chow_v1_init = `kao_chow_v1_init0
  kao_chow_v1_server = `kao_chow_v1_server0
  kao_chow_v1_resp = `kao_chow_v1_resp0
  AttackerStrand = `AttackerStrand0
  strand = kao_chow_v1_init + kao_chow_v1_server + kao_chow_v1_resp + AttackerStrand
}
inst attack_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7 + `Ciphertext8 + `Ciphertext9 + `Ciphertext10
  text = `text0 + `text1 + `text2
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10 + `tuple11 + `tuple12 + `tuple13 + `tuple14
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7 + `Timeslot8 + `Timeslot9 + `Timeslot10

  components in tuple -> (0+1+2+3+4+5) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7 + `Timeslot7->`Timeslot8 + `Timeslot8->`Timeslot9 + `Timeslot9->`Timeslot10
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  kao_chow_v1_init = `kao_chow_v1_init0
  kao_chow_v1_server = `kao_chow_v1_server0
  kao_chow_v1_resp = `kao_chow_v1_resp0 + `kao_chow_v1_resp1
  AttackerStrand = `AttackerStrand0
  strand = kao_chow_v1_init + kao_chow_v1_server + kao_chow_v1_resp + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

kao_chow_v1_honest_run: run {
    wellformed

    exec_kao_chow_v1_init
    exec_kao_chow_v1_server
    exec_kao_chow_v1_resp

    // constrain_skeleton_kao_chow_v1_0
    constrain_skeleton_attack_1

    kao_chow_v1_init.kao_chow_v1_init_b != Attacker
    kao_chow_v1_init.kao_chow_v1_init_s != Attacker
    kao_chow_v1_init.kao_chow_v1_init_a != Attacker

    kao_chow_v1_server.kao_chow_v1_server_b != Attacker
    kao_chow_v1_server.kao_chow_v1_server_a != Attacker
    kao_chow_v1_server.kao_chow_v1_server_s != Attacker

    kao_chow_v1_resp.kao_chow_v1_resp_a != Attacker
    kao_chow_v1_resp.kao_chow_v1_resp_s != Attacker
    kao_chow_v1_resp.kao_chow_v1_resp_b != Attacker

    kao_chow_v1_init.agent != kao_chow_v1_server.agent
    kao_chow_v1_init.agent != kao_chow_v1_resp.agent
    kao_chow_v1_server.agent != kao_chow_v1_resp.agent

    not Attacker in (kao_chow_v1_init + kao_chow_v1_server + kao_chow_v1_resp).agent

    
    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

    kao_chow_v1_server.kao_chow_v1_server_Kab
    in Attacker.learned_times.Timeslot

    all x: name, y: name | kao_chow_v1_server.kao_chow_v1_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    // honest_run_bounds
    attack_bounds
}