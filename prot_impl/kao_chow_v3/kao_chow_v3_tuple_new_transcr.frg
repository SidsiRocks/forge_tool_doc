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

sig kao_chow_v3_init extends strand {
  kao_chow_v3_init_a : one name,
  kao_chow_v3_init_b : one name,
  kao_chow_v3_init_s : one name,
  kao_chow_v3_init_Kab : one skey,
  kao_chow_v3_init_Kt : one skey,
  kao_chow_v3_init_Na : one text,
  kao_chow_v3_init_Nb : one text,
  kao_chow_v3_init_msg1 : one mesg
}
pred exec_kao_chow_v3_init {
  all arbitrary_init_kao_chow_v3 : kao_chow_v3_init | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_init_kao_chow_v3.kao_chow_v3_init_a,arbitrary_init_kao_chow_v3.kao_chow_v3_init_s]] or generates [aStrand,getLTK[arbitrary_init_kao_chow_v3.kao_chow_v3_init_a,arbitrary_init_kao_chow_v3.kao_chow_v3_init_s]]
    }
    (generated_times.Timeslot).(arbitrary_init_kao_chow_v3.kao_chow_v3_init_Na) = arbitrary_init_kao_chow_v3.agent
    arbitrary_init_kao_chow_v3.kao_chow_v3_init_a != arbitrary_init_kao_chow_v3.kao_chow_v3_init_b
    arbitrary_init_kao_chow_v3.kao_chow_v3_init_a != arbitrary_init_kao_chow_v3.kao_chow_v3_init_s
    arbitrary_init_kao_chow_v3.kao_chow_v3_init_b != arbitrary_init_kao_chow_v3.kao_chow_v3_init_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_init_kao_chow_v3.kao_chow_v3_init_Na)->t0) in (arbitrary_init_kao_chow_v3.agent).generated_times
      t0+t1+t2 = sender.arbitrary_init_kao_chow_v3 + receiver.arbitrary_init_kao_chow_v3
      t0.sender = arbitrary_init_kao_chow_v3
      inds[((t0.data).components)] = 0+1+2
      let name_1  = (((t0.data).components))[0] | {
      let name_2  = (((t0.data).components))[1] | {
      let text_3  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_1 + 1->name_2 + 2->text_3
        name_1 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_a
        name_2 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_b
        text_3 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Na
      }}}

      t1.receiver = arbitrary_init_kao_chow_v3
      inds[((t1.data).components)] = 0+1+2+3
      let enc_4  = (((t1.data).components))[0] | {
      let enc_5  = (((t1.data).components))[1] | {
      let text_6  = (((t1.data).components))[2] | {
      let mesg_7  = (((t1.data).components))[3] | {
        ((t1.data).components) = 0->enc_4 + 1->enc_5 + 2->text_6 + 3->mesg_7
        learnt_term_by[getLTK[arbitrary_init_kao_chow_v3.kao_chow_v3_init_a,arbitrary_init_kao_chow_v3.kao_chow_v3_init_s],arbitrary_init_kao_chow_v3.agent,t1]
        inds[(enc_4).plaintext.components] = 0+1+2+3+4
        let name_13  = ((enc_4).plaintext.components)[0] | {
        let name_14  = ((enc_4).plaintext.components)[1] | {
        let text_15  = ((enc_4).plaintext.components)[2] | {
        let skey_16  = ((enc_4).plaintext.components)[3] | {
        let skey_17  = ((enc_4).plaintext.components)[4] | {
          (enc_4).plaintext.components = 0->name_13 + 1->name_14 + 2->text_15 + 3->skey_16 + 4->skey_17
          name_13 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_a
          name_14 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_b
          text_15 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Na
          skey_16 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kab
          skey_17 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kt
        }}}}}
        (enc_4).encryptionKey = getLTK[arbitrary_init_kao_chow_v3.kao_chow_v3_init_a,arbitrary_init_kao_chow_v3.kao_chow_v3_init_s]
        learnt_term_by[arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kt,arbitrary_init_kao_chow_v3.agent,t1]
        inds[(enc_5).plaintext.components] = 0+1
        let text_20  = ((enc_5).plaintext.components)[0] | {
        let skey_21  = ((enc_5).plaintext.components)[1] | {
          (enc_5).plaintext.components = 0->text_20 + 1->skey_21
          text_20 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Na
          skey_21 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kab
        }}
        (enc_5).encryptionKey = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kt
        text_6 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Nb
        mesg_7 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_msg1
      }}}}

      t2.sender = arbitrary_init_kao_chow_v3
      inds[((t2.data).components)] = 0+1
      let enc_22  = (((t2.data).components))[0] | {
      let mesg_23  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->enc_22 + 1->mesg_23
        inds[(enc_22).plaintext.components] = 0+1
        let text_26  = ((enc_22).plaintext.components)[0] | {
        let skey_27  = ((enc_22).plaintext.components)[1] | {
          (enc_22).plaintext.components = 0->text_26 + 1->skey_27
          text_26 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Nb
          skey_27 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kab
        }}
        (enc_22).encryptionKey = arbitrary_init_kao_chow_v3.kao_chow_v3_init_Kt
        mesg_23 = arbitrary_init_kao_chow_v3.kao_chow_v3_init_msg1
      }}

    }}}
  }
}
sig kao_chow_v3_server extends strand {
  kao_chow_v3_server_a : one name,
  kao_chow_v3_server_b : one name,
  kao_chow_v3_server_s : one name,
  kao_chow_v3_server_Kab : one skey,
  kao_chow_v3_server_Kt : one skey,
  kao_chow_v3_server_Na : one text
}
pred exec_kao_chow_v3_server {
  all arbitrary_server_kao_chow_v3 : kao_chow_v3_server | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_a,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]] or generates [aStrand,getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_a,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_b,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]] or generates [aStrand,getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_b,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]]
    }
    (generated_times.Timeslot).(arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kab) = arbitrary_server_kao_chow_v3.agent
    (generated_times.Timeslot).(arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kt) = arbitrary_server_kao_chow_v3.agent
    arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kab != arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kt
    arbitrary_server_kao_chow_v3.kao_chow_v3_server_a != arbitrary_server_kao_chow_v3.kao_chow_v3_server_b
    arbitrary_server_kao_chow_v3.kao_chow_v3_server_a != arbitrary_server_kao_chow_v3.kao_chow_v3_server_s
    arbitrary_server_kao_chow_v3.kao_chow_v3_server_b != arbitrary_server_kao_chow_v3.kao_chow_v3_server_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kab)->t1 + (arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kt)->t1) in (arbitrary_server_kao_chow_v3.agent).generated_times
      t0+t1 = sender.arbitrary_server_kao_chow_v3 + receiver.arbitrary_server_kao_chow_v3
      t0.receiver = arbitrary_server_kao_chow_v3
      inds[((t0.data).components)] = 0+1+2
      let name_28  = (((t0.data).components))[0] | {
      let name_29  = (((t0.data).components))[1] | {
      let text_30  = (((t0.data).components))[2] | {
        ((t0.data).components) = 0->name_28 + 1->name_29 + 2->text_30
        name_28 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_a
        name_29 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_b
        text_30 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Na
      }}}

      t1.sender = arbitrary_server_kao_chow_v3
      inds[((t1.data).components)] = 0+1
      let enc_31  = (((t1.data).components))[0] | {
      let enc_32  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->enc_31 + 1->enc_32
        inds[(enc_31).plaintext.components] = 0+1+2+3+4
        let name_38  = ((enc_31).plaintext.components)[0] | {
        let name_39  = ((enc_31).plaintext.components)[1] | {
        let text_40  = ((enc_31).plaintext.components)[2] | {
        let skey_41  = ((enc_31).plaintext.components)[3] | {
        let skey_42  = ((enc_31).plaintext.components)[4] | {
          (enc_31).plaintext.components = 0->name_38 + 1->name_39 + 2->text_40 + 3->skey_41 + 4->skey_42
          name_38 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_a
          name_39 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_b
          text_40 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Na
          skey_41 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kab
          skey_42 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kt
        }}}}}
        (enc_31).encryptionKey = getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_a,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]
        inds[(enc_32).plaintext.components] = 0+1+2+3+4
        let name_48  = ((enc_32).plaintext.components)[0] | {
        let name_49  = ((enc_32).plaintext.components)[1] | {
        let text_50  = ((enc_32).plaintext.components)[2] | {
        let skey_51  = ((enc_32).plaintext.components)[3] | {
        let skey_52  = ((enc_32).plaintext.components)[4] | {
          (enc_32).plaintext.components = 0->name_48 + 1->name_49 + 2->text_50 + 3->skey_51 + 4->skey_52
          name_48 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_a
          name_49 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_b
          text_50 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Na
          skey_51 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kab
          skey_52 = arbitrary_server_kao_chow_v3.kao_chow_v3_server_Kt
        }}}}}
        (enc_32).encryptionKey = getLTK[arbitrary_server_kao_chow_v3.kao_chow_v3_server_b,arbitrary_server_kao_chow_v3.kao_chow_v3_server_s]
      }}

    }}
  }
}
sig kao_chow_v3_resp extends strand {
  kao_chow_v3_resp_a : one name,
  kao_chow_v3_resp_b : one name,
  kao_chow_v3_resp_s : one name,
  kao_chow_v3_resp_Kab : one skey,
  kao_chow_v3_resp_Kt : one skey,
  kao_chow_v3_resp_Na : one text,
  kao_chow_v3_resp_Nb : one text,
  kao_chow_v3_resp_Ta : one text,
  kao_chow_v3_resp_msg2 : one mesg
}
pred exec_kao_chow_v3_resp {
  all arbitrary_resp_kao_chow_v3 : kao_chow_v3_resp | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s]] or generates [aStrand,getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s]]
    }
    (generated_times.Timeslot).(arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Nb) = arbitrary_resp_kao_chow_v3.agent
    (generated_times.Timeslot).(arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Ta) = arbitrary_resp_kao_chow_v3.agent
    arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Nb != arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Ta
    arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_a != arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b
    arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_a != arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s
    arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b != arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Nb)->t1 + (arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Ta)->t1) in (arbitrary_resp_kao_chow_v3.agent).generated_times
      t0+t1+t2 = sender.arbitrary_resp_kao_chow_v3 + receiver.arbitrary_resp_kao_chow_v3
      t0.receiver = arbitrary_resp_kao_chow_v3
      inds[((t0.data).components)] = 0+1
      let mesg_53  = (((t0.data).components))[0] | {
      let enc_54  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->mesg_53 + 1->enc_54
        mesg_53 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_msg2
        learnt_term_by[getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s],arbitrary_resp_kao_chow_v3.agent,t0]
        inds[(enc_54).plaintext.components] = 0+1+2+3+4
        let name_60  = ((enc_54).plaintext.components)[0] | {
        let name_61  = ((enc_54).plaintext.components)[1] | {
        let text_62  = ((enc_54).plaintext.components)[2] | {
        let skey_63  = ((enc_54).plaintext.components)[3] | {
        let skey_64  = ((enc_54).plaintext.components)[4] | {
          (enc_54).plaintext.components = 0->name_60 + 1->name_61 + 2->text_62 + 3->skey_63 + 4->skey_64
          name_60 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_a
          name_61 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b
          text_62 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Na
          skey_63 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kab
          skey_64 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kt
        }}}}}
        (enc_54).encryptionKey = getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s]
      }}

      t1.sender = arbitrary_resp_kao_chow_v3
      inds[((t1.data).components)] = 0+1+2+3
      let mesg_65  = (((t1.data).components))[0] | {
      let enc_66  = (((t1.data).components))[1] | {
      let text_67  = (((t1.data).components))[2] | {
      let enc_68  = (((t1.data).components))[3] | {
        ((t1.data).components) = 0->mesg_65 + 1->enc_66 + 2->text_67 + 3->enc_68
        mesg_65 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_msg2
        inds[(enc_66).plaintext.components] = 0+1
        let text_71  = ((enc_66).plaintext.components)[0] | {
        let skey_72  = ((enc_66).plaintext.components)[1] | {
          (enc_66).plaintext.components = 0->text_71 + 1->skey_72
          text_71 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Na
          skey_72 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kab
        }}
        (enc_66).encryptionKey = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kt
        text_67 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Nb
        inds[(enc_68).plaintext.components] = 0+1+2+3
        let name_77  = ((enc_68).plaintext.components)[0] | {
        let name_78  = ((enc_68).plaintext.components)[1] | {
        let text_79  = ((enc_68).plaintext.components)[2] | {
        let skey_80  = ((enc_68).plaintext.components)[3] | {
          (enc_68).plaintext.components = 0->name_77 + 1->name_78 + 2->text_79 + 3->skey_80
          name_77 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_a
          name_78 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b
          text_79 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Ta
          skey_80 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kab
        }}}}
        (enc_68).encryptionKey = getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s]
      }}}}

      t2.receiver = arbitrary_resp_kao_chow_v3
      inds[((t2.data).components)] = 0+1
      let enc_81  = (((t2.data).components))[0] | {
      let enc_82  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->enc_81 + 1->enc_82
        learnt_term_by[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kt,arbitrary_resp_kao_chow_v3.agent,t2]
        inds[(enc_81).plaintext.components] = 0+1
        let text_85  = ((enc_81).plaintext.components)[0] | {
        let skey_86  = ((enc_81).plaintext.components)[1] | {
          (enc_81).plaintext.components = 0->text_85 + 1->skey_86
          text_85 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Nb
          skey_86 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kab
        }}
        (enc_81).encryptionKey = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kt
        learnt_term_by[getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s],arbitrary_resp_kao_chow_v3.agent,t2]
        inds[(enc_82).plaintext.components] = 0+1+2+3
        let name_91  = ((enc_82).plaintext.components)[0] | {
        let name_92  = ((enc_82).plaintext.components)[1] | {
        let text_93  = ((enc_82).plaintext.components)[2] | {
        let skey_94  = ((enc_82).plaintext.components)[3] | {
          (enc_82).plaintext.components = 0->name_91 + 1->name_92 + 2->text_93 + 3->skey_94
          name_91 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_a
          name_92 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b
          text_93 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Ta
          skey_94 = arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_Kab
        }}}}
        (enc_82).encryptionKey = getLTK[arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_b,arbitrary_resp_kao_chow_v3.kao_chow_v3_resp_s]
      }}

    }}}
  }
}
one sig skeleton_kao_chow_v3_0 {
  skeleton_kao_chow_v3_0_a : one name,
  skeleton_kao_chow_v3_0_b : one name,
  skeleton_kao_chow_v3_0_s : one name,
  skeleton_kao_chow_v3_0_Kab : one skey,
  skeleton_kao_chow_v3_0_Kt : one skey,
  skeleton_kao_chow_v3_0_Na : one text,
  skeleton_kao_chow_v3_0_Nb : one text,
  skeleton_kao_chow_v3_0_Ta : one text,
  skeleton_kao_chow_v3_0_msg1 : one mesg,
  skeleton_kao_chow_v3_0_msg2 : one mesg,
  skeleton_kao_chow_v3_0_init : one kao_chow_v3_init,
  skeleton_kao_chow_v3_0_server : one kao_chow_v3_server,
  skeleton_kao_chow_v3_0_resp : one kao_chow_v3_resp
}
pred constrain_skeleton_kao_chow_v3_0_honest_run {
  some t_0 : Timeslot {
  some t_1 : t_0.(^next) {
  some t_2 : t_1.(^next) {
  some t_3 : t_2.(^next) {
  some t_4 : t_3.(^next) {
  some t_5 : t_4.(^next) {
  some t_6 : t_5.(^next) {
  some t_7 : t_6.(^next) {
    t_0.sender = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_init
    inds[(t_0.data.components)] = 0+1+2
    let name_95  = ((t_0.data.components))[0] | {
    let name_96  = ((t_0.data.components))[1] | {
    let text_97  = ((t_0.data.components))[2] | {
      (t_0.data.components) = 0->name_95 + 1->name_96 + 2->text_97
      name_95 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
      name_96 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
      text_97 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
    }}}

    t_1.receiver = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_server
    inds[(t_1.data.components)] = 0+1+2
    let name_98  = ((t_1.data.components))[0] | {
    let name_99  = ((t_1.data.components))[1] | {
    let text_100  = ((t_1.data.components))[2] | {
      (t_1.data.components) = 0->name_98 + 1->name_99 + 2->text_100
      name_98 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
      name_99 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
      text_100 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
    }}}

    t_2.sender = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_server
    inds[(t_2.data.components)] = 0+1
    let enc_101  = ((t_2.data.components))[0] | {
    let enc_102  = ((t_2.data.components))[1] | {
      (t_2.data.components) = 0->enc_101 + 1->enc_102
      inds[(enc_101).plaintext.components] = 0+1+2+3+4
      let name_108  = ((enc_101).plaintext.components)[0] | {
      let name_109  = ((enc_101).plaintext.components)[1] | {
      let text_110  = ((enc_101).plaintext.components)[2] | {
      let skey_111  = ((enc_101).plaintext.components)[3] | {
      let skey_112  = ((enc_101).plaintext.components)[4] | {
        (enc_101).plaintext.components = 0->name_108 + 1->name_109 + 2->text_110 + 3->skey_111 + 4->skey_112
        name_108 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_109 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_110 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_111 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
        skey_112 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      }}}}}
      (enc_101).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
      inds[(enc_102).plaintext.components] = 0+1+2+3+4
      let name_118  = ((enc_102).plaintext.components)[0] | {
      let name_119  = ((enc_102).plaintext.components)[1] | {
      let text_120  = ((enc_102).plaintext.components)[2] | {
      let skey_121  = ((enc_102).plaintext.components)[3] | {
      let skey_122  = ((enc_102).plaintext.components)[4] | {
        (enc_102).plaintext.components = 0->name_118 + 1->name_119 + 2->text_120 + 3->skey_121 + 4->skey_122
        name_118 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_119 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_120 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_121 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
        skey_122 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      }}}}}
      (enc_102).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
    }}

    t_3.receiver = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_resp
    inds[(t_3.data.components)] = 0+1
    let mesg_123  = ((t_3.data.components))[0] | {
    let enc_124  = ((t_3.data.components))[1] | {
      (t_3.data.components) = 0->mesg_123 + 1->enc_124
      mesg_123 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_msg2
      inds[(enc_124).plaintext.components] = 0+1+2+3+4
      let name_130  = ((enc_124).plaintext.components)[0] | {
      let name_131  = ((enc_124).plaintext.components)[1] | {
      let text_132  = ((enc_124).plaintext.components)[2] | {
      let skey_133  = ((enc_124).plaintext.components)[3] | {
      let skey_134  = ((enc_124).plaintext.components)[4] | {
        (enc_124).plaintext.components = 0->name_130 + 1->name_131 + 2->text_132 + 3->skey_133 + 4->skey_134
        name_130 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_131 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_132 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_133 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
        skey_134 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      }}}}}
      (enc_124).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
    }}

    t_4.sender = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_resp
    inds[(t_4.data.components)] = 0+1+2+3
    let mesg_135  = ((t_4.data.components))[0] | {
    let enc_136  = ((t_4.data.components))[1] | {
    let text_137  = ((t_4.data.components))[2] | {
    let enc_138  = ((t_4.data.components))[3] | {
      (t_4.data.components) = 0->mesg_135 + 1->enc_136 + 2->text_137 + 3->enc_138
      mesg_135 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_msg2
      inds[(enc_136).plaintext.components] = 0+1
      let text_141  = ((enc_136).plaintext.components)[0] | {
      let skey_142  = ((enc_136).plaintext.components)[1] | {
        (enc_136).plaintext.components = 0->text_141 + 1->skey_142
        text_141 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_142 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}
      (enc_136).encryptionKey = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      text_137 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
      inds[(enc_138).plaintext.components] = 0+1+2+3
      let name_147  = ((enc_138).plaintext.components)[0] | {
      let name_148  = ((enc_138).plaintext.components)[1] | {
      let text_149  = ((enc_138).plaintext.components)[2] | {
      let skey_150  = ((enc_138).plaintext.components)[3] | {
        (enc_138).plaintext.components = 0->name_147 + 1->name_148 + 2->text_149 + 3->skey_150
        name_147 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_148 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_149 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Ta
        skey_150 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}}}
      (enc_138).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
    }}}}

    t_5.receiver = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_init
    inds[(t_5.data.components)] = 0+1+2+3
    let enc_151  = ((t_5.data.components))[0] | {
    let enc_152  = ((t_5.data.components))[1] | {
    let text_153  = ((t_5.data.components))[2] | {
    let mesg_154  = ((t_5.data.components))[3] | {
      (t_5.data.components) = 0->enc_151 + 1->enc_152 + 2->text_153 + 3->mesg_154
      inds[(enc_151).plaintext.components] = 0+1+2+3+4
      let name_160  = ((enc_151).plaintext.components)[0] | {
      let name_161  = ((enc_151).plaintext.components)[1] | {
      let text_162  = ((enc_151).plaintext.components)[2] | {
      let skey_163  = ((enc_151).plaintext.components)[3] | {
      let skey_164  = ((enc_151).plaintext.components)[4] | {
        (enc_151).plaintext.components = 0->name_160 + 1->name_161 + 2->text_162 + 3->skey_163 + 4->skey_164
        name_160 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_161 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_162 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_163 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
        skey_164 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      }}}}}
      (enc_151).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
      inds[(enc_152).plaintext.components] = 0+1
      let text_167  = ((enc_152).plaintext.components)[0] | {
      let skey_168  = ((enc_152).plaintext.components)[1] | {
        (enc_152).plaintext.components = 0->text_167 + 1->skey_168
        text_167 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
        skey_168 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}
      (enc_152).encryptionKey = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      text_153 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
      mesg_154 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_msg1
    }}}}

    t_6.sender = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_init
    inds[(t_6.data.components)] = 0+1
    let enc_169  = ((t_6.data.components))[0] | {
    let mesg_170  = ((t_6.data.components))[1] | {
      (t_6.data.components) = 0->enc_169 + 1->mesg_170
      inds[(enc_169).plaintext.components] = 0+1
      let text_173  = ((enc_169).plaintext.components)[0] | {
      let skey_174  = ((enc_169).plaintext.components)[1] | {
        (enc_169).plaintext.components = 0->text_173 + 1->skey_174
        text_173 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
        skey_174 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}
      (enc_169).encryptionKey = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      mesg_170 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_msg1
    }}

    t_7.receiver = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_resp
    inds[(t_7.data.components)] = 0+1
    let enc_175  = ((t_7.data.components))[0] | {
    let enc_176  = ((t_7.data.components))[1] | {
      (t_7.data.components) = 0->enc_175 + 1->enc_176
      inds[(enc_175).plaintext.components] = 0+1
      let text_179  = ((enc_175).plaintext.components)[0] | {
      let skey_180  = ((enc_175).plaintext.components)[1] | {
        (enc_175).plaintext.components = 0->text_179 + 1->skey_180
        text_179 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
        skey_180 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}
      (enc_175).encryptionKey = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
      inds[(enc_176).plaintext.components] = 0+1+2+3
      let name_185  = ((enc_176).plaintext.components)[0] | {
      let name_186  = ((enc_176).plaintext.components)[1] | {
      let text_187  = ((enc_176).plaintext.components)[2] | {
      let skey_188  = ((enc_176).plaintext.components)[3] | {
        (enc_176).plaintext.components = 0->name_185 + 1->name_186 + 2->text_187 + 3->skey_188
        name_185 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
        name_186 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
        text_187 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Ta
        skey_188 = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
      }}}}
      (enc_176).encryptionKey = getLTK[skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b,skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s]
    }}

  }}}}}}}}
}
pred constrain_skeleton_kao_chow_v3_0 {
  some skeleton_init_0_strand_0 : kao_chow_v3_init | {
    skeleton_init_0_strand_0.kao_chow_v3_init_a = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
    skeleton_init_0_strand_0.kao_chow_v3_init_b = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
    skeleton_init_0_strand_0.kao_chow_v3_init_s = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s
    skeleton_init_0_strand_0.kao_chow_v3_init_Kab = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
    skeleton_init_0_strand_0.kao_chow_v3_init_Kt = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
    skeleton_init_0_strand_0.kao_chow_v3_init_Na = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
    skeleton_init_0_strand_0.kao_chow_v3_init_Nb = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
  }
  some skeleton_server_0_strand_1 : kao_chow_v3_server | {
    skeleton_server_0_strand_1.kao_chow_v3_server_a = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
    skeleton_server_0_strand_1.kao_chow_v3_server_b = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
    skeleton_server_0_strand_1.kao_chow_v3_server_s = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s
    skeleton_server_0_strand_1.kao_chow_v3_server_Kab = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
    skeleton_server_0_strand_1.kao_chow_v3_server_Kt = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
    skeleton_server_0_strand_1.kao_chow_v3_server_Na = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
  }
  some skeleton_resp_0_strand_2 : kao_chow_v3_resp | {
    skeleton_resp_0_strand_2.kao_chow_v3_resp_a = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_a
    skeleton_resp_0_strand_2.kao_chow_v3_resp_b = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_b
    skeleton_resp_0_strand_2.kao_chow_v3_resp_s = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_s
    skeleton_resp_0_strand_2.kao_chow_v3_resp_Kab = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kab
    skeleton_resp_0_strand_2.kao_chow_v3_resp_Kt = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Kt
    skeleton_resp_0_strand_2.kao_chow_v3_resp_Na = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Na
    skeleton_resp_0_strand_2.kao_chow_v3_resp_Nb = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Nb
    skeleton_resp_0_strand_2.kao_chow_v3_resp_Ta = skeleton_kao_chow_v3_0.skeleton_kao_chow_v3_0_Ta
  }
  constrain_skeleton_kao_chow_v3_0_honest_run
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6 + `skey7
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6
  text = `text0 + `text1 + `text2
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1+2+3+4+5) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6 + `skey7->`skey7
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  kao_chow_v3_init = `kao_chow_v3_init0
  kao_chow_v3_server = `kao_chow_v3_server0
  kao_chow_v3_resp = `kao_chow_v3_resp0
  AttackerStrand = `AttackerStrand0
  strand = kao_chow_v3_init + kao_chow_v3_server + kao_chow_v3_resp + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

kao_chow_v3_honest_run: run {
    wellformed

    exec_kao_chow_v3_init
    exec_kao_chow_v3_server
    exec_kao_chow_v3_resp

    constrain_skeleton_kao_chow_v3_0

    kao_chow_v3_init.kao_chow_v3_init_b != Attacker
    kao_chow_v3_init.kao_chow_v3_init_s != Attacker
    kao_chow_v3_init.kao_chow_v3_init_a != Attacker

    kao_chow_v3_server.kao_chow_v3_server_b != Attacker
    kao_chow_v3_server.kao_chow_v3_server_a != Attacker
    kao_chow_v3_server.kao_chow_v3_server_s != Attacker

    kao_chow_v3_resp.kao_chow_v3_resp_a != Attacker
    kao_chow_v3_resp.kao_chow_v3_resp_s != Attacker
    kao_chow_v3_resp.kao_chow_v3_resp_b != Attacker

    kao_chow_v3_init.agent != kao_chow_v3_server.agent
    kao_chow_v3_init.agent != kao_chow_v3_resp.agent
    kao_chow_v3_server.agent != kao_chow_v3_resp.agent

    not Attacker in (kao_chow_v3_init + kao_chow_v3_server + kao_chow_v3_resp).agent

    
    no ((name.generated_times).Timeslot & name.(name.(KeyPairs.ltks)) )

} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}