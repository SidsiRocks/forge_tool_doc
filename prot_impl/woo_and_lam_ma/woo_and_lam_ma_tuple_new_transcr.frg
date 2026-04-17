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

sig woo_and_lam_ma_init extends strand {
  woo_and_lam_ma_init_p : one name,
  woo_and_lam_ma_init_q : one name,
  woo_and_lam_ma_init_s : one name,
  woo_and_lam_ma_init_N1 : one text,
  woo_and_lam_ma_init_N2 : one text,
  woo_and_lam_ma_init_Kpq : one skey
}
pred exec_woo_and_lam_ma_init {
  all arbitrary_init_woo_and_lam_ma : woo_and_lam_ma_init | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p,arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s]] or generates [aStrand,getLTK[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p,arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s]]
    }
    (generated_times.Timeslot).(arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1) = arbitrary_init_woo_and_lam_ma.agent
    arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p != arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_q
    arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p != arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s
    arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_q != arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
    some t4 : t3.(^next) {
      ((arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1)->t0) in (arbitrary_init_woo_and_lam_ma.agent).generated_times
      t0+t1+t2+t3+t4 = sender.arbitrary_init_woo_and_lam_ma + receiver.arbitrary_init_woo_and_lam_ma
      t0.sender = arbitrary_init_woo_and_lam_ma
      inds[((t0.data).components)] = 0+1
      let name_1  = (((t0.data).components))[0] | {
      let text_2  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_1 + 1->text_2
        name_1 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p
        text_2 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1
      }}

      t1.receiver = arbitrary_init_woo_and_lam_ma
      inds[((t1.data).components)] = 0+1
      let name_3  = (((t1.data).components))[0] | {
      let text_4  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_3 + 1->text_4
        name_3 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_q
        text_4 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N2
      }}

      t2.sender = arbitrary_init_woo_and_lam_ma
      inds[((t2.data)).plaintext.components] = 0+1+2+3
      let name_9  = (((t2.data)).plaintext.components)[0] | {
      let name_10  = (((t2.data)).plaintext.components)[1] | {
      let text_11  = (((t2.data)).plaintext.components)[2] | {
      let text_12  = (((t2.data)).plaintext.components)[3] | {
        ((t2.data)).plaintext.components = 0->name_9 + 1->name_10 + 2->text_11 + 3->text_12
        name_9 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p
        name_10 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_q
        text_11 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1
        text_12 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N2
      }}}}
      ((t2.data)).encryptionKey = getLTK[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p,arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s]

      t3.receiver = arbitrary_init_woo_and_lam_ma
      inds[((t3.data).components)] = 0+1
      let enc_13  = (((t3.data).components))[0] | {
      let enc_14  = (((t3.data).components))[1] | {
        ((t3.data).components) = 0->enc_13 + 1->enc_14
        learnt_term_by[getLTK[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p,arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s],arbitrary_init_woo_and_lam_ma.agent,t3]
        inds[(enc_13).plaintext.components] = 0+1+2+3
        let name_19  = ((enc_13).plaintext.components)[0] | {
        let text_20  = ((enc_13).plaintext.components)[1] | {
        let text_21  = ((enc_13).plaintext.components)[2] | {
        let skey_22  = ((enc_13).plaintext.components)[3] | {
          (enc_13).plaintext.components = 0->name_19 + 1->text_20 + 2->text_21 + 3->skey_22
          name_19 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_q
          text_20 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1
          text_21 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N2
          skey_22 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_Kpq
        }}}}
        (enc_13).encryptionKey = getLTK[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_p,arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_s]
        learnt_term_by[arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_Kpq,arbitrary_init_woo_and_lam_ma.agent,t3]
        inds[(enc_14).plaintext.components] = 0+1
        let text_25  = ((enc_14).plaintext.components)[0] | {
        let text_26  = ((enc_14).plaintext.components)[1] | {
          (enc_14).plaintext.components = 0->text_25 + 1->text_26
          text_25 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N1
          text_26 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N2
        }}
        (enc_14).encryptionKey = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_Kpq
      }}

      t4.sender = arbitrary_init_woo_and_lam_ma
      inds[((t4.data)).plaintext.components] = 0
      let text_28  = (((t4.data)).plaintext.components)[0] | {
        ((t4.data)).plaintext.components = 0->text_28
        text_28 = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_N2
      }
      ((t4.data)).encryptionKey = arbitrary_init_woo_and_lam_ma.woo_and_lam_ma_init_Kpq

    }}}}}
  }
}
sig woo_and_lam_ma_resp extends strand {
  woo_and_lam_ma_resp_p : one name,
  woo_and_lam_ma_resp_q : one name,
  woo_and_lam_ma_resp_s : one name,
  woo_and_lam_ma_resp_N1 : one text,
  woo_and_lam_ma_resp_N2 : one text,
  woo_and_lam_ma_resp_Kpq : one skey,
  woo_and_lam_ma_resp_msg1 : one mesg,
  woo_and_lam_ma_resp_msg2 : one mesg
}
pred exec_woo_and_lam_ma_resp {
  all arbitrary_resp_woo_and_lam_ma : woo_and_lam_ma_resp | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q,arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s]] or generates [aStrand,getLTK[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q,arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s]]
    }
    (generated_times.Timeslot).(arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2) = arbitrary_resp_woo_and_lam_ma.agent
    arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_p != arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q
    arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_p != arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s
    arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q != arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
    some t4 : t3.(^next) {
    some t5 : t4.(^next) {
    some t6 : t5.(^next) {
      ((arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2)->t1) in (arbitrary_resp_woo_and_lam_ma.agent).generated_times
      t0+t1+t2+t3+t4+t5+t6 = sender.arbitrary_resp_woo_and_lam_ma + receiver.arbitrary_resp_woo_and_lam_ma
      t0.receiver = arbitrary_resp_woo_and_lam_ma
      inds[((t0.data).components)] = 0+1
      let name_29  = (((t0.data).components))[0] | {
      let text_30  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_29 + 1->text_30
        name_29 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_p
        text_30 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N1
      }}

      t1.sender = arbitrary_resp_woo_and_lam_ma
      inds[((t1.data).components)] = 0+1
      let name_31  = (((t1.data).components))[0] | {
      let text_32  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_31 + 1->text_32
        name_31 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q
        text_32 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2
      }}

      t2.receiver = arbitrary_resp_woo_and_lam_ma
      (t2.data) = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_msg1

      t3.sender = arbitrary_resp_woo_and_lam_ma
      inds[((t3.data).components)] = 0+1
      let mesg_33  = (((t3.data).components))[0] | {
      let enc_34  = (((t3.data).components))[1] | {
        ((t3.data).components) = 0->mesg_33 + 1->enc_34
        mesg_33 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_msg1
        inds[(enc_34).plaintext.components] = 0+1+2+3
        let name_39  = ((enc_34).plaintext.components)[0] | {
        let name_40  = ((enc_34).plaintext.components)[1] | {
        let text_41  = ((enc_34).plaintext.components)[2] | {
        let text_42  = ((enc_34).plaintext.components)[3] | {
          (enc_34).plaintext.components = 0->name_39 + 1->name_40 + 2->text_41 + 3->text_42
          name_39 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_p
          name_40 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q
          text_41 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N1
          text_42 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2
        }}}}
        (enc_34).encryptionKey = getLTK[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q,arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s]
      }}

      t4.receiver = arbitrary_resp_woo_and_lam_ma
      inds[((t4.data).components)] = 0+1
      let mesg_43  = (((t4.data).components))[0] | {
      let enc_44  = (((t4.data).components))[1] | {
        ((t4.data).components) = 0->mesg_43 + 1->enc_44
        mesg_43 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_msg2
        learnt_term_by[getLTK[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q,arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s],arbitrary_resp_woo_and_lam_ma.agent,t4]
        inds[(enc_44).plaintext.components] = 0+1+2+3
        let name_49  = ((enc_44).plaintext.components)[0] | {
        let text_50  = ((enc_44).plaintext.components)[1] | {
        let text_51  = ((enc_44).plaintext.components)[2] | {
        let skey_52  = ((enc_44).plaintext.components)[3] | {
          (enc_44).plaintext.components = 0->name_49 + 1->text_50 + 2->text_51 + 3->skey_52
          name_49 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_p
          text_50 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N1
          text_51 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2
          skey_52 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_Kpq
        }}}}
        (enc_44).encryptionKey = getLTK[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_q,arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_s]
      }}

      t5.sender = arbitrary_resp_woo_and_lam_ma
      inds[((t5.data).components)] = 0+1
      let mesg_53  = (((t5.data).components))[0] | {
      let enc_54  = (((t5.data).components))[1] | {
        ((t5.data).components) = 0->mesg_53 + 1->enc_54
        mesg_53 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_msg2
        inds[(enc_54).plaintext.components] = 0+1
        let text_57  = ((enc_54).plaintext.components)[0] | {
        let text_58  = ((enc_54).plaintext.components)[1] | {
          (enc_54).plaintext.components = 0->text_57 + 1->text_58
          text_57 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N1
          text_58 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2
        }}
        (enc_54).encryptionKey = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_Kpq
      }}

      t6.receiver = arbitrary_resp_woo_and_lam_ma
      learnt_term_by[arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_Kpq,arbitrary_resp_woo_and_lam_ma.agent,t6]
      inds[((t6.data)).plaintext.components] = 0
      let text_60  = (((t6.data)).plaintext.components)[0] | {
        ((t6.data)).plaintext.components = 0->text_60
        text_60 = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_N2
      }
      ((t6.data)).encryptionKey = arbitrary_resp_woo_and_lam_ma.woo_and_lam_ma_resp_Kpq

    }}}}}}}
  }
}
sig woo_and_lam_ma_server extends strand {
  woo_and_lam_ma_server_p : one name,
  woo_and_lam_ma_server_q : one name,
  woo_and_lam_ma_server_s : one name,
  woo_and_lam_ma_server_N1 : one text,
  woo_and_lam_ma_server_N2 : one text,
  woo_and_lam_ma_server_Kpq : one skey
}
pred exec_woo_and_lam_ma_server {
  all arbitrary_server_woo_and_lam_ma : woo_and_lam_ma_server | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]] or generates [aStrand,getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]] or generates [aStrand,getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]]
    }
    (generated_times.Timeslot).(arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_Kpq) = arbitrary_server_woo_and_lam_ma.agent
    arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p != arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q
    arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p != arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s
    arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q != arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      ((arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_Kpq)->t1) in (arbitrary_server_woo_and_lam_ma.agent).generated_times
      t0+t1 = sender.arbitrary_server_woo_and_lam_ma + receiver.arbitrary_server_woo_and_lam_ma
      t0.receiver = arbitrary_server_woo_and_lam_ma
      inds[((t0.data).components)] = 0+1
      let enc_61  = (((t0.data).components))[0] | {
      let enc_62  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->enc_61 + 1->enc_62
        learnt_term_by[getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s],arbitrary_server_woo_and_lam_ma.agent,t0]
        inds[(enc_61).plaintext.components] = 0+1+2+3
        let name_67  = ((enc_61).plaintext.components)[0] | {
        let name_68  = ((enc_61).plaintext.components)[1] | {
        let text_69  = ((enc_61).plaintext.components)[2] | {
        let text_70  = ((enc_61).plaintext.components)[3] | {
          (enc_61).plaintext.components = 0->name_67 + 1->name_68 + 2->text_69 + 3->text_70
          name_67 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p
          name_68 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q
          text_69 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N1
          text_70 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N2
        }}}}
        (enc_61).encryptionKey = getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]
        learnt_term_by[getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s],arbitrary_server_woo_and_lam_ma.agent,t0]
        inds[(enc_62).plaintext.components] = 0+1+2+3
        let name_75  = ((enc_62).plaintext.components)[0] | {
        let name_76  = ((enc_62).plaintext.components)[1] | {
        let text_77  = ((enc_62).plaintext.components)[2] | {
        let text_78  = ((enc_62).plaintext.components)[3] | {
          (enc_62).plaintext.components = 0->name_75 + 1->name_76 + 2->text_77 + 3->text_78
          name_75 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p
          name_76 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q
          text_77 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N1
          text_78 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N2
        }}}}
        (enc_62).encryptionKey = getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]
      }}

      t1.sender = arbitrary_server_woo_and_lam_ma
      inds[((t1.data).components)] = 0+1
      let enc_79  = (((t1.data).components))[0] | {
      let enc_80  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->enc_79 + 1->enc_80
        inds[(enc_79).plaintext.components] = 0+1+2+3
        let name_85  = ((enc_79).plaintext.components)[0] | {
        let text_86  = ((enc_79).plaintext.components)[1] | {
        let text_87  = ((enc_79).plaintext.components)[2] | {
        let skey_88  = ((enc_79).plaintext.components)[3] | {
          (enc_79).plaintext.components = 0->name_85 + 1->text_86 + 2->text_87 + 3->skey_88
          name_85 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q
          text_86 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N1
          text_87 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N2
          skey_88 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_Kpq
        }}}}
        (enc_79).encryptionKey = getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]
        inds[(enc_80).plaintext.components] = 0+1+2+3
        let name_93  = ((enc_80).plaintext.components)[0] | {
        let text_94  = ((enc_80).plaintext.components)[1] | {
        let text_95  = ((enc_80).plaintext.components)[2] | {
        let skey_96  = ((enc_80).plaintext.components)[3] | {
          (enc_80).plaintext.components = 0->name_93 + 1->text_94 + 2->text_95 + 3->skey_96
          name_93 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_p
          text_94 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N1
          text_95 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_N2
          skey_96 = arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_Kpq
        }}}}
        (enc_80).encryptionKey = getLTK[arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_q,arbitrary_server_woo_and_lam_ma.woo_and_lam_ma_server_s]
      }}

    }}
  }
}
one sig skeleton_woo_and_lam_ma_0 {
  skeleton_woo_and_lam_ma_0_p : one name,
  skeleton_woo_and_lam_ma_0_q : one name,
  skeleton_woo_and_lam_ma_0_s : one name,
  skeleton_woo_and_lam_ma_0_N1 : one text,
  skeleton_woo_and_lam_ma_0_N2 : one text,
  skeleton_woo_and_lam_ma_0_Kpq : one skey,
  skeleton_woo_and_lam_ma_0_msg1 : one mesg,
  skeleton_woo_and_lam_ma_0_msg2 : one mesg,
  skeleton_woo_and_lam_ma_0_init_strand : one woo_and_lam_ma_init,
  skeleton_woo_and_lam_ma_0_resp_strand : one woo_and_lam_ma_resp,
  skeleton_woo_and_lam_ma_0_server_strand : one woo_and_lam_ma_server
}
pred constrain_skeleton_woo_and_lam_ma_0_honest_run {
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
    t_0.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_init_strand
    inds[(t_0.data.components)] = 0+1
    let name_97  = ((t_0.data.components))[0] | {
    let text_98  = ((t_0.data.components))[1] | {
      (t_0.data.components) = 0->name_97 + 1->text_98
      name_97 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
      text_98 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
    }}

    t_1.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[(t_1.data.components)] = 0+1
    let name_99  = ((t_1.data.components))[0] | {
    let text_100  = ((t_1.data.components))[1] | {
      (t_1.data.components) = 0->name_99 + 1->text_100
      name_99 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
      text_100 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
    }}

    t_2.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[(t_2.data.components)] = 0+1
    let name_101  = ((t_2.data.components))[0] | {
    let text_102  = ((t_2.data.components))[1] | {
      (t_2.data.components) = 0->name_101 + 1->text_102
      name_101 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
      text_102 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
    }}

    t_3.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_init_strand
    inds[(t_3.data.components)] = 0+1
    let name_103  = ((t_3.data.components))[0] | {
    let text_104  = ((t_3.data.components))[1] | {
      (t_3.data.components) = 0->name_103 + 1->text_104
      name_103 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
      text_104 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
    }}

    t_4.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_init_strand
    inds[((t_4.data)).plaintext.components] = 0+1+2+3
    let name_109  = (((t_4.data)).plaintext.components)[0] | {
    let name_110  = (((t_4.data)).plaintext.components)[1] | {
    let text_111  = (((t_4.data)).plaintext.components)[2] | {
    let text_112  = (((t_4.data)).plaintext.components)[3] | {
      ((t_4.data)).plaintext.components = 0->name_109 + 1->name_110 + 2->text_111 + 3->text_112
      name_109 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
      name_110 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
      text_111 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
      text_112 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
    }}}}
    ((t_4.data)).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]

    t_5.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    (t_5.data) = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_msg1

    t_6.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[(t_6.data.components)] = 0+1
    let mesg_113  = ((t_6.data.components))[0] | {
    let enc_114  = ((t_6.data.components))[1] | {
      (t_6.data.components) = 0->mesg_113 + 1->enc_114
      mesg_113 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_msg1
      inds[(enc_114).plaintext.components] = 0+1+2+3
      let name_119  = ((enc_114).plaintext.components)[0] | {
      let name_120  = ((enc_114).plaintext.components)[1] | {
      let text_121  = ((enc_114).plaintext.components)[2] | {
      let text_122  = ((enc_114).plaintext.components)[3] | {
        (enc_114).plaintext.components = 0->name_119 + 1->name_120 + 2->text_121 + 3->text_122
        name_119 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
        name_120 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
        text_121 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_122 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
      }}}}
      (enc_114).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
    }}

    t_7.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_server_strand
    inds[(t_7.data.components)] = 0+1
    let enc_123  = ((t_7.data.components))[0] | {
    let enc_124  = ((t_7.data.components))[1] | {
      (t_7.data.components) = 0->enc_123 + 1->enc_124
      inds[(enc_123).plaintext.components] = 0+1+2+3
      let name_129  = ((enc_123).plaintext.components)[0] | {
      let name_130  = ((enc_123).plaintext.components)[1] | {
      let text_131  = ((enc_123).plaintext.components)[2] | {
      let text_132  = ((enc_123).plaintext.components)[3] | {
        (enc_123).plaintext.components = 0->name_129 + 1->name_130 + 2->text_131 + 3->text_132
        name_129 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
        name_130 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
        text_131 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_132 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
      }}}}
      (enc_123).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
      inds[(enc_124).plaintext.components] = 0+1+2+3
      let name_137  = ((enc_124).plaintext.components)[0] | {
      let name_138  = ((enc_124).plaintext.components)[1] | {
      let text_139  = ((enc_124).plaintext.components)[2] | {
      let text_140  = ((enc_124).plaintext.components)[3] | {
        (enc_124).plaintext.components = 0->name_137 + 1->name_138 + 2->text_139 + 3->text_140
        name_137 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
        name_138 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
        text_139 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_140 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
      }}}}
      (enc_124).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
    }}

    t_8.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_server_strand
    inds[(t_8.data.components)] = 0+1
    let enc_141  = ((t_8.data.components))[0] | {
    let enc_142  = ((t_8.data.components))[1] | {
      (t_8.data.components) = 0->enc_141 + 1->enc_142
      inds[(enc_141).plaintext.components] = 0+1+2+3
      let name_147  = ((enc_141).plaintext.components)[0] | {
      let text_148  = ((enc_141).plaintext.components)[1] | {
      let text_149  = ((enc_141).plaintext.components)[2] | {
      let skey_150  = ((enc_141).plaintext.components)[3] | {
        (enc_141).plaintext.components = 0->name_147 + 1->text_148 + 2->text_149 + 3->skey_150
        name_147 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
        text_148 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_149 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
        skey_150 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
      }}}}
      (enc_141).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
      inds[(enc_142).plaintext.components] = 0+1+2+3
      let name_155  = ((enc_142).plaintext.components)[0] | {
      let text_156  = ((enc_142).plaintext.components)[1] | {
      let text_157  = ((enc_142).plaintext.components)[2] | {
      let skey_158  = ((enc_142).plaintext.components)[3] | {
        (enc_142).plaintext.components = 0->name_155 + 1->text_156 + 2->text_157 + 3->skey_158
        name_155 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
        text_156 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_157 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
        skey_158 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
      }}}}
      (enc_142).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
    }}

    t_9.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[(t_9.data.components)] = 0+1
    let mesg_159  = ((t_9.data.components))[0] | {
    let enc_160  = ((t_9.data.components))[1] | {
      (t_9.data.components) = 0->mesg_159 + 1->enc_160
      mesg_159 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_msg2
      inds[(enc_160).plaintext.components] = 0+1+2+3
      let name_165  = ((enc_160).plaintext.components)[0] | {
      let text_166  = ((enc_160).plaintext.components)[1] | {
      let text_167  = ((enc_160).plaintext.components)[2] | {
      let skey_168  = ((enc_160).plaintext.components)[3] | {
        (enc_160).plaintext.components = 0->name_165 + 1->text_166 + 2->text_167 + 3->skey_168
        name_165 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
        text_166 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_167 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
        skey_168 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
      }}}}
      (enc_160).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
    }}

    t_10.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[(t_10.data.components)] = 0+1
    let mesg_169  = ((t_10.data.components))[0] | {
    let enc_170  = ((t_10.data.components))[1] | {
      (t_10.data.components) = 0->mesg_169 + 1->enc_170
      mesg_169 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_msg2
      inds[(enc_170).plaintext.components] = 0+1
      let text_173  = ((enc_170).plaintext.components)[0] | {
      let text_174  = ((enc_170).plaintext.components)[1] | {
        (enc_170).plaintext.components = 0->text_173 + 1->text_174
        text_173 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_174 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
      }}
      (enc_170).encryptionKey = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
    }}

    t_11.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_init_strand
    inds[(t_11.data.components)] = 0+1
    let enc_175  = ((t_11.data.components))[0] | {
    let enc_176  = ((t_11.data.components))[1] | {
      (t_11.data.components) = 0->enc_175 + 1->enc_176
      inds[(enc_175).plaintext.components] = 0+1+2+3
      let name_181  = ((enc_175).plaintext.components)[0] | {
      let text_182  = ((enc_175).plaintext.components)[1] | {
      let text_183  = ((enc_175).plaintext.components)[2] | {
      let skey_184  = ((enc_175).plaintext.components)[3] | {
        (enc_175).plaintext.components = 0->name_181 + 1->text_182 + 2->text_183 + 3->skey_184
        name_181 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
        text_182 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_183 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
        skey_184 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
      }}}}
      (enc_175).encryptionKey = getLTK[skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p,skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s]
      inds[(enc_176).plaintext.components] = 0+1
      let text_187  = ((enc_176).plaintext.components)[0] | {
      let text_188  = ((enc_176).plaintext.components)[1] | {
        (enc_176).plaintext.components = 0->text_187 + 1->text_188
        text_187 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
        text_188 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
      }}
      (enc_176).encryptionKey = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
    }}

    t_12.sender = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_init_strand
    inds[((t_12.data)).plaintext.components] = 0
    let text_190  = (((t_12.data)).plaintext.components)[0] | {
      ((t_12.data)).plaintext.components = 0->text_190
      text_190 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
    }
    ((t_12.data)).encryptionKey = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq

    t_13.receiver = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_resp_strand
    inds[((t_13.data)).plaintext.components] = 0
    let text_192  = (((t_13.data)).plaintext.components)[0] | {
      ((t_13.data)).plaintext.components = 0->text_192
      text_192 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
    }
    ((t_13.data)).encryptionKey = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq

  }}}}}}}}}}}}}}
}
pred constrain_skeleton_woo_and_lam_ma_0 {
  some skeleton_init_0_strand_0 : woo_and_lam_ma_init | {
    skeleton_init_0_strand_0.woo_and_lam_ma_init_p = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
    skeleton_init_0_strand_0.woo_and_lam_ma_init_q = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
    skeleton_init_0_strand_0.woo_and_lam_ma_init_s = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s
    skeleton_init_0_strand_0.woo_and_lam_ma_init_Kpq = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
    skeleton_init_0_strand_0.woo_and_lam_ma_init_N1 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
    skeleton_init_0_strand_0.woo_and_lam_ma_init_N2 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
  }
  some skeleton_resp_0_strand_1 : woo_and_lam_ma_resp | {
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_p = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_q = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_s = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_Kpq = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_N1 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
    skeleton_resp_0_strand_1.woo_and_lam_ma_resp_N2 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
  }
  some skeleton_server_0_strand_2 : woo_and_lam_ma_server | {
    skeleton_server_0_strand_2.woo_and_lam_ma_server_p = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_p
    skeleton_server_0_strand_2.woo_and_lam_ma_server_q = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_q
    skeleton_server_0_strand_2.woo_and_lam_ma_server_s = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_s
    skeleton_server_0_strand_2.woo_and_lam_ma_server_Kpq = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_Kpq
    skeleton_server_0_strand_2.woo_and_lam_ma_server_N1 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N1
    skeleton_server_0_strand_2.woo_and_lam_ma_server_N2 = skeleton_woo_and_lam_ma_0.skeleton_woo_and_lam_ma_0_N2
  }
  constrain_skeleton_woo_and_lam_ma_0_honest_run
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10 + `tuple11 + `tuple12
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7 + `Timeslot8 + `Timeslot9 + `Timeslot10 + `Timeslot11 + `Timeslot12 + `Timeslot13

  components in tuple -> (0+1+2+3) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7 + `Timeslot7->`Timeslot8 + `Timeslot8->`Timeslot9 + `Timeslot9->`Timeslot10 + `Timeslot10->`Timeslot11 + `Timeslot11->`Timeslot12 + `Timeslot12->`Timeslot13
  mt_next = `Microtick0 -> `Microtick1

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  woo_and_lam_ma_init = `woo_and_lam_ma_init0
  woo_and_lam_ma_resp = `woo_and_lam_ma_resp0
  woo_and_lam_ma_server = `woo_and_lam_ma_server0
  AttackerStrand = `AttackerStrand0
  strand = woo_and_lam_ma_init + woo_and_lam_ma_resp + woo_and_lam_ma_server + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

woo_and_lam_ma_honest_run: run {
    wellformed 

    exec_woo_and_lam_ma_init
    exec_woo_and_lam_ma_server
    exec_woo_and_lam_ma_resp

    constrain_skeleton_woo_and_lam_ma_0

    no (woo_and_lam_ma_init.woo_and_lam_ma_init_p & Attacker)
    no (woo_and_lam_ma_init.woo_and_lam_ma_init_q & Attacker)
    no (woo_and_lam_ma_init.woo_and_lam_ma_init_s & Attacker)

    no (woo_and_lam_ma_server.woo_and_lam_ma_server_p & Attacker)
    no (woo_and_lam_ma_server.woo_and_lam_ma_server_q & Attacker)
    no (woo_and_lam_ma_server.woo_and_lam_ma_server_s & Attacker)

    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_p & Attacker)
    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_q & Attacker)
    no (woo_and_lam_ma_resp.woo_and_lam_ma_resp_s & Attacker)

    no (woo_and_lam_ma_init.agent & woo_and_lam_ma_server.agent)
    no (woo_and_lam_ma_init.agent & woo_and_lam_ma_resp.agent)
    no (woo_and_lam_ma_server.agent & woo_and_lam_ma_resp.agent)

    not Attacker in (woo_and_lam_ma_init + woo_and_lam_ma_server + woo_and_lam_ma_resp).agent

    all x, y: name | woo_and_lam_ma_server.woo_and_lam_ma_server_Kpq != x.(KeyPairs.ltks)[y]
} for {
    next is linear
    mt_next is linear
    honest_run_bounds
}