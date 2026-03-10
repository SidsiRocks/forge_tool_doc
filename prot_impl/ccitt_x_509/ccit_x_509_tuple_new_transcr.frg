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

sig ccit_x_509_A extends strand {
  ccit_x_509_A_a : one name,
  ccit_x_509_A_b : one name,
  ccit_x_509_A_Ta : one text,
  ccit_x_509_A_Tb : one text,
  ccit_x_509_A_Na : one text,
  ccit_x_509_A_Nb : one text,
  ccit_x_509_A_Ya : one text,
  ccit_x_509_A_Yb : one text,
  ccit_x_509_A_Xa : one text,
  ccit_x_509_A_Xb : one text
}
pred exec_ccit_x_509_A {
  all arbitrary_A_ccit_x_509 : ccit_x_509_A | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_a]] or generates [aStrand,getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_a]]
    }
    (generated_times.Timeslot).(arbitrary_A_ccit_x_509.ccit_x_509_A_Ta) = arbitrary_A_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_A_ccit_x_509.ccit_x_509_A_Na) = arbitrary_A_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_A_ccit_x_509.ccit_x_509_A_Xa) = arbitrary_A_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_A_ccit_x_509.ccit_x_509_A_Ya) = arbitrary_A_ccit_x_509.agent
    arbitrary_A_ccit_x_509.ccit_x_509_A_Ta != arbitrary_A_ccit_x_509.ccit_x_509_A_Na
    arbitrary_A_ccit_x_509.ccit_x_509_A_Ta != arbitrary_A_ccit_x_509.ccit_x_509_A_Xa
    arbitrary_A_ccit_x_509.ccit_x_509_A_Ta != arbitrary_A_ccit_x_509.ccit_x_509_A_Ya
    arbitrary_A_ccit_x_509.ccit_x_509_A_Na != arbitrary_A_ccit_x_509.ccit_x_509_A_Xa
    arbitrary_A_ccit_x_509.ccit_x_509_A_Na != arbitrary_A_ccit_x_509.ccit_x_509_A_Ya
    arbitrary_A_ccit_x_509.ccit_x_509_A_Xa != arbitrary_A_ccit_x_509.ccit_x_509_A_Ya
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_A_ccit_x_509.ccit_x_509_A_Ta)->t0 + (arbitrary_A_ccit_x_509.ccit_x_509_A_Na)->t0 + (arbitrary_A_ccit_x_509.ccit_x_509_A_Xa)->t0 + (arbitrary_A_ccit_x_509.ccit_x_509_A_Ya)->t0) in (arbitrary_A_ccit_x_509.agent).generated_times
      t0+t1+t2 = sender.arbitrary_A_ccit_x_509 + receiver.arbitrary_A_ccit_x_509
      t0.sender = arbitrary_A_ccit_x_509
      inds[((t0.data).components)] = 0+1
      let name_1  = (((t0.data).components))[0] | {
      let enc_2  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_1 + 1->enc_2
        name_1 = arbitrary_A_ccit_x_509.ccit_x_509_A_a
        inds[(enc_2).plaintext.components] = 0+1+2+3+4
        let text_8  = ((enc_2).plaintext.components)[0] | {
        let text_9  = ((enc_2).plaintext.components)[1] | {
        let name_10  = ((enc_2).plaintext.components)[2] | {
        let text_11  = ((enc_2).plaintext.components)[3] | {
        let enc_12  = ((enc_2).plaintext.components)[4] | {
          (enc_2).plaintext.components = 0->text_8 + 1->text_9 + 2->name_10 + 3->text_11 + 4->enc_12
          text_8 = arbitrary_A_ccit_x_509.ccit_x_509_A_Ta
          text_9 = arbitrary_A_ccit_x_509.ccit_x_509_A_Na
          name_10 = arbitrary_A_ccit_x_509.ccit_x_509_A_b
          text_11 = arbitrary_A_ccit_x_509.ccit_x_509_A_Xa
          inds[(enc_12).plaintext.components] = 0
          let text_14  = ((enc_12).plaintext.components)[0] | {
            (enc_12).plaintext.components = 0->text_14
            text_14 = arbitrary_A_ccit_x_509.ccit_x_509_A_Ya
          }
          (enc_12).encryptionKey = getPUBK[arbitrary_A_ccit_x_509.ccit_x_509_A_b]
        }}}}}
        (enc_2).encryptionKey = getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_a]
      }}

      t1.receiver = arbitrary_A_ccit_x_509
      inds[((t1.data).components)] = 0+1
      let name_15  = (((t1.data).components))[0] | {
      let enc_16  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_15 + 1->enc_16
        name_15 = arbitrary_A_ccit_x_509.ccit_x_509_A_b
        learnt_term_by[getPUBK[arbitrary_A_ccit_x_509.ccit_x_509_A_b],arbitrary_A_ccit_x_509.agent,t1]
        inds[(enc_16).plaintext.components] = 0+1+2+3+4+5
        let text_23  = ((enc_16).plaintext.components)[0] | {
        let text_24  = ((enc_16).plaintext.components)[1] | {
        let name_25  = ((enc_16).plaintext.components)[2] | {
        let text_26  = ((enc_16).plaintext.components)[3] | {
        let text_27  = ((enc_16).plaintext.components)[4] | {
        let enc_28  = ((enc_16).plaintext.components)[5] | {
          (enc_16).plaintext.components = 0->text_23 + 1->text_24 + 2->name_25 + 3->text_26 + 4->text_27 + 5->enc_28
          text_23 = arbitrary_A_ccit_x_509.ccit_x_509_A_Tb
          text_24 = arbitrary_A_ccit_x_509.ccit_x_509_A_Nb
          name_25 = arbitrary_A_ccit_x_509.ccit_x_509_A_a
          text_26 = arbitrary_A_ccit_x_509.ccit_x_509_A_Na
          text_27 = arbitrary_A_ccit_x_509.ccit_x_509_A_Xb
          learnt_term_by[getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_a],arbitrary_A_ccit_x_509.agent,t1]
          inds[(enc_28).plaintext.components] = 0
          let text_30  = ((enc_28).plaintext.components)[0] | {
            (enc_28).plaintext.components = 0->text_30
            text_30 = arbitrary_A_ccit_x_509.ccit_x_509_A_Yb
          }
          (enc_28).encryptionKey = getPUBK[arbitrary_A_ccit_x_509.ccit_x_509_A_a]
        }}}}}}
        (enc_16).encryptionKey = getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_b]
      }}

      t2.sender = arbitrary_A_ccit_x_509
      inds[((t2.data).components)] = 0+1
      let name_31  = (((t2.data).components))[0] | {
      let enc_32  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->name_31 + 1->enc_32
        name_31 = arbitrary_A_ccit_x_509.ccit_x_509_A_a
        inds[(enc_32).plaintext.components] = 0
        let text_34  = ((enc_32).plaintext.components)[0] | {
          (enc_32).plaintext.components = 0->text_34
          text_34 = arbitrary_A_ccit_x_509.ccit_x_509_A_Nb
        }
        (enc_32).encryptionKey = getPRIVK[arbitrary_A_ccit_x_509.ccit_x_509_A_a]
      }}

    }}}
  }
}
sig ccit_x_509_B extends strand {
  ccit_x_509_B_a : one name,
  ccit_x_509_B_b : one name,
  ccit_x_509_B_Ta : one text,
  ccit_x_509_B_Tb : one text,
  ccit_x_509_B_Na : one text,
  ccit_x_509_B_Nb : one text,
  ccit_x_509_B_Ya : one text,
  ccit_x_509_B_Yb : one text,
  ccit_x_509_B_Xa : one text,
  ccit_x_509_B_Xb : one text
}
pred exec_ccit_x_509_B {
  all arbitrary_B_ccit_x_509 : ccit_x_509_B | {
    no aStrand : strand | {
      originates[aStrand,getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_b]] or generates [aStrand,getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_b]]
    }
    (generated_times.Timeslot).(arbitrary_B_ccit_x_509.ccit_x_509_B_Tb) = arbitrary_B_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_B_ccit_x_509.ccit_x_509_B_Nb) = arbitrary_B_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_B_ccit_x_509.ccit_x_509_B_Xb) = arbitrary_B_ccit_x_509.agent
    (generated_times.Timeslot).(arbitrary_B_ccit_x_509.ccit_x_509_B_Yb) = arbitrary_B_ccit_x_509.agent
    arbitrary_B_ccit_x_509.ccit_x_509_B_Tb != arbitrary_B_ccit_x_509.ccit_x_509_B_Nb
    arbitrary_B_ccit_x_509.ccit_x_509_B_Tb != arbitrary_B_ccit_x_509.ccit_x_509_B_Xb
    arbitrary_B_ccit_x_509.ccit_x_509_B_Tb != arbitrary_B_ccit_x_509.ccit_x_509_B_Yb
    arbitrary_B_ccit_x_509.ccit_x_509_B_Nb != arbitrary_B_ccit_x_509.ccit_x_509_B_Xb
    arbitrary_B_ccit_x_509.ccit_x_509_B_Nb != arbitrary_B_ccit_x_509.ccit_x_509_B_Yb
    arbitrary_B_ccit_x_509.ccit_x_509_B_Xb != arbitrary_B_ccit_x_509.ccit_x_509_B_Yb
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
      ((arbitrary_B_ccit_x_509.ccit_x_509_B_Tb)->t1 + (arbitrary_B_ccit_x_509.ccit_x_509_B_Nb)->t1 + (arbitrary_B_ccit_x_509.ccit_x_509_B_Xb)->t1 + (arbitrary_B_ccit_x_509.ccit_x_509_B_Yb)->t1) in (arbitrary_B_ccit_x_509.agent).generated_times
      t0+t1+t2 = sender.arbitrary_B_ccit_x_509 + receiver.arbitrary_B_ccit_x_509
      t0.receiver = arbitrary_B_ccit_x_509
      inds[((t0.data).components)] = 0+1
      let name_35  = (((t0.data).components))[0] | {
      let enc_36  = (((t0.data).components))[1] | {
        ((t0.data).components) = 0->name_35 + 1->enc_36
        name_35 = arbitrary_B_ccit_x_509.ccit_x_509_B_a
        learnt_term_by[getPUBK[arbitrary_B_ccit_x_509.ccit_x_509_B_a],arbitrary_B_ccit_x_509.agent,t0]
        inds[(enc_36).plaintext.components] = 0+1+2+3+4
        let text_42  = ((enc_36).plaintext.components)[0] | {
        let text_43  = ((enc_36).plaintext.components)[1] | {
        let name_44  = ((enc_36).plaintext.components)[2] | {
        let text_45  = ((enc_36).plaintext.components)[3] | {
        let enc_46  = ((enc_36).plaintext.components)[4] | {
          (enc_36).plaintext.components = 0->text_42 + 1->text_43 + 2->name_44 + 3->text_45 + 4->enc_46
          text_42 = arbitrary_B_ccit_x_509.ccit_x_509_B_Ta
          text_43 = arbitrary_B_ccit_x_509.ccit_x_509_B_Na
          name_44 = arbitrary_B_ccit_x_509.ccit_x_509_B_b
          text_45 = arbitrary_B_ccit_x_509.ccit_x_509_B_Xa
          learnt_term_by[getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_b],arbitrary_B_ccit_x_509.agent,t0]
          inds[(enc_46).plaintext.components] = 0
          let text_48  = ((enc_46).plaintext.components)[0] | {
            (enc_46).plaintext.components = 0->text_48
            text_48 = arbitrary_B_ccit_x_509.ccit_x_509_B_Ya
          }
          (enc_46).encryptionKey = getPUBK[arbitrary_B_ccit_x_509.ccit_x_509_B_b]
        }}}}}
        (enc_36).encryptionKey = getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_a]
      }}

      t1.sender = arbitrary_B_ccit_x_509
      inds[((t1.data).components)] = 0+1
      let name_49  = (((t1.data).components))[0] | {
      let enc_50  = (((t1.data).components))[1] | {
        ((t1.data).components) = 0->name_49 + 1->enc_50
        name_49 = arbitrary_B_ccit_x_509.ccit_x_509_B_b
        inds[(enc_50).plaintext.components] = 0+1+2+3+4+5
        let text_57  = ((enc_50).plaintext.components)[0] | {
        let text_58  = ((enc_50).plaintext.components)[1] | {
        let name_59  = ((enc_50).plaintext.components)[2] | {
        let text_60  = ((enc_50).plaintext.components)[3] | {
        let text_61  = ((enc_50).plaintext.components)[4] | {
        let enc_62  = ((enc_50).plaintext.components)[5] | {
          (enc_50).plaintext.components = 0->text_57 + 1->text_58 + 2->name_59 + 3->text_60 + 4->text_61 + 5->enc_62
          text_57 = arbitrary_B_ccit_x_509.ccit_x_509_B_Tb
          text_58 = arbitrary_B_ccit_x_509.ccit_x_509_B_Nb
          name_59 = arbitrary_B_ccit_x_509.ccit_x_509_B_a
          text_60 = arbitrary_B_ccit_x_509.ccit_x_509_B_Na
          text_61 = arbitrary_B_ccit_x_509.ccit_x_509_B_Xb
          inds[(enc_62).plaintext.components] = 0
          let text_64  = ((enc_62).plaintext.components)[0] | {
            (enc_62).plaintext.components = 0->text_64
            text_64 = arbitrary_B_ccit_x_509.ccit_x_509_B_Yb
          }
          (enc_62).encryptionKey = getPUBK[arbitrary_B_ccit_x_509.ccit_x_509_B_a]
        }}}}}}
        (enc_50).encryptionKey = getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_b]
      }}

      t2.receiver = arbitrary_B_ccit_x_509
      inds[((t2.data).components)] = 0+1
      let name_65  = (((t2.data).components))[0] | {
      let enc_66  = (((t2.data).components))[1] | {
        ((t2.data).components) = 0->name_65 + 1->enc_66
        name_65 = arbitrary_B_ccit_x_509.ccit_x_509_B_a
        learnt_term_by[getPUBK[arbitrary_B_ccit_x_509.ccit_x_509_B_a],arbitrary_B_ccit_x_509.agent,t2]
        inds[(enc_66).plaintext.components] = 0
        let text_68  = ((enc_66).plaintext.components)[0] | {
          (enc_66).plaintext.components = 0->text_68
          text_68 = arbitrary_B_ccit_x_509.ccit_x_509_B_Nb
        }
        (enc_66).encryptionKey = getPRIVK[arbitrary_B_ccit_x_509.ccit_x_509_B_a]
      }}

    }}}
  }
}
inst honest_run_test {
  PublicKey = `PublicKey0 + `PublicKey1 + `PublicKey2
  PrivateKey = `PrivateKey0 + `PrivateKey1 + `PrivateKey2
  akey = PublicKey + PrivateKey
  no skey
  Key = akey
  Attacker = `Attacker0
  name = `name0 + `name1 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7 + `Ciphertext8 + `Ciphertext9
  text = `text0 + `text1 + `text2 + `text3 + `text4 + `text5 + `text6 + `text7 + `text8 + `text9 + `text10 + `text11
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10 + `tuple11
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5

  components in tuple -> (0+1+2+3+4+5) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  pairs = KeyPairs -> (`PrivateKey0->`PublicKey0 + `PrivateKey1->`PublicKey1 + `PrivateKey2->`PublicKey2)
  owners = KeyPairs -> (`PrivateKey0->`name0 + `PrivateKey1->`name1 + `PrivateKey2->`Attacker0)
  no ltks

  `KeyPairs0.inv_key_helper = `PublicKey0->`PrivateKey0 + `PrivateKey0->`PublicKey0 + `PublicKey1->`PrivateKey1 + `PrivateKey1->`PublicKey1 + `PublicKey2->`PrivateKey2 + `PrivateKey2->`PublicKey2
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  ccit_x_509_A = `ccit_x_509_A0
  ccit_x_509_B = `ccit_x_509_B0
  AttackerStrand = `AttackerStrand0
  strand = ccit_x_509_A + ccit_x_509_B + AttackerStrand
}

option run_sterling "../../crypto_viz_seq_tuple.js"
option verbose 5
option solver Glucose

-- option solver MiniSatProver
-- option logtranslation 2
-- option coregranularity 1
-- option engine_verbosity 3
-- option core_minimization rce


pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

pred gen_honest_run{
    no (ccit_x_509_A.agent & ccit_x_509_B.agent)
}
pred originates_name[n:name,d:mesg]{
    some aStrand: (agent.n) | {
        originates[aStrand,d]
    }
}
-- TODO can add support for specifying this in defprotocol as a protocol level constraint clause perhaps
pred protocol_constr{
    all arbit_A : ccit_x_509_A | {
        arbit_A.ccit_x_509_A_b != Attacker => not corrected_attacker_learns[arbit_A.ccit_x_509_A_Ya]
        originates_name[arbit_A.ccit_x_509_A_b,arbit_A.ccit_x_509_A_Xb]
        originates_name[arbit_A.ccit_x_509_A_b,arbit_A.ccit_x_509_A_Yb]
    }
    all arbit_B : ccit_x_509_B | {
        arbit_B.ccit_x_509_B_a != Attacker => not corrected_attacker_learns[arbit_B.ccit_x_509_B_Yb]

        originates_name[arbit_B.ccit_x_509_B_a,arbit_B.ccit_x_509_B_Xa]
        originates_name[arbit_B.ccit_x_509_B_a,arbit_B.ccit_x_509_B_Ya]
    }
}

ccit_x_509_run : run {
    wellformed
    exec_ccit_x_509_A
    exec_ccit_x_509_B

    gen_honest_run
    not protocol_constr
}for
    exactly 4 Int
    for{
        next is linear
        honest_run_test
    }
