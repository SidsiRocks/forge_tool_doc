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
  ltks: set name -> name -> skey
}

/** Get a long-term key associated with a pair of agents */
fun getLTK[name_a: name, name_b: name]: lone skey {
    (KeyPairs.ltks)[name_a][name_b] + (KeyPairs.ltks)[name_b][name_a]
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
   plaintext: one tuple
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



/** This (large) predicate contains the vast majority of domain axioms */
pred wellformed {
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
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in elems[msg1.components]}} + plaintext | {
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
  let subterm_rel = {msg1:mesg,msg2:mesg | {msg2 in elems[msg1.components]}} + plaintext | {
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
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]] or generates [aStrand,getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]]
    }
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      t0+t1 = sender.arbitrary_A_ootway_rees + receiver.arbitrary_A_ootway_rees
      t0.sender = arbitrary_A_ootway_rees
      inds[(t0.data.components)] = 0+1+2+3
      let text_1  = ((t0.data.components))[0] | {
      let name_2  = ((t0.data.components))[1] | {
      let name_3  = ((t0.data.components))[2] | {
      let enc_4  = ((t0.data.components))[3] | {
        (t0.data.components) = 0->text_1 + 1->name_2 + 2->name_3 + 3->enc_4
        text_1 = arbitrary_A_ootway_rees.ootway_rees_A_m
        name_2 = arbitrary_A_ootway_rees.ootway_rees_A_a
        name_3 = arbitrary_A_ootway_rees.ootway_rees_A_b
        inds[(enc_4).plaintext.components] = 0+1+2+3
        let text_9  = ((enc_4).plaintext.components)[0] | {
        let text_10  = ((enc_4).plaintext.components)[1] | {
        let name_11  = ((enc_4).plaintext.components)[2] | {
        let name_12  = ((enc_4).plaintext.components)[3] | {
          (enc_4).plaintext.components = 0->text_9 + 1->text_10 + 2->name_11 + 3->name_12
          text_9 = arbitrary_A_ootway_rees.ootway_rees_A_na
          text_10 = arbitrary_A_ootway_rees.ootway_rees_A_m
          name_11 = arbitrary_A_ootway_rees.ootway_rees_A_a
          name_12 = arbitrary_A_ootway_rees.ootway_rees_A_b
        }}}}
        (enc_4).encryptionKey = getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]
      }}}}

      t1.receiver = arbitrary_A_ootway_rees
      inds[(t1.data.components)] = 0+1
      let text_13  = ((t1.data.components))[0] | {
      let enc_14  = ((t1.data.components))[1] | {
        (t1.data.components) = 0->text_13 + 1->enc_14
        text_13 = arbitrary_A_ootway_rees.ootway_rees_A_m
        learnt_term_by[getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s],arbitrary_A_ootway_rees.agent,t1]
        inds[(enc_14).plaintext.components] = 0+1
        let text_17  = ((enc_14).plaintext.components)[0] | {
        let skey_18  = ((enc_14).plaintext.components)[1] | {
          (enc_14).plaintext.components = 0->text_17 + 1->skey_18
          text_17 = arbitrary_A_ootway_rees.ootway_rees_A_na
          skey_18 = arbitrary_A_ootway_rees.ootway_rees_A_kab
        }}
        (enc_14).encryptionKey = getLTK[arbitrary_A_ootway_rees.ootway_rees_A_a,arbitrary_A_ootway_rees.ootway_rees_A_s]
      }}

    }}
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
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]] or generates [aStrand,getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]]
    }
    some t0 : Timeslot {
    some t1 : t0.(^next) {
    some t2 : t1.(^next) {
    some t3 : t2.(^next) {
      t0+t1+t2+t3 = sender.arbitrary_B_ootway_rees + receiver.arbitrary_B_ootway_rees
      t0.receiver = arbitrary_B_ootway_rees
      inds[(t0.data.components)] = 0+1+2+3
      let text_19  = ((t0.data.components))[0] | {
      let name_20  = ((t0.data.components))[1] | {
      let name_21  = ((t0.data.components))[2] | {
      let mesg_22  = ((t0.data.components))[3] | {
        (t0.data.components) = 0->text_19 + 1->name_20 + 2->name_21 + 3->mesg_22
        text_19 = arbitrary_B_ootway_rees.ootway_rees_B_m
        name_20 = arbitrary_B_ootway_rees.ootway_rees_B_a
        name_21 = arbitrary_B_ootway_rees.ootway_rees_B_b
        mesg_22 = arbitrary_B_ootway_rees.ootway_rees_B_first_a_s_mesg
      }}}}

      t1.sender = arbitrary_B_ootway_rees
      inds[(t1.data.components)] = 0+1+2+3+4
      let text_23  = ((t1.data.components))[0] | {
      let name_24  = ((t1.data.components))[1] | {
      let name_25  = ((t1.data.components))[2] | {
      let mesg_26  = ((t1.data.components))[3] | {
      let enc_27  = ((t1.data.components))[4] | {
        (t1.data.components) = 0->text_23 + 1->name_24 + 2->name_25 + 3->mesg_26 + 4->enc_27
        text_23 = arbitrary_B_ootway_rees.ootway_rees_B_m
        name_24 = arbitrary_B_ootway_rees.ootway_rees_B_a
        name_25 = arbitrary_B_ootway_rees.ootway_rees_B_b
        mesg_26 = arbitrary_B_ootway_rees.ootway_rees_B_first_a_s_mesg
        inds[(enc_27).plaintext.components] = 0+1+2+3
        let text_32  = ((enc_27).plaintext.components)[0] | {
        let text_33  = ((enc_27).plaintext.components)[1] | {
        let name_34  = ((enc_27).plaintext.components)[2] | {
        let name_35  = ((enc_27).plaintext.components)[3] | {
          (enc_27).plaintext.components = 0->text_32 + 1->text_33 + 2->name_34 + 3->name_35
          text_32 = arbitrary_B_ootway_rees.ootway_rees_B_nb
          text_33 = arbitrary_B_ootway_rees.ootway_rees_B_m
          name_34 = arbitrary_B_ootway_rees.ootway_rees_B_a
          name_35 = arbitrary_B_ootway_rees.ootway_rees_B_b
        }}}}
        (enc_27).encryptionKey = getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]
      }}}}}

      t2.receiver = arbitrary_B_ootway_rees
      inds[(t2.data.components)] = 0+1+2
      let text_36  = ((t2.data.components))[0] | {
      let mesg_37  = ((t2.data.components))[1] | {
      let enc_38  = ((t2.data.components))[2] | {
        (t2.data.components) = 0->text_36 + 1->mesg_37 + 2->enc_38
        text_36 = arbitrary_B_ootway_rees.ootway_rees_B_m
        mesg_37 = arbitrary_B_ootway_rees.ootway_rees_B_second_a_s_mesg
        learnt_term_by[getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s],arbitrary_B_ootway_rees.agent,t2]
        inds[(enc_38).plaintext.components] = 0+1
        let text_41  = ((enc_38).plaintext.components)[0] | {
        let skey_42  = ((enc_38).plaintext.components)[1] | {
          (enc_38).plaintext.components = 0->text_41 + 1->skey_42
          text_41 = arbitrary_B_ootway_rees.ootway_rees_B_nb
          skey_42 = arbitrary_B_ootway_rees.ootway_rees_B_kab
        }}
        (enc_38).encryptionKey = getLTK[arbitrary_B_ootway_rees.ootway_rees_B_b,arbitrary_B_ootway_rees.ootway_rees_B_s]
      }}}

      t3.sender = arbitrary_B_ootway_rees
      inds[(t3.data.components)] = 0+1
      let text_43  = ((t3.data.components))[0] | {
      let mesg_44  = ((t3.data.components))[1] | {
        (t3.data.components) = 0->text_43 + 1->mesg_44
        text_43 = arbitrary_B_ootway_rees.ootway_rees_B_m
        mesg_44 = arbitrary_B_ootway_rees.ootway_rees_B_second_a_s_mesg
      }}

    }}}}
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
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]] or generates [aStrand,getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]] or generates [aStrand,getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]]
    }
    some t0 : Timeslot {
    some t1 : t0.(^next) {
      t0+t1 = sender.arbitrary_S_ootway_rees + receiver.arbitrary_S_ootway_rees
      t0.receiver = arbitrary_S_ootway_rees
      inds[(t0.data.components)] = 0+1+2+3+4
      let text_45  = ((t0.data.components))[0] | {
      let name_46  = ((t0.data.components))[1] | {
      let name_47  = ((t0.data.components))[2] | {
      let enc_48  = ((t0.data.components))[3] | {
      let enc_49  = ((t0.data.components))[4] | {
        (t0.data.components) = 0->text_45 + 1->name_46 + 2->name_47 + 3->enc_48 + 4->enc_49
        text_45 = arbitrary_S_ootway_rees.ootway_rees_S_m
        name_46 = arbitrary_S_ootway_rees.ootway_rees_S_a
        name_47 = arbitrary_S_ootway_rees.ootway_rees_S_b
        learnt_term_by[getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s],arbitrary_S_ootway_rees.agent,t0]
        inds[(enc_48).plaintext.components] = 0+1+2+3
        let text_54  = ((enc_48).plaintext.components)[0] | {
        let text_55  = ((enc_48).plaintext.components)[1] | {
        let name_56  = ((enc_48).plaintext.components)[2] | {
        let name_57  = ((enc_48).plaintext.components)[3] | {
          (enc_48).plaintext.components = 0->text_54 + 1->text_55 + 2->name_56 + 3->name_57
          text_54 = arbitrary_S_ootway_rees.ootway_rees_S_na
          text_55 = arbitrary_S_ootway_rees.ootway_rees_S_m
          name_56 = arbitrary_S_ootway_rees.ootway_rees_S_a
          name_57 = arbitrary_S_ootway_rees.ootway_rees_S_b
        }}}}
        (enc_48).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]
        learnt_term_by[getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s],arbitrary_S_ootway_rees.agent,t0]
        inds[(enc_49).plaintext.components] = 0+1+2+3
        let text_62  = ((enc_49).plaintext.components)[0] | {
        let text_63  = ((enc_49).plaintext.components)[1] | {
        let name_64  = ((enc_49).plaintext.components)[2] | {
        let name_65  = ((enc_49).plaintext.components)[3] | {
          (enc_49).plaintext.components = 0->text_62 + 1->text_63 + 2->name_64 + 3->name_65
          text_62 = arbitrary_S_ootway_rees.ootway_rees_S_nb
          text_63 = arbitrary_S_ootway_rees.ootway_rees_S_m
          name_64 = arbitrary_S_ootway_rees.ootway_rees_S_a
          name_65 = arbitrary_S_ootway_rees.ootway_rees_S_b
        }}}}
        (enc_49).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]
      }}}}}

      t1.sender = arbitrary_S_ootway_rees
      inds[(t1.data.components)] = 0+1+2
      let text_66  = ((t1.data.components))[0] | {
      let enc_67  = ((t1.data.components))[1] | {
      let enc_68  = ((t1.data.components))[2] | {
        (t1.data.components) = 0->text_66 + 1->enc_67 + 2->enc_68
        text_66 = arbitrary_S_ootway_rees.ootway_rees_S_m
        inds[(enc_67).plaintext.components] = 0+1
        let text_71  = ((enc_67).plaintext.components)[0] | {
        let skey_72  = ((enc_67).plaintext.components)[1] | {
          (enc_67).plaintext.components = 0->text_71 + 1->skey_72
          text_71 = arbitrary_S_ootway_rees.ootway_rees_S_na
          skey_72 = arbitrary_S_ootway_rees.ootway_rees_S_kab
        }}
        (enc_67).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_a,arbitrary_S_ootway_rees.ootway_rees_S_s]
        inds[(enc_68).plaintext.components] = 0+1
        let text_75  = ((enc_68).plaintext.components)[0] | {
        let skey_76  = ((enc_68).plaintext.components)[1] | {
          (enc_68).plaintext.components = 0->text_75 + 1->skey_76
          text_75 = arbitrary_S_ootway_rees.ootway_rees_S_nb
          skey_76 = arbitrary_S_ootway_rees.ootway_rees_S_kab
        }}
        (enc_68).encryptionKey = getLTK[arbitrary_S_ootway_rees.ootway_rees_S_b,arbitrary_S_ootway_rees.ootway_rees_S_s]
      }}}

    }}
  }
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2 + `text3 + `text4 + `text5
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10 + `tuple11 + `tuple12 + `tuple13 + `tuple14 + `tuple15
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1+2+3+4) -> (Key + name + text + Ciphertext + tuple)
  Microtick = `Microtick0 + `Microtick1
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name1->`name2->`skey2
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6 + `Timeslot6->`Timeslot7
  mt_next = `Microtick0 -> `Microtick1

  generated_times in name -> (Key + text) -> Timeslot
  ootway_rees_A = `ootway_rees_A0
  ootway_rees_B = `ootway_rees_B0
  ootway_rees_S = `ootway_rees_S0
  AttackerStrand = `AttackerStrand0
  strand = ootway_rees_A + ootway_rees_B + ootway_rees_S + AttackerStrand
}
one sig skeleton_honest_run_with_1_ABS_0 {
  skeleton_honest_run_with_1_ABS_0_a : one name,
  skeleton_honest_run_with_1_ABS_0_b : one name,
  skeleton_honest_run_with_1_ABS_0_s : one name,
  skeleton_honest_run_with_1_ABS_0_m : one text,
  skeleton_honest_run_with_1_ABS_0_na : one text,
  skeleton_honest_run_with_1_ABS_0_nb : one text,
  skeleton_honest_run_with_1_ABS_0_kab : one skey,
  skeleton_honest_run_with_1_ABS_0_A : one ootway_rees_A,
  skeleton_honest_run_with_1_ABS_0_B : one ootway_rees_B,
  skeleton_honest_run_with_1_ABS_0_S : one ootway_rees_S
}
pred constrain_skeleton_honest_run_with_1_ABS_0_honest_run {
  some t_0 : Timeslot {
  some t_1 : t_0.(^next) {
  some t_2 : t_1.(^next) {
  some t_3 : t_2.(^next) {
  some t_4 : t_3.(^next) {
  some t_5 : t_4.(^next) {
  some t_6 : t_5.(^next) {
  some t_7 : t_6.(^next) {
    t_0.sender = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_A
    inds[(t_0.data.components)] = 0+1+2+3
    let text_77  = ((t_0.data.components))[0] | {
    let name_78  = ((t_0.data.components))[1] | {
    let name_79  = ((t_0.data.components))[2] | {
    let enc_80  = ((t_0.data.components))[3] | {
      (t_0.data.components) = 0->text_77 + 1->name_78 + 2->name_79 + 3->enc_80
      text_77 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      name_78 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
      name_79 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      inds[(enc_80).plaintext.components] = 0+1+2+3
      let text_85  = ((enc_80).plaintext.components)[0] | {
      let text_86  = ((enc_80).plaintext.components)[1] | {
      let name_87  = ((enc_80).plaintext.components)[2] | {
      let name_88  = ((enc_80).plaintext.components)[3] | {
        (enc_80).plaintext.components = 0->text_85 + 1->text_86 + 2->name_87 + 3->name_88
        text_85 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        text_86 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_87 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_88 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_80).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}}

    t_1.receiver = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_B
    inds[(t_1.data.components)] = 0+1+2+3
    let text_89  = ((t_1.data.components))[0] | {
    let name_90  = ((t_1.data.components))[1] | {
    let name_91  = ((t_1.data.components))[2] | {
    let enc_92  = ((t_1.data.components))[3] | {
      (t_1.data.components) = 0->text_89 + 1->name_90 + 2->name_91 + 3->enc_92
      text_89 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      name_90 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
      name_91 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      inds[(enc_92).plaintext.components] = 0+1+2+3
      let text_97  = ((enc_92).plaintext.components)[0] | {
      let text_98  = ((enc_92).plaintext.components)[1] | {
      let name_99  = ((enc_92).plaintext.components)[2] | {
      let name_100  = ((enc_92).plaintext.components)[3] | {
        (enc_92).plaintext.components = 0->text_97 + 1->text_98 + 2->name_99 + 3->name_100
        text_97 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        text_98 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_99 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_100 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_92).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}}

    t_2.sender = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_B
    inds[(t_2.data.components)] = 0+1+2+3+4
    let text_101  = ((t_2.data.components))[0] | {
    let name_102  = ((t_2.data.components))[1] | {
    let name_103  = ((t_2.data.components))[2] | {
    let enc_104  = ((t_2.data.components))[3] | {
    let enc_105  = ((t_2.data.components))[4] | {
      (t_2.data.components) = 0->text_101 + 1->name_102 + 2->name_103 + 3->enc_104 + 4->enc_105
      text_101 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      name_102 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
      name_103 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      inds[(enc_104).plaintext.components] = 0+1+2+3
      let text_110  = ((enc_104).plaintext.components)[0] | {
      let text_111  = ((enc_104).plaintext.components)[1] | {
      let name_112  = ((enc_104).plaintext.components)[2] | {
      let name_113  = ((enc_104).plaintext.components)[3] | {
        (enc_104).plaintext.components = 0->text_110 + 1->text_111 + 2->name_112 + 3->name_113
        text_110 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        text_111 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_112 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_113 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_104).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
      inds[(enc_105).plaintext.components] = 0+1+2+3
      let text_118  = ((enc_105).plaintext.components)[0] | {
      let text_119  = ((enc_105).plaintext.components)[1] | {
      let name_120  = ((enc_105).plaintext.components)[2] | {
      let name_121  = ((enc_105).plaintext.components)[3] | {
        (enc_105).plaintext.components = 0->text_118 + 1->text_119 + 2->name_120 + 3->name_121
        text_118 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_nb
        text_119 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_120 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_121 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_105).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}}}

    t_3.receiver = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_S
    inds[(t_3.data.components)] = 0+1+2+3+4
    let text_122  = ((t_3.data.components))[0] | {
    let name_123  = ((t_3.data.components))[1] | {
    let name_124  = ((t_3.data.components))[2] | {
    let enc_125  = ((t_3.data.components))[3] | {
    let enc_126  = ((t_3.data.components))[4] | {
      (t_3.data.components) = 0->text_122 + 1->name_123 + 2->name_124 + 3->enc_125 + 4->enc_126
      text_122 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      name_123 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
      name_124 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      inds[(enc_125).plaintext.components] = 0+1+2+3
      let text_131  = ((enc_125).plaintext.components)[0] | {
      let text_132  = ((enc_125).plaintext.components)[1] | {
      let name_133  = ((enc_125).plaintext.components)[2] | {
      let name_134  = ((enc_125).plaintext.components)[3] | {
        (enc_125).plaintext.components = 0->text_131 + 1->text_132 + 2->name_133 + 3->name_134
        text_131 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        text_132 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_133 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_134 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_125).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
      inds[(enc_126).plaintext.components] = 0+1+2+3
      let text_139  = ((enc_126).plaintext.components)[0] | {
      let text_140  = ((enc_126).plaintext.components)[1] | {
      let name_141  = ((enc_126).plaintext.components)[2] | {
      let name_142  = ((enc_126).plaintext.components)[3] | {
        (enc_126).plaintext.components = 0->text_139 + 1->text_140 + 2->name_141 + 3->name_142
        text_139 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_nb
        text_140 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
        name_141 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
        name_142 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
      }}}}
      (enc_126).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}}}

    t_4.sender = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_S
    inds[(t_4.data.components)] = 0+1+2
    let text_143  = ((t_4.data.components))[0] | {
    let enc_144  = ((t_4.data.components))[1] | {
    let enc_145  = ((t_4.data.components))[2] | {
      (t_4.data.components) = 0->text_143 + 1->enc_144 + 2->enc_145
      text_143 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      inds[(enc_144).plaintext.components] = 0+1
      let text_148  = ((enc_144).plaintext.components)[0] | {
      let skey_149  = ((enc_144).plaintext.components)[1] | {
        (enc_144).plaintext.components = 0->text_148 + 1->skey_149
        text_148 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        skey_149 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_144).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
      inds[(enc_145).plaintext.components] = 0+1
      let text_152  = ((enc_145).plaintext.components)[0] | {
      let skey_153  = ((enc_145).plaintext.components)[1] | {
        (enc_145).plaintext.components = 0->text_152 + 1->skey_153
        text_152 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_nb
        skey_153 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_145).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}

    t_5.receiver = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_B
    inds[(t_5.data.components)] = 0+1+2
    let text_154  = ((t_5.data.components))[0] | {
    let enc_155  = ((t_5.data.components))[1] | {
    let enc_156  = ((t_5.data.components))[2] | {
      (t_5.data.components) = 0->text_154 + 1->enc_155 + 2->enc_156
      text_154 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      inds[(enc_155).plaintext.components] = 0+1
      let text_159  = ((enc_155).plaintext.components)[0] | {
      let skey_160  = ((enc_155).plaintext.components)[1] | {
        (enc_155).plaintext.components = 0->text_159 + 1->skey_160
        text_159 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        skey_160 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_155).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
      inds[(enc_156).plaintext.components] = 0+1
      let text_163  = ((enc_156).plaintext.components)[0] | {
      let skey_164  = ((enc_156).plaintext.components)[1] | {
        (enc_156).plaintext.components = 0->text_163 + 1->skey_164
        text_163 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_nb
        skey_164 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_156).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}}

    t_6.sender = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_B
    inds[(t_6.data.components)] = 0+1
    let text_165  = ((t_6.data.components))[0] | {
    let enc_166  = ((t_6.data.components))[1] | {
      (t_6.data.components) = 0->text_165 + 1->enc_166
      text_165 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      inds[(enc_166).plaintext.components] = 0+1
      let text_169  = ((enc_166).plaintext.components)[0] | {
      let skey_170  = ((enc_166).plaintext.components)[1] | {
        (enc_166).plaintext.components = 0->text_169 + 1->skey_170
        text_169 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        skey_170 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_166).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}

    t_7.receiver = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_A
    inds[(t_7.data.components)] = 0+1
    let text_171  = ((t_7.data.components))[0] | {
    let enc_172  = ((t_7.data.components))[1] | {
      (t_7.data.components) = 0->text_171 + 1->enc_172
      text_171 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_m
      inds[(enc_172).plaintext.components] = 0+1
      let text_175  = ((enc_172).plaintext.components)[0] | {
      let skey_176  = ((enc_172).plaintext.components)[1] | {
        (enc_172).plaintext.components = 0->text_175 + 1->skey_176
        text_175 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_na
        skey_176 = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_kab
      }}
      (enc_172).encryptionKey = getLTK[skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a,skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s]
    }}

  }}}}}}}}
}
pred constrain_skeleton_honest_run_with_1_ABS_0 {
  some skeleton_A_0_strand_0 : ootway_rees_A | {
    skeleton_A_0_strand_0.ootway_rees_A_a = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
    skeleton_A_0_strand_0.ootway_rees_A_b = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
    skeleton_A_0_strand_0.ootway_rees_A_s = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s
  }
  some skeleton_B_0_strand_1 : ootway_rees_B | {
    skeleton_B_0_strand_1.ootway_rees_B_a = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
    skeleton_B_0_strand_1.ootway_rees_B_b = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
    skeleton_B_0_strand_1.ootway_rees_B_s = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s
  }
  some skeleton_S_0_strand_2 : ootway_rees_S | {
    skeleton_S_0_strand_2.ootway_rees_S_a = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_a
    skeleton_S_0_strand_2.ootway_rees_S_b = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_b
    skeleton_S_0_strand_2.ootway_rees_S_s = skeleton_honest_run_with_1_ABS_0.skeleton_honest_run_with_1_ABS_0_s
  }
  constrain_skeleton_honest_run_with_1_ABS_0_honest_run
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose

option logtranslation 1
option coregranularity 1
option core_minimization rce

pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}

ootway_rees_prot_run: run {
    wellformed
    exec_ootway_rees_A
    exec_ootway_rees_B
    exec_ootway_rees_S
    constrain_skeleton_honest_run_with_1_ABS_0

    ootway_rees_A.agent != ootway_rees_B.agent
    ootway_rees_A.agent != ootway_rees_S.agent
    ootway_rees_B.agent != ootway_rees_S.agent
}for
  exactly 4 Int
  for{
      next is linear
      mt_next is linear
      honest_run_bounds
  }
--    exactly 8 Timeslot,
--    exactly 37 mesg,
--    exactly 4 Key,exactly 3 name,exactly 8 Ciphertext,exactly 6 text,exactly 16 tuple,
--    exactly 0 akey,exactly 4 skey,exactly 1 Attacker,
--    exactly 0 PublicKey,exactly 0 PrivateKey,
--    exactly 2 Microtick,
--    exactly 1 ootway_rees_A,exactly 1 ootway_rees_B,exactly 1 ootway_rees_S,
--    exactly 4 Int
--    for{
--        next is linear
--        mt_next is linear
--    }
