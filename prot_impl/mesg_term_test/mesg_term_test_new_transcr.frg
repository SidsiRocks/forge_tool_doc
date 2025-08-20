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
  (KeyPairs.ltks)[name_a][name_b]
}

/** Get the inverse key for a given key (if any) */
fun getInv[k: Key]: one Key {
  (k in PublicKey => ((KeyPairs.pairs).k) else none)
  +
  (k in PrivateKey => (k.(KeyPairs.pairs)) else none)
  +
  (k in skey => k else none)
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
   plaintext: pfunc Int -> mesg
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

/** This (large) predicate contains the vast majority of domain axioms */
pred wellformed {
  -- Design choice: only one message event per timeslot;
  --   assume we have a shared notion of time
  all m: Timeslot | isSeqOf[m.data,mesg]
  all t: Ciphertext | isSeqOf[t.plaintext,mesg]
  -- You cannot send a message with no data
  all m: Timeslot | some elems[m.data]

  -- someone cannot send a message to themselves
  all m: Timeslot | m.sender not in m.receiver

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
    -- construct encrypted terms (only allow at NON-reception time; see above)
    -- NOTE WELL: if ever allow an agent to send/receive at same time, need rewrite 
    {d in Ciphertext and 
	   d.encryptionKey in (a.learned_times).(Timeslot - t.^next) and        
	   elems[d.plaintext] in (a.learned_times).(Timeslot - t.^next)
     {a not in t.receiver.agent} -- non-reception
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
  all m: Timeslot | elems[m.data] in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
  -- Always send or receive to the adversary
  all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 

  -- plaintext relation is acyclic  
  --  NOTE WELL: if ever add another type of mesg that contains data, add with + inside ^.
  --old_plainw ould be unique so some or all doesn't
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
    all d: mesg | d not in d.^(old_plain)
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
  let old_plain = {cipher: Ciphertext,msg:mesg | {msg in elems[cipher.plaintext]}} | {
    supers + supers.^(old_plain) -- union on new subterm relations inside parens
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


fun getPRIVK[name_a:name] : lone Key{
    (KeyPairs.owners).name_a
}
fun getPUBK[name_a:name] : lone Key {
    (KeyPairs.owners.(name_a)).(KeyPairs.pairs)
}
pred learnt_term_by[m:mesg,a:name,t:Timeslot] {
    m in (a.learned_times).(Timeslot - t.^next)
}

sig mesg_term_test_A extends strand {
  mesg_term_test_A_a : one name,
  mesg_term_test_A_b : one name,
  mesg_term_test_A_n1 : one text
}
pred exec_mesg_term_test_A {
  all arbitrary_A_mesg_term_test : mesg_term_test_A | {
    some t0,t1 : Timeslot | {
      t1 in t0.(^next)
      t0+t1 = sender.arbitrary_A_mesg_term_test + receiver.arbitrary_A_mesg_term_test
      t0.sender = arbitrary_A_mesg_term_test
      inds[(t0.data)] = 0
      some atom_1 : elems[(t0.data)] | {
        (t0.data)[0] = atom_1
        inds[(atom_1).plaintext] = 0
        some atom_2 : elems[(atom_1).plaintext] | {
          (atom_1).plaintext[0] = atom_2
          atom_2 = arbitrary_A_mesg_term_test.mesg_term_test_A_n1
        }
        (atom_1).encryptionKey = getPUBK[arbitrary_A_mesg_term_test.mesg_term_test_A_a]
      }
      
      t1.receiver = arbitrary_A_mesg_term_test
      inds[(t1.data)] = 0
      some atom_3 : elems[(t1.data)] | {
        (t1.data)[0] = atom_3
        learnt_term_by[getPRIVK[arbitrary_A_mesg_term_test.mesg_term_test_A_a],arbitrary_A_mesg_term_test.agent,t1]
        inds[(atom_3).plaintext] = 0
        some atom_4 : elems[(atom_3).plaintext] | {
          (atom_3).plaintext[0] = atom_4
          atom_4 = arbitrary_A_mesg_term_test.mesg_term_test_A_n1
        }
        (atom_3).encryptionKey = getPUBK[arbitrary_A_mesg_term_test.mesg_term_test_A_a]
      }
      
    }
  }
}
sig mesg_term_test_B extends strand {
  mesg_term_test_B_a : one name,
  mesg_term_test_B_b : one name,
  mesg_term_test_B_m : one mesg
}
pred exec_mesg_term_test_B {
  all arbitrary_B_mesg_term_test : mesg_term_test_B | {
    some t0,t1 : Timeslot | {
      t1 in t0.(^next)
      t0+t1 = sender.arbitrary_B_mesg_term_test + receiver.arbitrary_B_mesg_term_test
      t0.receiver = arbitrary_B_mesg_term_test
      inds[(t0.data)] = 0
      some atom_5 : elems[(t0.data)] | {
        (t0.data)[0] = atom_5
        atom_5 = arbitrary_B_mesg_term_test.mesg_term_test_B_m
      }
      
      t1.sender = arbitrary_B_mesg_term_test
      inds[(t1.data)] = 0
      some atom_6 : elems[(t1.data)] | {
        (t1.data)[0] = atom_6
        atom_6 = arbitrary_B_mesg_term_test.mesg_term_test_B_m
      }
      
    }
  }
}
option run_sterling "../../crypto_viz_seq.js"

-- TODO add something to auto generate common parts of base file
-- end up making silly mistakes like not including pred weillformed
mesg_term_test_run : run {
    wellformed 

    exec_mesg_term_test_A
    exec_mesg_term_test_B

    mesg_term_test_A.agent != AttackerStrand.agent
    mesg_term_test_B.agent != AttackerStrand.agent
    mesg_term_test_A.agent != mesg_term_test_B.agent

    mesg_term_test_B.mesg_term_test_B_m in Ciphertext
} for 
    exactly 4 Timeslot,25 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,

    exactly 3 name,exactly 2 text,exactly 2 Ciphertext,
    exactly 1 mesg_term_test_A,exactly 1 mesg_term_test_B,
    4 Int
for {next is linear}