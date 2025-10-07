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
  data: one mesg,
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
   plaintext: one mesg
}

-- Non-name base value (e.g., nonces)
sig text extends mesg {}
sig tuple extends mesg {
    components: pfunc Int -> mesg
}
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
  -- Constraint ensures that m.components is a well formed sequence
  all m: tuple | isSeqOf[m.components,mesg]

  -- someone cannot send a message to themselves
  all m: Timeslot | m.sender not in m.receiver

  -- workspace: workaround to avoid cyclic justification within just deconstructions
  -- AGENT -> TICK -> MICRO-TICK LEARNED_SUBTERM
  all d: mesg | all t, microt: Timeslot | let a = t.receiver.agent | d in (workspace[t])[microt] iff {
    -- Base case:
    -- received the data in the clear just now 
    {d in t.data and no microt.~next}
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
      d in superterm.plaintext and     
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a] and
      getInv[superterm.encryptionKey] in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}
    or
    {some superterm: tuple | {
      d in elems[superterm.components] and
      superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
    }}
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
      d in workspace[t][Timeslot] -- derived in any micro-tick in this (reception) timeslot
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

    -- Only build up tuples when sending a message no need to breakdown when receiving a message
    -- (breakdown of tuples handled inside microtick idea probably do not need it inside)
    -- NOTE: this means maximum nesting which can be broken down currently depends on the number of timeslots in the trae
    -- this is undesirable as with the addition of a tuple inside every encrypted term the depth will certainly increase
    { d in tuple and 
      elems[d.components] in (a.learned_times).(Timeslot - t.^next) and
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
  -- Now the only type contatining data is tuple and Ciphertext so only have to write 
  -- constraint for those two
    let components_relation = {msg1:mesg,msg2:mesg | {msg2 in (elems[msg1.components] + msg1.plaintext)}} | {
    all d: mesg | d not in d.^(components_relation)
  }
  -- Disallow empty tuples
  -- TODO might not need elemes here just some works
  all t: tuple | some elems[t.components]

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
  let components_relation = {tpl:tuple,msg:mesg | {msg in elems[tuple.components]}} | {
    supers + supers.^(components_relation + plaintext) -- union on new subterm relations inside parens
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
    m in (a.learned_times).(Timeslot - t.^next)
}

sig simple_enc_init extends strand {
  simple_enc_init_a : one name,
  simple_enc_init_b : one name
}
pred exec_simple_enc_init {
  all arbitrary_init_simple_enc : simple_enc_init | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        t0+t1 = sender.arbitrary_init_simple_enc + receiver.arbitrary_init_simple_enc
        t0.sender = arbitrary_init_simple_enc
        (t0.data) in tuple
        inds[((t0.data).components)] = 0
        some enc_2 : elems[((t0.data).components)] | {
          ((t0.data).components)[0] = enc_2
          ((enc_2).plaintext) in tuple
          inds[(((enc_2).plaintext).components)] = 0
          (((enc_2).plaintext).components)[0] = arbitrary_init_simple_enc.simple_enc_init_a
          ((enc_2).encryptionKey) = getPUBK[arbitrary_init_simple_enc.simple_enc_init_b]
        }

        t1.receiver = arbitrary_init_simple_enc
        (t1.data) in tuple
        inds[((t1.data).components)] = 0
        some enc_5 : elems[((t1.data).components)] | {
          ((t1.data).components)[0] = enc_5
          learnt_term_by[getPRIVK[arbitrary_init_simple_enc.simple_enc_init_a],arbitrary_init_simple_enc.agent,t1]
          ((enc_5).plaintext) in tuple
          inds[(((enc_5).plaintext).components)] = 0
          (((enc_5).plaintext).components)[0] = arbitrary_init_simple_enc.simple_enc_init_b
          ((enc_5).encryptionKey) = getPUBK[arbitrary_init_simple_enc.simple_enc_init_a]
        }

      }
    }
  }
}
sig simple_enc_resp extends strand {
  simple_enc_resp_a : one name,
  simple_enc_resp_b : one name
}
pred exec_simple_enc_resp {
  all arbitrary_resp_simple_enc : simple_enc_resp | {
    some t0 : Timeslot {
      some t1 : t0.(^next) {
        t0+t1 = sender.arbitrary_resp_simple_enc + receiver.arbitrary_resp_simple_enc
        t0.receiver = arbitrary_resp_simple_enc
        (t0.data) in tuple
        inds[((t0.data).components)] = 0
        some enc_8 : elems[((t0.data).components)] | {
          ((t0.data).components)[0] = enc_8
          learnt_term_by[getPRIVK[arbitrary_resp_simple_enc.simple_enc_resp_b],arbitrary_resp_simple_enc.agent,t0]
          ((enc_8).plaintext) in tuple
          inds[(((enc_8).plaintext).components)] = 0
          (((enc_8).plaintext).components)[0] = arbitrary_resp_simple_enc.simple_enc_resp_a
          ((enc_8).encryptionKey) = getPUBK[arbitrary_resp_simple_enc.simple_enc_resp_b]
        }

        t1.sender = arbitrary_resp_simple_enc
        (t1.data) in tuple
        inds[((t1.data).components)] = 0
        some enc_11 : elems[((t1.data).components)] | {
          ((t1.data).components)[0] = enc_11
          ((enc_11).plaintext) in tuple
          inds[(((enc_11).plaintext).components)] = 0
          (((enc_11).plaintext).components)[0] = arbitrary_resp_simple_enc.simple_enc_resp_b
          ((enc_11).encryptionKey) = getPUBK[arbitrary_resp_simple_enc.simple_enc_resp_a]
        }

      }
    }
  }
}
one sig skeleton_simple_enc_0 {
  skeleton_simple_enc_0_a : one name,
  skeleton_simple_enc_0_b : one name
}
pred constrain_skeleton_simple_enc_0 {
  some skeleton_init_0_strand_0 : simple_enc_init | {
    skeleton_init_0_strand_0.simple_enc_init_a = skeleton_simple_enc_0.skeleton_simple_enc_0_a
    skeleton_init_0_strand_0.simple_enc_init_b = skeleton_simple_enc_0.skeleton_simple_enc_0_b
  }
  some skeleton_resp_0_strand_1 : simple_enc_resp | {
    skeleton_resp_0_strand_1.simple_enc_resp_a = skeleton_simple_enc_0.skeleton_simple_enc_0_a
    skeleton_resp_0_strand_1.simple_enc_resp_b = skeleton_simple_enc_0.skeleton_simple_enc_0_b
  }
}
option run_sterling "../../crypto_viz_tuple.js"

option solver MiniSatProver
option logtranslation 1
option coregranularity 1
option core_minimization rce

simple_enc_responder_pov: run {
    wellformed

    exec_simple_enc_init
    exec_simple_enc_resp
    constrain_skeleton_simple_enc_0

    simple_enc_resp.agent != simple_enc_init.agent

    simple_enc_init.simple_enc_init_a = simple_enc_init.agent
    simple_enc_resp.simple_enc_resp_b = simple_enc_resp.agent
}for 
    exactly 4 Timeslot,20 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,0 skey,
    exactly 3 PrivateKey, exactly 3 PublicKey,
    --it seems like if you mention exactly then bit-width 
    --of Int can be 1 (maybe no counting needed internally)
    --writing exactly makes it work though
    
    --also seem like if you do not mention exactly then 
    --the execution is not rendered properly
    exactly 3 name,0 text,exactly 4 Ciphertext,
    exactly 1 simple_enc_init,exactly 1 simple_enc_resp,
    2 Int
for {next is linear}
