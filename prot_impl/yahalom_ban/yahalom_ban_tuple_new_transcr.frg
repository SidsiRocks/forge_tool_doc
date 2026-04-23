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

sig yahalom_ban_init extends strand {
  yahalom_ban_init_a : one name,
  yahalom_ban_init_b : one name,
  yahalom_ban_init_s : one name,
  yahalom_ban_init_Na : one text,
  yahalom_ban_init_Nb : one text,
  yahalom_ban_init_Kab : one skey,
  yahalom_ban_init_msg : one mesg
}
pred exec_yahalom_ban_init_mesg_0[t0:Timeslot,arbitrary_init_yahalom_ban:yahalom_ban_init]{
  t0.sender = arbitrary_init_yahalom_ban
  inds[((t0.data).components)] = 0+1
  let name_1  = (((t0.data).components))[0] | {
  let text_2  = (((t0.data).components))[1] | {
    ((t0.data).components) = 0->name_1 + 1->text_2
    name_1 = arbitrary_init_yahalom_ban.yahalom_ban_init_a
    text_2 = arbitrary_init_yahalom_ban.yahalom_ban_init_Na
  }}
}
pred exec_yahalom_ban_init_mesg_1[t1:Timeslot,arbitrary_init_yahalom_ban:yahalom_ban_init]{
  t1.receiver = arbitrary_init_yahalom_ban
  inds[((t1.data).components)] = 0+1+2
  let text_3  = (((t1.data).components))[0] | {
  let enc_4  = (((t1.data).components))[1] | {
  let mesg_5  = (((t1.data).components))[2] | {
    ((t1.data).components) = 0->text_3 + 1->enc_4 + 2->mesg_5
    text_3 = arbitrary_init_yahalom_ban.yahalom_ban_init_Nb
    learnt_term_by[getLTK[arbitrary_init_yahalom_ban.yahalom_ban_init_a,arbitrary_init_yahalom_ban.yahalom_ban_init_s],arbitrary_init_yahalom_ban.agent,t1]
    inds[(enc_4).plaintext.components] = 0+1+2
    let name_9  = ((enc_4).plaintext.components)[0] | {
    let skey_10  = ((enc_4).plaintext.components)[1] | {
    let text_11  = ((enc_4).plaintext.components)[2] | {
      (enc_4).plaintext.components = 0->name_9 + 1->skey_10 + 2->text_11
      name_9 = arbitrary_init_yahalom_ban.yahalom_ban_init_b
      skey_10 = arbitrary_init_yahalom_ban.yahalom_ban_init_Kab
      text_11 = arbitrary_init_yahalom_ban.yahalom_ban_init_Na
    }}}
    (enc_4).encryptionKey = getLTK[arbitrary_init_yahalom_ban.yahalom_ban_init_a,arbitrary_init_yahalom_ban.yahalom_ban_init_s]
    mesg_5 = arbitrary_init_yahalom_ban.yahalom_ban_init_msg
  }}}
}
pred exec_yahalom_ban_init_mesg_2[t2:Timeslot,arbitrary_init_yahalom_ban:yahalom_ban_init]{
  t2.sender = arbitrary_init_yahalom_ban
  inds[((t2.data).components)] = 0+1
  let mesg_12  = (((t2.data).components))[0] | {
  let enc_13  = (((t2.data).components))[1] | {
    ((t2.data).components) = 0->mesg_12 + 1->enc_13
    mesg_12 = arbitrary_init_yahalom_ban.yahalom_ban_init_msg
    inds[(enc_13).plaintext.components] = 0
    let text_15  = ((enc_13).plaintext.components)[0] | {
      (enc_13).plaintext.components = 0->text_15
      text_15 = arbitrary_init_yahalom_ban.yahalom_ban_init_Nb
    }
    (enc_13).encryptionKey = arbitrary_init_yahalom_ban.yahalom_ban_init_Kab
  }}
}
pred exec_init_trace_len_0[arbitrary_init_yahalom_ban:yahalom_ban_init]{
  no (sender.arbitrary_init_yahalom_ban + receiver.arbitrary_init_yahalom_ban)
}
pred exec_init_trace_len_1[arbitrary_init_yahalom_ban:yahalom_ban_init]{
  some t0 : Timeslot {
    t0 = sender.arbitrary_init_yahalom_ban + receiver.arbitrary_init_yahalom_ban
    exec_yahalom_ban_init_mesg_0[t0,arbitrary_init_yahalom_ban]
  }
}
pred exec_init_trace_len_2[arbitrary_init_yahalom_ban:yahalom_ban_init]{
  some t0 : Timeslot {
  some t1 : t0.(^next) {
    t0+t1 = sender.arbitrary_init_yahalom_ban + receiver.arbitrary_init_yahalom_ban
    exec_yahalom_ban_init_mesg_0[t0,arbitrary_init_yahalom_ban]
    exec_yahalom_ban_init_mesg_1[t1,arbitrary_init_yahalom_ban]
  }}
}
pred exec_init_trace_len_3[arbitrary_init_yahalom_ban:yahalom_ban_init]{
  some t0 : Timeslot {
  some t1 : t0.(^next) {
  some t2 : t1.(^next) {
    t0+t1+t2 = sender.arbitrary_init_yahalom_ban + receiver.arbitrary_init_yahalom_ban
    exec_yahalom_ban_init_mesg_0[t0,arbitrary_init_yahalom_ban]
    exec_yahalom_ban_init_mesg_1[t1,arbitrary_init_yahalom_ban]
    exec_yahalom_ban_init_mesg_2[t2,arbitrary_init_yahalom_ban]
  }}}
}
pred exec_yahalom_ban_init{
  all arbitrary_init_yahalom_ban : yahalom_ban_init | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_init_yahalom_ban.yahalom_ban_init_a,arbitrary_init_yahalom_ban.yahalom_ban_init_s]] or generates [aStrand,getLTK[arbitrary_init_yahalom_ban.yahalom_ban_init_a,arbitrary_init_yahalom_ban.yahalom_ban_init_s]]
    }
    (generated_times.Timeslot).(arbitrary_init_yahalom_ban.yahalom_ban_init_Na) = arbitrary_init_yahalom_ban.agent
    arbitrary_init_yahalom_ban.yahalom_ban_init_a != arbitrary_init_yahalom_ban.yahalom_ban_init_b
    arbitrary_init_yahalom_ban.yahalom_ban_init_a != arbitrary_init_yahalom_ban.yahalom_ban_init_s
    arbitrary_init_yahalom_ban.yahalom_ban_init_b != arbitrary_init_yahalom_ban.yahalom_ban_init_s
    {
      { exec_init_trace_len_0[arbitrary_init_yahalom_ban] }
      or
      { exec_init_trace_len_1[arbitrary_init_yahalom_ban] }
      or
      { exec_init_trace_len_2[arbitrary_init_yahalom_ban] }
      or
      { exec_init_trace_len_3[arbitrary_init_yahalom_ban] }
    }
  }
}
sig yahalom_ban_server extends strand {
  yahalom_ban_server_a : one name,
  yahalom_ban_server_b : one name,
  yahalom_ban_server_s : one name,
  yahalom_ban_server_Na : one text,
  yahalom_ban_server_Nb : one text,
  yahalom_ban_server_Kab : one skey
}
pred exec_yahalom_ban_server_mesg_0[t0:Timeslot,arbitrary_server_yahalom_ban:yahalom_ban_server]{
  t0.receiver = arbitrary_server_yahalom_ban
  inds[((t0.data).components)] = 0+1+2
  let name_16  = (((t0.data).components))[0] | {
  let text_17  = (((t0.data).components))[1] | {
  let enc_18  = (((t0.data).components))[2] | {
    ((t0.data).components) = 0->name_16 + 1->text_17 + 2->enc_18
    name_16 = arbitrary_server_yahalom_ban.yahalom_ban_server_b
    text_17 = arbitrary_server_yahalom_ban.yahalom_ban_server_Nb
    learnt_term_by[getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_b,arbitrary_server_yahalom_ban.yahalom_ban_server_s],arbitrary_server_yahalom_ban.agent,t0]
    inds[(enc_18).plaintext.components] = 0+1
    let name_21  = ((enc_18).plaintext.components)[0] | {
    let text_22  = ((enc_18).plaintext.components)[1] | {
      (enc_18).plaintext.components = 0->name_21 + 1->text_22
      name_21 = arbitrary_server_yahalom_ban.yahalom_ban_server_a
      text_22 = arbitrary_server_yahalom_ban.yahalom_ban_server_Na
    }}
    (enc_18).encryptionKey = getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_b,arbitrary_server_yahalom_ban.yahalom_ban_server_s]
  }}}
}
pred exec_yahalom_ban_server_mesg_1[t1:Timeslot,arbitrary_server_yahalom_ban:yahalom_ban_server]{
  t1.sender = arbitrary_server_yahalom_ban
  inds[((t1.data).components)] = 0+1+2
  let text_23  = (((t1.data).components))[0] | {
  let enc_24  = (((t1.data).components))[1] | {
  let enc_25  = (((t1.data).components))[2] | {
    ((t1.data).components) = 0->text_23 + 1->enc_24 + 2->enc_25
    text_23 = arbitrary_server_yahalom_ban.yahalom_ban_server_Nb
    inds[(enc_24).plaintext.components] = 0+1+2
    let name_29  = ((enc_24).plaintext.components)[0] | {
    let skey_30  = ((enc_24).plaintext.components)[1] | {
    let text_31  = ((enc_24).plaintext.components)[2] | {
      (enc_24).plaintext.components = 0->name_29 + 1->skey_30 + 2->text_31
      name_29 = arbitrary_server_yahalom_ban.yahalom_ban_server_b
      skey_30 = arbitrary_server_yahalom_ban.yahalom_ban_server_Kab
      text_31 = arbitrary_server_yahalom_ban.yahalom_ban_server_Na
    }}}
    (enc_24).encryptionKey = getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_a,arbitrary_server_yahalom_ban.yahalom_ban_server_s]
    inds[(enc_25).plaintext.components] = 0+1+2
    let name_35  = ((enc_25).plaintext.components)[0] | {
    let skey_36  = ((enc_25).plaintext.components)[1] | {
    let text_37  = ((enc_25).plaintext.components)[2] | {
      (enc_25).plaintext.components = 0->name_35 + 1->skey_36 + 2->text_37
      name_35 = arbitrary_server_yahalom_ban.yahalom_ban_server_a
      skey_36 = arbitrary_server_yahalom_ban.yahalom_ban_server_Kab
      text_37 = arbitrary_server_yahalom_ban.yahalom_ban_server_Nb
    }}}
    (enc_25).encryptionKey = getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_b,arbitrary_server_yahalom_ban.yahalom_ban_server_s]
  }}}
}
pred exec_server_trace_len_0[arbitrary_server_yahalom_ban:yahalom_ban_server]{
  no (sender.arbitrary_server_yahalom_ban + receiver.arbitrary_server_yahalom_ban)
}
pred exec_server_trace_len_1[arbitrary_server_yahalom_ban:yahalom_ban_server]{
  some t0 : Timeslot {
    t0 = sender.arbitrary_server_yahalom_ban + receiver.arbitrary_server_yahalom_ban
    exec_yahalom_ban_server_mesg_0[t0,arbitrary_server_yahalom_ban]
  }
}
pred exec_server_trace_len_2[arbitrary_server_yahalom_ban:yahalom_ban_server]{
  some t0 : Timeslot {
  some t1 : t0.(^next) {
    t0+t1 = sender.arbitrary_server_yahalom_ban + receiver.arbitrary_server_yahalom_ban
    exec_yahalom_ban_server_mesg_0[t0,arbitrary_server_yahalom_ban]
    exec_yahalom_ban_server_mesg_1[t1,arbitrary_server_yahalom_ban]
  }}
}
pred exec_yahalom_ban_server{
  all arbitrary_server_yahalom_ban : yahalom_ban_server | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_a,arbitrary_server_yahalom_ban.yahalom_ban_server_s]] or generates [aStrand,getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_a,arbitrary_server_yahalom_ban.yahalom_ban_server_s]]
    }
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_b,arbitrary_server_yahalom_ban.yahalom_ban_server_s]] or generates [aStrand,getLTK[arbitrary_server_yahalom_ban.yahalom_ban_server_b,arbitrary_server_yahalom_ban.yahalom_ban_server_s]]
    }
    (generated_times.Timeslot).(arbitrary_server_yahalom_ban.yahalom_ban_server_Kab) = arbitrary_server_yahalom_ban.agent
    arbitrary_server_yahalom_ban.yahalom_ban_server_a != arbitrary_server_yahalom_ban.yahalom_ban_server_b
    arbitrary_server_yahalom_ban.yahalom_ban_server_a != arbitrary_server_yahalom_ban.yahalom_ban_server_s
    arbitrary_server_yahalom_ban.yahalom_ban_server_b != arbitrary_server_yahalom_ban.yahalom_ban_server_s
    {
      { exec_server_trace_len_0[arbitrary_server_yahalom_ban] }
      or
      { exec_server_trace_len_1[arbitrary_server_yahalom_ban] }
      or
      { exec_server_trace_len_2[arbitrary_server_yahalom_ban] }
    }
  }
}
sig yahalom_ban_resp extends strand {
  yahalom_ban_resp_a : one name,
  yahalom_ban_resp_b : one name,
  yahalom_ban_resp_s : one name,
  yahalom_ban_resp_Na : one text,
  yahalom_ban_resp_Nb : one text,
  yahalom_ban_resp_Kab : one skey
}
pred exec_yahalom_ban_resp_mesg_0[t0:Timeslot,arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  t0.receiver = arbitrary_resp_yahalom_ban
  inds[((t0.data).components)] = 0+1
  let name_38  = (((t0.data).components))[0] | {
  let text_39  = (((t0.data).components))[1] | {
    ((t0.data).components) = 0->name_38 + 1->text_39
    name_38 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_a
    text_39 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Na
  }}
}
pred exec_yahalom_ban_resp_mesg_1[t1:Timeslot,arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  t1.sender = arbitrary_resp_yahalom_ban
  inds[((t1.data).components)] = 0+1+2
  let name_40  = (((t1.data).components))[0] | {
  let text_41  = (((t1.data).components))[1] | {
  let enc_42  = (((t1.data).components))[2] | {
    ((t1.data).components) = 0->name_40 + 1->text_41 + 2->enc_42
    name_40 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_b
    text_41 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Nb
    inds[(enc_42).plaintext.components] = 0+1
    let name_45  = ((enc_42).plaintext.components)[0] | {
    let text_46  = ((enc_42).plaintext.components)[1] | {
      (enc_42).plaintext.components = 0->name_45 + 1->text_46
      name_45 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_a
      text_46 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Na
    }}
    (enc_42).encryptionKey = getLTK[arbitrary_resp_yahalom_ban.yahalom_ban_resp_b,arbitrary_resp_yahalom_ban.yahalom_ban_resp_s]
  }}}
}
pred exec_yahalom_ban_resp_mesg_2[t2:Timeslot,arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  t2.receiver = arbitrary_resp_yahalom_ban
  inds[((t2.data).components)] = 0+1
  let enc_47  = (((t2.data).components))[0] | {
  let enc_48  = (((t2.data).components))[1] | {
    ((t2.data).components) = 0->enc_47 + 1->enc_48
    learnt_term_by[getLTK[arbitrary_resp_yahalom_ban.yahalom_ban_resp_b,arbitrary_resp_yahalom_ban.yahalom_ban_resp_s],arbitrary_resp_yahalom_ban.agent,t2]
    inds[(enc_47).plaintext.components] = 0+1+2
    let name_52  = ((enc_47).plaintext.components)[0] | {
    let skey_53  = ((enc_47).plaintext.components)[1] | {
    let text_54  = ((enc_47).plaintext.components)[2] | {
      (enc_47).plaintext.components = 0->name_52 + 1->skey_53 + 2->text_54
      name_52 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_a
      skey_53 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Kab
      text_54 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Nb
    }}}
    (enc_47).encryptionKey = getLTK[arbitrary_resp_yahalom_ban.yahalom_ban_resp_b,arbitrary_resp_yahalom_ban.yahalom_ban_resp_s]
    learnt_term_by[arbitrary_resp_yahalom_ban.yahalom_ban_resp_Kab,arbitrary_resp_yahalom_ban.agent,t2]
    inds[(enc_48).plaintext.components] = 0
    let text_56  = ((enc_48).plaintext.components)[0] | {
      (enc_48).plaintext.components = 0->text_56
      text_56 = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Nb
    }
    (enc_48).encryptionKey = arbitrary_resp_yahalom_ban.yahalom_ban_resp_Kab
  }}
}
pred exec_resp_trace_len_0[arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  no (sender.arbitrary_resp_yahalom_ban + receiver.arbitrary_resp_yahalom_ban)
}
pred exec_resp_trace_len_1[arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  some t0 : Timeslot {
    t0 = sender.arbitrary_resp_yahalom_ban + receiver.arbitrary_resp_yahalom_ban
    exec_yahalom_ban_resp_mesg_0[t0,arbitrary_resp_yahalom_ban]
  }
}
pred exec_resp_trace_len_2[arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  some t0 : Timeslot {
  some t1 : t0.(^next) {
    t0+t1 = sender.arbitrary_resp_yahalom_ban + receiver.arbitrary_resp_yahalom_ban
    exec_yahalom_ban_resp_mesg_0[t0,arbitrary_resp_yahalom_ban]
    exec_yahalom_ban_resp_mesg_1[t1,arbitrary_resp_yahalom_ban]
  }}
}
pred exec_resp_trace_len_3[arbitrary_resp_yahalom_ban:yahalom_ban_resp]{
  some t0 : Timeslot {
  some t1 : t0.(^next) {
  some t2 : t1.(^next) {
    t0+t1+t2 = sender.arbitrary_resp_yahalom_ban + receiver.arbitrary_resp_yahalom_ban
    exec_yahalom_ban_resp_mesg_0[t0,arbitrary_resp_yahalom_ban]
    exec_yahalom_ban_resp_mesg_1[t1,arbitrary_resp_yahalom_ban]
    exec_yahalom_ban_resp_mesg_2[t2,arbitrary_resp_yahalom_ban]
  }}}
}
pred exec_yahalom_ban_resp{
  all arbitrary_resp_yahalom_ban : yahalom_ban_resp | {
    no aStrand : strand | {
      originates[aStrand,getLTK[arbitrary_resp_yahalom_ban.yahalom_ban_resp_b,arbitrary_resp_yahalom_ban.yahalom_ban_resp_s]] or generates [aStrand,getLTK[arbitrary_resp_yahalom_ban.yahalom_ban_resp_b,arbitrary_resp_yahalom_ban.yahalom_ban_resp_s]]
    }
    (generated_times.Timeslot).(arbitrary_resp_yahalom_ban.yahalom_ban_resp_Nb) = arbitrary_resp_yahalom_ban.agent
    arbitrary_resp_yahalom_ban.yahalom_ban_resp_a != arbitrary_resp_yahalom_ban.yahalom_ban_resp_b
    arbitrary_resp_yahalom_ban.yahalom_ban_resp_a != arbitrary_resp_yahalom_ban.yahalom_ban_resp_s
    arbitrary_resp_yahalom_ban.yahalom_ban_resp_b != arbitrary_resp_yahalom_ban.yahalom_ban_resp_s
    {
      { exec_resp_trace_len_0[arbitrary_resp_yahalom_ban] }
      or
      { exec_resp_trace_len_1[arbitrary_resp_yahalom_ban] }
      or
      { exec_resp_trace_len_2[arbitrary_resp_yahalom_ban] }
      or
      { exec_resp_trace_len_3[arbitrary_resp_yahalom_ban] }
    }
  }
}
one sig skeleton_yahalom_ban_0 {
  skeleton_yahalom_ban_0_a : one name,
  skeleton_yahalom_ban_0_b : one name,
  skeleton_yahalom_ban_0_s : one name,
  skeleton_yahalom_ban_0_Na : one text,
  skeleton_yahalom_ban_0_Nb : one text,
  skeleton_yahalom_ban_0_Kab : one skey
}
pred constrain_skeleton_yahalom_ban_0{
  some skeleton_init_0_strand_0 : yahalom_ban_init | {
    skeleton_init_0_strand_0.yahalom_ban_init_a = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_a
    skeleton_init_0_strand_0.yahalom_ban_init_b = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_b
    skeleton_init_0_strand_0.yahalom_ban_init_s = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_s
    skeleton_init_0_strand_0.yahalom_ban_init_Kab = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Kab
    skeleton_init_0_strand_0.yahalom_ban_init_Na = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Na
    skeleton_init_0_strand_0.yahalom_ban_init_Nb = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Nb
  }
  some skeleton_server_0_strand_1 : yahalom_ban_server | {
    skeleton_server_0_strand_1.yahalom_ban_server_a = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_a
    skeleton_server_0_strand_1.yahalom_ban_server_b = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_b
    skeleton_server_0_strand_1.yahalom_ban_server_s = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_s
    skeleton_server_0_strand_1.yahalom_ban_server_Kab = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Kab
    skeleton_server_0_strand_1.yahalom_ban_server_Na = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Na
    skeleton_server_0_strand_1.yahalom_ban_server_Nb = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Nb
  }
  some skeleton_resp_0_strand_2 : yahalom_ban_resp | {
    skeleton_resp_0_strand_2.yahalom_ban_resp_a = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_a
    skeleton_resp_0_strand_2.yahalom_ban_resp_b = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_b
    skeleton_resp_0_strand_2.yahalom_ban_resp_s = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_s
    skeleton_resp_0_strand_2.yahalom_ban_resp_Kab = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Kab
    skeleton_resp_0_strand_2.yahalom_ban_resp_Na = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Na
    skeleton_resp_0_strand_2.yahalom_ban_resp_Nb = skeleton_yahalom_ban_0.skeleton_yahalom_ban_0_Nb
  }
}
one sig skeleton_attack_1 {
  skeleton_attack_1_a : one name,
  skeleton_attack_1_b : one name,
  skeleton_attack_1_s : one name,
  skeleton_attack_1_Na : one text,
  skeleton_attack_1_Nb : one text,
  skeleton_attack_1_Na_ : one text,
  skeleton_attack_1_Ni : one text,
  skeleton_attack_1_Kab : one skey,
  skeleton_attack_1_init_strand1 : one yahalom_ban_init,
  skeleton_attack_1_init_strand2 : one yahalom_ban_init,
  skeleton_attack_1_server_strand1 : one yahalom_ban_server,
  skeleton_attack_1_server_strand2 : one yahalom_ban_server
}
pred constrain_skeleton_attack_1_attack_run{
  some t_0 : Timeslot {
  some t_1 : t_0.(^next) {
  some t_2 : t_1.(^next) {
  some t_3 : t_2.(^next) {
  some t_4 : t_3.(^next) {
  some t_5 : t_4.(^next) {
  some t_6 : t_5.(^next) {
    t_0.sender = skeleton_attack_1.skeleton_attack_1_init_strand1
    inds[(t_0.data.components)] = 0+1
    let name_57  = ((t_0.data.components))[0] | {
    let text_58  = ((t_0.data.components))[1] | {
      (t_0.data.components) = 0->name_57 + 1->text_58
      name_57 = skeleton_attack_1.skeleton_attack_1_a
      text_58 = skeleton_attack_1.skeleton_attack_1_Na
    }}

    t_1.receiver = skeleton_attack_1.skeleton_attack_1_init_strand2
    inds[(t_1.data.components)] = 0+1
    let name_59  = ((t_1.data.components))[0] | {
    let text_60  = ((t_1.data.components))[1] | {
      (t_1.data.components) = 0->name_59 + 1->text_60
      name_59 = skeleton_attack_1.skeleton_attack_1_b
      text_60 = skeleton_attack_1.skeleton_attack_1_Na
    }}

    t_2.sender = skeleton_attack_1.skeleton_attack_1_init_strand2
    inds[(t_2.data.components)] = 0+1+2
    let name_61  = ((t_2.data.components))[0] | {
    let text_62  = ((t_2.data.components))[1] | {
    let enc_63  = ((t_2.data.components))[2] | {
      (t_2.data.components) = 0->name_61 + 1->text_62 + 2->enc_63
      name_61 = skeleton_attack_1.skeleton_attack_1_a
      text_62 = skeleton_attack_1.skeleton_attack_1_Na_
      inds[(enc_63).plaintext.components] = 0+1
      let name_66  = ((enc_63).plaintext.components)[0] | {
      let text_67  = ((enc_63).plaintext.components)[1] | {
        (enc_63).plaintext.components = 0->name_66 + 1->text_67
        name_66 = skeleton_attack_1.skeleton_attack_1_b
        text_67 = skeleton_attack_1.skeleton_attack_1_Na
      }}
      (enc_63).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
    }}}

    t_3.receiver = skeleton_attack_1.skeleton_attack_1_server_strand2
    inds[(t_3.data.components)] = 0+1+2
    let name_68  = ((t_3.data.components))[0] | {
    let text_69  = ((t_3.data.components))[1] | {
    let enc_70  = ((t_3.data.components))[2] | {
      (t_3.data.components) = 0->name_68 + 1->text_69 + 2->enc_70
      name_68 = skeleton_attack_1.skeleton_attack_1_a
      text_69 = skeleton_attack_1.skeleton_attack_1_Na
      inds[(enc_70).plaintext.components] = 0+1
      let name_73  = ((enc_70).plaintext.components)[0] | {
      let text_74  = ((enc_70).plaintext.components)[1] | {
        (enc_70).plaintext.components = 0->name_73 + 1->text_74
        name_73 = skeleton_attack_1.skeleton_attack_1_b
        text_74 = skeleton_attack_1.skeleton_attack_1_Na
      }}
      (enc_70).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
    }}}

    t_4.sender = skeleton_attack_1.skeleton_attack_1_server_strand1
    inds[(t_4.data.components)] = 0+1+2
    let text_75  = ((t_4.data.components))[0] | {
    let enc_76  = ((t_4.data.components))[1] | {
    let enc_77  = ((t_4.data.components))[2] | {
      (t_4.data.components) = 0->text_75 + 1->enc_76 + 2->enc_77
      text_75 = skeleton_attack_1.skeleton_attack_1_Na
      inds[(enc_76).plaintext.components] = 0+1+2
      let name_81  = ((enc_76).plaintext.components)[0] | {
      let skey_82  = ((enc_76).plaintext.components)[1] | {
      let text_83  = ((enc_76).plaintext.components)[2] | {
        (enc_76).plaintext.components = 0->name_81 + 1->skey_82 + 2->text_83
        name_81 = skeleton_attack_1.skeleton_attack_1_a
        skey_82 = skeleton_attack_1.skeleton_attack_1_Kab
        text_83 = skeleton_attack_1.skeleton_attack_1_Na
      }}}
      (enc_76).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
      inds[(enc_77).plaintext.components] = 0+1+2
      let name_87  = ((enc_77).plaintext.components)[0] | {
      let skey_88  = ((enc_77).plaintext.components)[1] | {
      let text_89  = ((enc_77).plaintext.components)[2] | {
        (enc_77).plaintext.components = 0->name_87 + 1->skey_88 + 2->text_89
        name_87 = skeleton_attack_1.skeleton_attack_1_b
        skey_88 = skeleton_attack_1.skeleton_attack_1_Kab
        text_89 = skeleton_attack_1.skeleton_attack_1_Na
      }}}
      (enc_77).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
    }}}

    t_5.receiver = skeleton_attack_1.skeleton_attack_1_init_strand1
    inds[(t_5.data.components)] = 0+1+2
    let text_90  = ((t_5.data.components))[0] | {
    let enc_91  = ((t_5.data.components))[1] | {
    let enc_92  = ((t_5.data.components))[2] | {
      (t_5.data.components) = 0->text_90 + 1->enc_91 + 2->enc_92
      text_90 = skeleton_attack_1.skeleton_attack_1_Ni
      inds[(enc_91).plaintext.components] = 0+1+2
      let name_96  = ((enc_91).plaintext.components)[0] | {
      let skey_97  = ((enc_91).plaintext.components)[1] | {
      let text_98  = ((enc_91).plaintext.components)[2] | {
        (enc_91).plaintext.components = 0->name_96 + 1->skey_97 + 2->text_98
        name_96 = skeleton_attack_1.skeleton_attack_1_b
        skey_97 = skeleton_attack_1.skeleton_attack_1_Kab
        text_98 = skeleton_attack_1.skeleton_attack_1_Na
      }}}
      (enc_91).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_a,skeleton_attack_1.skeleton_attack_1_s]
      inds[(enc_92).plaintext.components] = 0+1+2
      let name_102  = ((enc_92).plaintext.components)[0] | {
      let skey_103  = ((enc_92).plaintext.components)[1] | {
      let text_104  = ((enc_92).plaintext.components)[2] | {
        (enc_92).plaintext.components = 0->name_102 + 1->skey_103 + 2->text_104
        name_102 = skeleton_attack_1.skeleton_attack_1_a
        skey_103 = skeleton_attack_1.skeleton_attack_1_Kab
        text_104 = skeleton_attack_1.skeleton_attack_1_Na
      }}}
      (enc_92).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
    }}}

    t_6.sender = skeleton_attack_1.skeleton_attack_1_init_strand1
    inds[(t_6.data.components)] = 0+1
    let enc_105  = ((t_6.data.components))[0] | {
    let enc_106  = ((t_6.data.components))[1] | {
      (t_6.data.components) = 0->enc_105 + 1->enc_106
      inds[(enc_105).plaintext.components] = 0+1+2
      let name_110  = ((enc_105).plaintext.components)[0] | {
      let skey_111  = ((enc_105).plaintext.components)[1] | {
      let text_112  = ((enc_105).plaintext.components)[2] | {
        (enc_105).plaintext.components = 0->name_110 + 1->skey_111 + 2->text_112
        name_110 = skeleton_attack_1.skeleton_attack_1_a
        skey_111 = skeleton_attack_1.skeleton_attack_1_Kab
        text_112 = skeleton_attack_1.skeleton_attack_1_Na
      }}}
      (enc_105).encryptionKey = getLTK[skeleton_attack_1.skeleton_attack_1_b,skeleton_attack_1.skeleton_attack_1_s]
      inds[(enc_106).plaintext.components] = 0
      let text_114  = ((enc_106).plaintext.components)[0] | {
        (enc_106).plaintext.components = 0->text_114
        text_114 = skeleton_attack_1.skeleton_attack_1_Ni
      }
      (enc_106).encryptionKey = skeleton_attack_1.skeleton_attack_1_Kab
    }}

  }}}}}}}
}
pred constrain_skeleton_attack_1{
  constrain_skeleton_attack_1_attack_run
}
inst honest_run_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4
  text = `text0 + `text1
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6 + `Timeslot7

  components in tuple -> (0+1+2+3) -> (Key + name + text + Ciphertext + tuple + Hashed)
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
  yahalom_ban_init = `yahalom_ban_init0
  yahalom_ban_server = `yahalom_ban_server0
  yahalom_ban_resp = `yahalom_ban_resp0
  AttackerStrand = `AttackerStrand0
  strand = yahalom_ban_init + yahalom_ban_server + yahalom_ban_resp + AttackerStrand
}
inst attack_bounds {
  no akey
  skey = `skey0 + `skey1 + `skey2 + `skey3 + `skey4 + `skey5 + `skey6
  Key = skey
  Attacker = `Attacker0
  name = `name0 + `name1 + `name2 + Attacker
  Ciphertext = `Ciphertext0 + `Ciphertext1 + `Ciphertext2 + `Ciphertext3 + `Ciphertext4 + `Ciphertext5 + `Ciphertext6 + `Ciphertext7
  text = `text0 + `text1 + `text2
  no Hashed
  tuple = `tuple0 + `tuple1 + `tuple2 + `tuple3 + `tuple4 + `tuple5 + `tuple6 + `tuple7 + `tuple8 + `tuple9 + `tuple10 + `tuple11 + `tuple12 + `tuple13 + `tuple14
  mesg = Key + name + Ciphertext + text + tuple

  Timeslot = `Timeslot0 + `Timeslot1 + `Timeslot2 + `Timeslot3 + `Timeslot4 + `Timeslot5 + `Timeslot6

  components in tuple -> (0+1+2+3) -> (Key + name + text + Ciphertext + tuple + Hashed)
  KeyPairs = `KeyPairs0
  Microtick = `Microtick0 + `Microtick1 + `Microtick2
  no PublicKey
  no PrivateKey

  `KeyPairs0.ltks = `name0->`name1->`skey0 + `name0->`name2->`skey1 + `name0->`Attacker0->`skey2 + `name1->`name2->`skey3 + `name1->`Attacker0->`skey4 + `name2->`Attacker0->`skey5
  `KeyPairs0.inv_key_helper = `skey0->`skey0 + `skey1->`skey1 + `skey2->`skey2 + `skey3->`skey3 + `skey4->`skey4 + `skey5->`skey5 + `skey6->`skey6
  next = `Timeslot0->`Timeslot1 + `Timeslot1->`Timeslot2 + `Timeslot2->`Timeslot3 + `Timeslot3->`Timeslot4 + `Timeslot4->`Timeslot5 + `Timeslot5->`Timeslot6
  mt_next = `Microtick0 -> `Microtick1 + `Microtick1 -> `Microtick2

  generated_times in name -> (Key + text) -> Timeslot
  hash_of in Hashed -> text
  yahalom_ban_init = `yahalom_ban_init0 + `yahalom_ban_init1
  yahalom_ban_server = `yahalom_ban_server0 + `yahalom_ban_server1
  yahalom_ban_resp = `yahalom_ban_resp0
  AttackerStrand = `AttackerStrand0
  strand = yahalom_ban_init + yahalom_ban_server + yahalom_ban_resp + AttackerStrand
}
option run_sterling "../../crypto_viz_seq_tuple.js"
option solver Glucose
option verbose 5

yahalom_ban_honest_run: run {
    wellformed

    exec_yahalom_ban_init
    exec_yahalom_ban_server
    exec_yahalom_ban_resp

    // constrain_skeleton_yahalom_ban_0
    constrain_skeleton_attack_1

    no (yahalom_ban_init.agent & yahalom_ban_server.agent)
    no (yahalom_ban_init.agent & yahalom_ban_resp.agent)
    no (yahalom_ban_server.agent & yahalom_ban_resp.agent)

    not Attacker in (yahalom_ban_init + yahalom_ban_server + yahalom_ban_resp).agent

    all x, y: name | yahalom_ban_server.yahalom_ban_server_Kab != x.(KeyPairs.ltks)[y]

} for {
    next is linear
    mt_next is linear
    // honest_run_bounds
    attack_bounds
}