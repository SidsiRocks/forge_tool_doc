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
   //plaintext: set mesg
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
  //old_plainw ould be unique so some or all doesn't
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

sig enc_term_A extends strand{
    enc_term_A_a: one name,
    enc_term_A_b: one name,
    enc_term_A_n1: one text,
    enc_term_A_n2: one text,
    enc_term_A_n3: one text,
    enc_term_A_n4: one text
}

// predicate follows below
pred exec_enc_term_A {
    all arbitrary_enc_term_A : enc_term_A | {
        some t0,t1 : Timeslot | {
            t1 in t0.(^next)
            
            t0 + t1  = sender.arbitrary_enc_term_A + receiver.arbitrary_enc_term_A
            
            t0.sender = arbitrary_enc_term_A
            t1.receiver = arbitrary_enc_term_A
            
            inds[t0.data] = 0
            some enc1 : elems[t0.data] | {
                elems[t0.data] = enc1
                enc1 in Ciphertext
                learnt_term_by[getPRIVK[arbitrary_enc_term_A.enc_term_A_a],arbitrary_enc_term_A.agent,t0] => {
                    getPUBK[arbitrary_enc_term_A.enc_term_A_a] = (enc1).encryptionKey
                    inds[((enc1).plaintext)] = 0 + 1
                    some atom2,atom3 : elems[((enc1).plaintext)] {
                        (((enc1).plaintext))[0] = atom2
                        (((enc1).plaintext))[1] = atom3
                        atom2 = arbitrary_enc_term_A.enc_term_A_n1
                        atom3 = arbitrary_enc_term_A.enc_term_A_n2
                    }
                }
            }
            inds[t1.data] = 0
            some enc4 : elems[t1.data] | {
                elems[t1.data] = enc4
                enc4 in Ciphertext
                learnt_term_by[getPRIVK[arbitrary_enc_term_A.enc_term_A_b],arbitrary_enc_term_A.agent,t1] => {
                    getPUBK[arbitrary_enc_term_A.enc_term_A_b] = (enc4).encryptionKey
                    inds[((enc4).plaintext)] = 0 + 1
                    some atom5,atom6 : elems[((enc4).plaintext)] {
                        (((enc4).plaintext))[0] = atom5
                        (((enc4).plaintext))[1] = atom6
                        atom5 = arbitrary_enc_term_A.enc_term_A_n3
                        atom6 = arbitrary_enc_term_A.enc_term_A_n4
                    }
                }
            }
        }
    }
}
// end of predicate

sig enc_term_B extends strand{
    enc_term_B_a: one name,
    enc_term_B_b: one name,
    enc_term_B_n1: one text,
    enc_term_B_n2: one text,
    enc_term_B_n3: one text,
    enc_term_B_n4: one text
}

// predicate follows below
pred exec_enc_term_B {
    all arbitrary_enc_term_B : enc_term_B | {
        some t0,t1 : Timeslot | {
            t1 in t0.(^next)
            
            t0 + t1  = sender.arbitrary_enc_term_B + receiver.arbitrary_enc_term_B
            
            t0.receiver = arbitrary_enc_term_B
            t1.sender = arbitrary_enc_term_B
            
            inds[t0.data] = 0
            some enc7 : elems[t0.data] | {
                elems[t0.data] = enc7
                enc7 in Ciphertext
                learnt_term_by[getPRIVK[arbitrary_enc_term_B.enc_term_B_a],arbitrary_enc_term_B.agent,t0] => {
                    getPUBK[arbitrary_enc_term_B.enc_term_B_a] = (enc7).encryptionKey
                    inds[((enc7).plaintext)] = 0 + 1
                    some atom8,atom9 : elems[((enc7).plaintext)] {
                        (((enc7).plaintext))[0] = atom8
                        (((enc7).plaintext))[1] = atom9
                        atom8 = arbitrary_enc_term_B.enc_term_B_n1
                        atom9 = arbitrary_enc_term_B.enc_term_B_n2
                    }
                }
            }
            inds[t1.data] = 0
            some enc10 : elems[t1.data] | {
                elems[t1.data] = enc10
                enc10 in Ciphertext
                learnt_term_by[getPRIVK[arbitrary_enc_term_B.enc_term_B_b],arbitrary_enc_term_B.agent,t1] => {
                    getPUBK[arbitrary_enc_term_B.enc_term_B_b] = (enc10).encryptionKey
                    inds[((enc10).plaintext)] = 0 + 1
                    some atom11,atom12 : elems[((enc10).plaintext)] {
                        (((enc10).plaintext))[0] = atom11
                        (((enc10).plaintext))[1] = atom12
                        atom11 = arbitrary_enc_term_B.enc_term_B_n3
                        atom12 = arbitrary_enc_term_B.enc_term_B_n4
                    }
                }
            }
        }
    }
}
// end of predicate

one sig skeleton_enc_term_0 {
    skeleton_enc_term_0_a: one name,
    skeleton_enc_term_0_b: one name,
    skeleton_enc_term_0_n1: one text,
    skeleton_enc_term_0_n2: one text,
    skeleton_enc_term_0_n3: one text,
    skeleton_enc_term_0_n4: one text
}
pred constrain_skeleton_enc_term_0 {
    some skeleton_enc_term_0_strand1 : enc_term_A | {
        skeleton_enc_term_0.skeleton_enc_term_0_a = skeleton_enc_term_0_strand1.enc_term_A_a
        skeleton_enc_term_0.skeleton_enc_term_0_b = skeleton_enc_term_0_strand1.enc_term_A_b
        skeleton_enc_term_0.skeleton_enc_term_0_n1 = skeleton_enc_term_0_strand1.enc_term_A_n1
        skeleton_enc_term_0.skeleton_enc_term_0_n2 = skeleton_enc_term_0_strand1.enc_term_A_n2
        skeleton_enc_term_0.skeleton_enc_term_0_n3 = skeleton_enc_term_0_strand1.enc_term_A_n3
        skeleton_enc_term_0.skeleton_enc_term_0_n4 = skeleton_enc_term_0_strand1.enc_term_A_n4
    }

    not ( getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_a] in baseKnown[Attacker]  )
    no aStrand : strand | {
        originates[aStrand,getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_a]]
        or
        generates[aStrand,getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_a]]
    }
    
    not ( getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_b] in baseKnown[Attacker]  )
    no aStrand : strand | {
        originates[aStrand,getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_b]]
        or
        generates[aStrand,getPRIVK[skeleton_enc_term_0.skeleton_enc_term_0_b]]
    }
    
}
option run_sterling "../../crypto_viz_seq.js"

enc_term_exmpl : run {
    wellformed
    
    exec_enc_term_A
    exec_enc_term_B
    
    constrain_skeleton_enc_term_0
}for 
    exactly 4 Timeslot,30 mesg,
    exactly 1 KeyPairs,exactly 6 Key,exactly 6 akey,exactly 0 skey,
    exactly 3 PrivateKey,exactly 3 PublicKey,
    exactly 3 name,exactly 10 text,exactly 8 Ciphertext,
    exactly 1 enc_term_A,exactly 1 enc_term_B,
    4 Int
for {next is linear}
