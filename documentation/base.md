# Intro 
Documentation goes over the code line by line, explaining sections of the code

## Message Subtypes
The mesg type represents the messages transfered between principals and all the components of the message (keys/nonces etc.)
Line number 27 in base.frg
```frg
abstract sig mesg {} 

abstract sig Key extends mesg {}
abstract sig akey extends Key {} -- asymmetric key
sig skey extends Key {}          -- symmetric key
sig PrivateKey extends akey {}
sig PublicKey extends akey {}
```
The signature names here directly refer to their usage.

```frg
-- Helper to hold relations that match key pairs
one sig KeyPairs {
  pairs: set PrivateKey -> PublicKey, -- asymmetric key pairing
  owners: set PrivateKey -> name,     -- who owns a key
  ltks: set name -> name -> skey      -- symmetric long-term keys
}

/** Get a long-term key associated with a pair of agents */
fun getLTK[name_a: name, name_b: name]: lone skey {
  (KeyPairs.ltks)[name_a][name_b]
}

/** Get the inverse key for a given key (if any) */
fun getInv[k: Key]: one Key {
  (k in PublicKey => ((KeyPairs.pairs).k) else (k.(KeyPairs.pairs)))
  +
  (k in skey => k else none)
}
```
The signature KeyPairs here (marked as one denoting only one element in it like singelton class). The signature merely holds some relations which hold properties of the keys.
- pairs: PrivateKey,PublicKey mappings later constraints ensure bijective function(check this statement)
- owners: PrivateKey to agent names mappings
- ltks: Stores the long term keys for pairs of agents, relation holds pairs of names and symmetric key.

Note: Here in various parts of the code you will see expressions like set PrivateKey -> PublicKey which is bracketed like so set (PrivateKey -> PublicKey) Here (PrivateKey -> PublicKey) denotes a cartesian product of those two sets, denoting the type of element here hence set (A -> B) is a relation on A,B.

Functions explanation:
- getLTK: Helper function returning LTK for the two agents passed in 
- getInv: returns the inversekey for the key passed in

### Timeslots
```frg
-- Time indexes (t=0, t=1, ...). These are also used as micro-tick indexes, so the 
-- bound on `Timeslot` will also affect how many microticks are available between ticks.
sig Timeslot {
  -- structure of time (must be rendered linear in every run via `next is linear`)
  next: lone Timeslot,
  
  -- <=1 actual "message tuple" sent/received per timeslot
  sender: one strand,
  receiver: one strand,  
  data: set mesg,

  -- relation is: Tick x Microtick x learned-mesg
  -- Only one agent per tick is receiving, so always know which agent's workspace it is
  workspace: set Timeslot -> mesg
}
```
The Timeslot signature represnets a send/receive between two agents and also serves an additional use to show processing in workspace discussed later:
- next: The ordering on timeslot represented using a linked list like structure with each timeslot pointing to the next Timeslot
- sender/receiver: The sender/reciever for this Timeslot 
- data: The data(message) in this Timeslot, represented as a set of messages. This is because the tool represents a tuple of messages as a set of messages.
- workspace: Consists of the set of timeslot where the message is furthur broken down.
As explained in tool's github repo to prevent cylic justification while trying to find what terms can be derived nested encrypted terms are decrypted one level at a time.
This sequential decryption represented in the microtick relation.

### More message subtypes
```frg
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
   plaintext: set mesg
}

-- Non-name base value (e.g., nonces)
sig text extends mesg {}

```
The name signature refers to the agent names, it also consists of two relations specific to the agents, learned_times and generated_times.
- learned_times: The agents only send messages they can derive(learn), the first timeslot at which this term is learn is stored in the learned_times relation.
- generated_times: This relation keeps track of when nonces are generated(denoted by text here)

The strand signature just consists of the agent performing the protocol role.
The signature AttackerStrand and Attacker denote the strand used by attacket and the Attacker's name respectively.

The text signature refers to nonce's generated for use in the code.
```frg
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
    a
}
```
The baseKnown function returns for an agent the set of terms the agent would know before receiving any messages.(+ operator here is union)
- PublicKey: The set of all public keys (should be known to all agents)
- (KeyPairs.owners).a: '.' In forge denotes join operator, explained in forge documentation. KeyPairs.owners returns elements of owners relation .a returns all keys with agent a as their owner. 
- {d : skey | some a2 : name - a | d in getLTK[a, a2] + getLTK[a2, a] }:
All keys d such that the key is owned by a, and some agent a2 != a.
- a: The agent's name itself.

The wellformed predicate is explained section by section. The wellformed predicate consists of the constraints the agents most satisfy and some of the relations defined before.
```frg
  -- You cannot send a message with no data
  all m: Timeslot | some m.data

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
    }}}
  }
```
The first predicate (all m: TimeSlot .. ) ensures every Timeslot has some data in it.
The second predicate of this form ensures both sender and receiver are not the same.
The third predicate of the form (all d: mesg | all t,microt: T...) where the message d belongs to the workspace of TimeSlot t, and the microtick 'microt' if and only if (this predicate defines how ciphertext broken inductively in workspace).
The first part of the or clause {d in t.data and no microt.~next} is to ensure the first microtick consists of the message receivied in the tick itself. 
The other part of the or clause is for decrypting the nested encrypted term.
{some superterm : Ciphertext | {      
d in superterm.plaintext and  
These lines refer to d being the plain text part of a cipher.
superterm in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a] 
The above lines ensures the encrypted term was known at some time before the current microtick or was derived in the workspace of some microtick.
getInv[superterm.encryptionKey] in (a.learned_times).(Timeslot - t.*next) + workspace[t][Timeslot - microt.*next] + baseKnown[a]
The last line here ensures the key for the cipher text was also known or learnt at some point.
Now we have the code for the predicates on the learned times relation itself.
```frg
  all d: mesg | all t: Timeslot | all a: name | d->t in a.learned_times iff {
```
This line just serves to quantify what terms we are talking about.
```frg
{d not in (a.learned_times).(Timeslot - t.*next)} and 
```
Here we say that d doesn't belong to learned times at time t since it was learnt at a previous time.'
Next we have multiple or predicates for membership 
```frg
    { t.receiver.agent = a
      d in workspace[t][Timeslot] -- derived in any micro-tick in this (reception) timeslot
    }
```
This is for adding the term to learned_times relation if it is in the workspace for that Timeslot (obtained by removing nested decryption)
```frg
    {d in Ciphertext and 
	   d.encryptionKey in (a.learned_times).(Timeslot - t.^next) and        
	   d.plaintext in (a.learned_times).(Timeslot - t.^next)
     {a not in t.receiver.agent} -- non-reception
    }
```
This part refers to constructing encrypted terms and requires that the both the plain text and the key must be known by current TimeSlot (current also inculded ^ denotes transitive closure not reflexive transitive.)
```frg
    {d in baseKnown[a]}
```
Belongs to learned_times if part of base knowledge
```frg
    {d in (a.generated_times).t} 
```
Corresponds to a value which was just generated.
```frg
  all a: name | all d: text | lone t: Timeslot | d in (a.generated_times).t
```
Ensures that each text(nonce) could only have been generated once.(To prevent duplicate nonces)
```frg
  all m: Timeslot | m.data in (((m.sender).agent).learned_times).(Timeslot - m.^next) 
```
Ensures that all messages sent by sender in any timeslot only consists of terms which they can derive before that timeslot.(Doubt: have to ensure only learns from sent messages not received messages to ensure no cyclic justification, since used ^next instead of *next).
```frg
all m: Timeslot | m.sender = AttackerStrand or m.receiver = AttackerStrand 
```
ensures all sends/receives go through Attacker (have assumed that Attacker is the network itself all messages go thorough it).
```frg
  all d: mesg | d not in d.^(plaintext)
```
Above ensures that an encrypted term d doesn't contain itself in its plain text.
```frg
  all c: Ciphertext | some c.plaintext
```
Ensures no empty encrypted terms.
```frg
  (KeyPairs.pairs).PublicKey = PrivateKey -- total
  PrivateKey.(KeyPairs.pairs) = PublicKey -- total
```
Ensures that all the keys corresponding to PublicKeys in KeyPairs consist of complete private key set, and vice versa.
```frg
  all privKey: PrivateKey | {one pubKey: PublicKey | privKey->pubKey in KeyPairs.pairs} -- uniqueness
  all priv1: PrivateKey | all priv2: PrivateKey - priv1 | all pub: PublicKey | priv1->pub in KeyPairs.pairs implies priv2->pub not in KeyPairs.pairs
```
The first predicate ensures every PrivateKey has exactly one corresponding PublicKey.
The second predicate ensures no two private keys correspond to same PublicKey.
```frg
  -- at most one long-term key per (ordered) pair of names
  all a:name, b:name | lone getLTK[a,b]
  
  -- assume long-term keys are used for only one agent pair (or unused)
  all k: skey | lone (KeyPairs.ltks).k

  -- The Attacker agent is represented by the attacker strand
  AttackerStrand.agent = Attacker
```
First predicate ensures every pair of agents has different long term keys.
Second predicate ensures the no two distinct pairs of agents share the same long term key. Each LTK corresponds to unique agent pair.
Third predicate ensures that AttackerStrand corresponds to attacker.
```frg
  -- If one agent has a key, it is different from any other agent's key
  all a1, a2: name | { 
    (some KeyPairs.owners.a1 and a1 != a2) implies 
      (KeyPairs.owners.a1 != KeyPairs.owners.a2)
  }
```
Above predicate ensurses no two agents have the same set of private/public keys.
```frg
  -- private key ownership is unique 
  all p: PrivateKey | one p.(KeyPairs.owners) 
```
Ensures each agent has exactly one private key.
```frg
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
```
The first line ensures that terms in the generated times relation only consist of text and keys not any complex terms .
the later parts ensures that if term d is in generated times at some point t then it wasn't learned at some previous time t2 and is not in baseKnown for that agent.
```frg
/** Definition of subterms for some set of terms */
fun subterm[supers: set mesg]: set mesg {
  -- VITAL: if you add a new subterm relation, needs to be added here, too!
  supers +
  supers.^(plaintext) -- union on new subterm relations inside parens
}
```
Defining subterm for any message, currently only relevant for ciphertext.
```frg
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
```
(Doc: Try finding out why it is vital that it is about strands and not names)
The originates predicates ensures that any particular mesg only originated froma particular strand.
The first d in line is to find a mesg/subterm of mesg where this particular strand first sent the term. An additional restriction is that for all other messages m2 such that m2 in m.^(~next) ~next is transpose of next so before ^ is transitive closure so any time before, implies d is not located in the subterms there.(Doubt: in subterm relation currently stated at ^(plaintext) which works when nesting only happens with encryption (matters if we have nested pairs and such later).)
```frg
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
```
Some helper functions for finding respectively if 
- an agent generated this term 
- the attacket has learnt this term 
- the agent for this strand eventually learns this value 
NOTE: There seems to be a mistake with the code for attacker_learns and strand_agent_learns the corrected code used in two_nonce.frg is as below
```frg
pred corrected_attacker_learns[d:mesg]{
    d in Attacker.learned_times.Timeslot
}
```
Here neither s/d is a relation so join operator doesn't make sense here. (Check if this justification is correct later)



