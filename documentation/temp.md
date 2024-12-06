<!DOCTYPE html>
<html>
<head>
	<meta http-equiv="content-type" content="text/html; charset=utf-8"/>
	<title></title>
	<meta name="generator" content="LibreOffice 24.2.7.2 (Linux)"/>
	<meta name="created" content="2024-12-05T16:08:24.085712694"/>
	<meta name="changed" content="2024-12-05T16:09:48.528710213"/>
	<style type="text/css">
		@page { size: 21cm 29.7cm; margin: 2cm }
		p { line-height: 115%; margin-bottom: 0cm; margin-top: 0cm;background: #1f1f1f}
	</style>
</head>
<body lang="en-IN" link="#000080" vlink="#800000" dir="ltr"><p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#c586c0">#lang</font>
<font color="#c586c0">forge</font></span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/*</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Base
domain model of strand space style crypto (2021)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Abby
Siegel</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Mia
Santomauro </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Tim
Nelson </span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">We
say &quot;strand space style&quot; above because this model
approximates the strand-space </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">formalism.
See the &quot;Prototyping Formal Methods Tools&quot; paper for more
information.</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Design
notes: </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">-
We opted to build this in Relational Forge, not Temporal Forge; at
the time, </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">Temporal
Forge was very new and still being tested. </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">-
Forge has a somewhat more restricted syntax than Alloy. E.g., Forge
doesn't </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">have
`facts` (which are always true); instead, predicates must be
asserted. </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">-
CPSA has some idiosyncratic terminology, which we echo here somewhat.
For </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">example,
the &quot;strand&quot; is not the same as the &quot;agent&quot; for
that strand; it </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">may
be best to think of the agent as a knowledge database and the strand </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">as
the protocol role execution.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">-
This model embraces Dolev-Yao in a very concrete way: there is an
explicit </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">attacker,
who is also the medium of communication between participants.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">*/</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
NOTE WELL: `mesg` is what CPSA calls terms; we echo that here, do not
confuse </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
`mesg` with just messages being sent or received.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">abstract</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">mesg</font> {}
</span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">abstract</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">Key</font>
<font color="#569cd6">extends</font> <font color="#4ec9b0">mesg</font>
{}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">abstract</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">akey</font>
<font color="#569cd6">extends</font> <font color="#4ec9b0">Key</font>
{} <font color="#6a9955">-- asymmetric key</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">skey</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">Key</font> {} <font color="#6a9955">--
symmetric key</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">PrivateKey</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">akey</font> {}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">PublicKey</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">akey</font> {}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Helper to hold relations that match key pairs</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">one</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">KeyPairs</font>
{</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">pairs<font color="#569cd6">:</font>
<font color="#569cd6">set</font> PrivateKey <font color="#c586c0">-&gt;</font>
PublicKey<font color="#569cd6">,</font> <font color="#6a9955">--
asymmetric key pairing</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">owners<font color="#569cd6">:</font>
<font color="#569cd6">set</font> PrivateKey <font color="#c586c0">-&gt;</font>
name<font color="#569cd6">,</font> <font color="#6a9955">-- who owns
a key</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">ltks<font color="#569cd6">:</font>
<font color="#569cd6">set</font> name <font color="#c586c0">-&gt;</font>
name <font color="#c586c0">-&gt;</font> skey <font color="#6a9955">--
symmetric long-term keys</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
Get a long-term key associated with a pair of agents */</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">fun</font>
<font color="#dcdcaa">getLTK</font><font color="#ce9178">[</font>name_a<font color="#569cd6">:</font>
name<font color="#569cd6">,</font> name_b<font color="#569cd6">:</font>
name<font color="#ce9178">]</font><font color="#569cd6">:</font> <font color="#569cd6">lone</font>
skey {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(KeyPairs<font color="#c586c0">.</font>ltks)<font color="#ce9178">[</font>name_a<font color="#ce9178">][</font>name_b<font color="#ce9178">]</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
Get the inverse key for a given key (if any) */</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">fun</font>
<font color="#dcdcaa">getInv</font><font color="#ce9178">[</font>k<font color="#569cd6">:</font>
Key<font color="#ce9178">]</font><font color="#569cd6">:</font> <font color="#569cd6">one</font>
Key {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(k
<font color="#c586c0">in</font> PublicKey <font color="#c586c0">=&gt;</font>
((KeyPairs<font color="#c586c0">.</font>pairs)<font color="#c586c0">.</font>k)
<font color="#c586c0">else</font> (k<font color="#c586c0">.</font>(KeyPairs<font color="#c586c0">.</font>pairs)))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">+</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(k
<font color="#c586c0">in</font> skey <font color="#c586c0">=&gt;</font>
k <font color="#c586c0">else</font> <font color="#569cd6">none</font>)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0.5cm"><br/>
<br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Time indexes (t=0, t=1, ...). These are also used as micro-tick
indexes, so the </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
bound on `Timeslot` will also affect how many microticks are
available between ticks.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">Timeslot</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
structure of time (must be rendered linear in every run via `next is
linear`)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">next<font color="#569cd6">:</font>
<font color="#569cd6">lone</font> Timeslot<font color="#569cd6">,</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
&lt;=1 actual &quot;message tuple&quot; sent/received per timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">sender<font color="#569cd6">:</font>
<font color="#569cd6">one</font> strand<font color="#569cd6">,</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">receiver<font color="#569cd6">:</font>
<font color="#569cd6">one</font> strand<font color="#569cd6">,</font>
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">data<font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg<font color="#569cd6">,</font></span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
relation is: Tick x Microtick x learned-mesg</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Only one agent per tick is receiving, so always know which agent's
workspace it is</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">workspace<font color="#569cd6">:</font>
<font color="#569cd6">set</font> Timeslot <font color="#c586c0">-&gt;</font>
mesg</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
As names process received messages, they learn pieces of data</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
(they may also generate new values on their own)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">name</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">mesg</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">learned_times<font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg <font color="#c586c0">-&gt;</font>
Timeslot<font color="#569cd6">,</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">generated_times<font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg <font color="#c586c0">-&gt;</font>
Timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
every strand will be either a protocol role or the attacker/medium</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">abstract</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">strand</font>
{</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
the name associated with this strand</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">agent<font color="#569cd6">:</font>
<font color="#569cd6">one</font> name</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">one</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">AttackerStrand</font>
<font color="#569cd6">extends</font> <font color="#4ec9b0">strand</font>
{}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">one</font>
<font color="#569cd6">sig</font> <font color="#4ec9b0">Attacker</font>
<font color="#569cd6">extends</font> <font color="#4ec9b0">name</font>
{}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">Ciphertext</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">mesg</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
encrypted with this key</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">encryptionKey<font color="#569cd6">:</font>
<font color="#569cd6">one</font> Key<font color="#569cd6">,</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
result in concating plaintexts</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">plaintext<font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Non-name base value (e.g., nonces)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">sig</font>
<font color="#4ec9b0">text</font> <font color="#569cd6">extends</font>
<font color="#4ec9b0">mesg</font> {}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
The starting knowledge base for all agents */</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">fun</font>
<font color="#dcdcaa">baseKnown</font><font color="#ce9178">[</font>a<font color="#569cd6">:</font>
name<font color="#ce9178">]</font><font color="#569cd6">:</font> <font color="#569cd6">set</font>
mesg {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
name knows all public keys</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">PublicKey</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">+</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
name knows the private keys it owns</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(KeyPairs<font color="#c586c0">.</font>owners)<font color="#c586c0">.</font>a</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">+</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
name knows long-term keys they are party to </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#569cd6">:</font> skey <font color="#569cd6">|</font>
<font color="#569cd6">some</font> a2 <font color="#569cd6">:</font>
name <font color="#c586c0">-</font> a <font color="#569cd6">|</font>
d <font color="#c586c0">in</font> <font color="#dcdcaa">getLTK</font><font color="#ce9178">[</font>a<font color="#569cd6">,</font>
a2<font color="#ce9178">]</font> <font color="#c586c0">+</font>
<font color="#dcdcaa">getLTK</font><font color="#ce9178">[</font>a2<font color="#569cd6">,</font>
a<font color="#ce9178">]</font> }</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">+</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
names know their own names</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">a</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
This (large) predicate contains the vast majority of domain axioms */</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">pred</font>
<font color="#dcdcaa">wellformed</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Design choice: only one message event per timeslot;</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
assume we have a shared notion of time</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
You cannot send a message with no data</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
m<font color="#569cd6">:</font> Timeslot <font color="#569cd6">|</font>
<font color="#569cd6">some</font> m<font color="#c586c0">.</font>data</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
someone cannot send a message to themselves</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
m<font color="#569cd6">:</font> Timeslot <font color="#569cd6">|</font>
m<font color="#c586c0">.</font>sender <font color="#c586c0">not</font>
<font color="#c586c0">in</font> m<font color="#c586c0">.</font>receiver</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
workspace: workaround to avoid cyclic justification within just
deconstructions</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
AGENT -&gt; TICK -&gt; MICRO-TICK LEARNED_SUBTERM</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
d<font color="#569cd6">:</font> mesg <font color="#569cd6">|</font>
<font color="#569cd6">all</font> t<font color="#569cd6">,</font>
microt<font color="#569cd6">:</font> Timeslot <font color="#569cd6">|</font>
<font color="#569cd6">let</font> a <font color="#d4d4d4">=</font>
t<font color="#c586c0">.</font>receiver<font color="#c586c0">.</font>agent
<font color="#569cd6">|</font> d <font color="#c586c0">in</font>
(<font color="#dcdcaa">workspace</font><font color="#ce9178">[</font>t<font color="#ce9178">]</font>)<font color="#ce9178">[</font>microt<font color="#ce9178">]</font>
<font color="#c586c0">iff</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Base case:</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
received the data in the clear just now </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">in</font> t<font color="#c586c0">.</font>data
<font color="#c586c0">and</font> <font color="#569cd6">no</font>
microt<font color="#c586c0">.~</font>next}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">or</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Inductive case:</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
breaking down a ciphertext we learned *previously*, or that we've
produced from </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
something larger this timeslot via a key we learned *previously*, or
that we've </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
produced from something larger in this timeslot Note use of
&quot;previously&quot; by </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
subtracting the *reflexive* transitive closure is crucial in
preventing cyclic justification.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Note: the baseKnown function includes an agent's private key,
otherwise &quot;prior</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
knowledge&quot; is empty (even of their private key!)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--d
not in ((a.workspace)[t])[Timeslot - microt.^next] and -- first time
appearing</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{<font color="#569cd6">some</font>
superterm <font color="#569cd6">:</font> Ciphertext <font color="#569cd6">|</font>
{ </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d
<font color="#c586c0">in</font> superterm<font color="#c586c0">.</font>plaintext
<font color="#c586c0">and</font> </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">superterm
<font color="#c586c0">in</font> (a<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> t<font color="#c586c0">.*</font>next)
<font color="#c586c0">+</font> <font color="#dcdcaa">workspace</font><font color="#ce9178">[</font>t<font color="#ce9178">][</font>Timeslot
<font color="#c586c0">-</font> microt<font color="#c586c0">.*</font>next<font color="#ce9178">]</font>
<font color="#c586c0">+</font> <font color="#dcdcaa">baseKnown</font><font color="#ce9178">[</font>a<font color="#ce9178">]</font>
<font color="#c586c0">and</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#dcdcaa">getInv</font><font color="#ce9178">[</font>superterm<font color="#c586c0">.</font>encryptionKey<font color="#ce9178">]</font>
<font color="#c586c0">in</font> (a<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> t<font color="#c586c0">.*</font>next)
<font color="#c586c0">+</font> <font color="#dcdcaa">workspace</font><font color="#ce9178">[</font>t<font color="#ce9178">][</font>Timeslot
<font color="#c586c0">-</font> microt<font color="#c586c0">.*</font>next<font color="#ce9178">]</font>
<font color="#c586c0">+</font> <font color="#dcdcaa">baseKnown</font><font color="#ce9178">[</font>a<font color="#ce9178">]</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}}}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
names only learn information that associated strands are explicitly
sent </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
(start big disjunction for learned_times)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
d<font color="#569cd6">:</font> mesg <font color="#569cd6">|</font>
<font color="#569cd6">all</font> t<font color="#569cd6">:</font>
Timeslot <font color="#569cd6">|</font> <font color="#569cd6">all</font>
a<font color="#569cd6">:</font> name <font color="#569cd6">|</font>
d<font color="#c586c0">-&gt;</font>t <font color="#c586c0">in</font>
a<font color="#c586c0">.</font>learned_times <font color="#c586c0">iff</font>
{</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
they have not already learned this value</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
(a<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> t<font color="#c586c0">.*</font>next)}
<font color="#c586c0">and</font> </span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
This base-case is handled in the workspace now, hence commented out:</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
They received a message directly containing d (may be a ciphertext)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{
<font color="#6a9955">--{some m: Message | {d in m.data and t =
m.sendTime and m.receiver.agent = a}}</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--or</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
deconstruct encrypted term </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
constrain time to reception to avoid cyclic justification of
knowledge. e.g.,</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
&quot;I know enc(other-agent's-private-key, pubk(me)) [from below via
construct]&quot;</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
&quot;I know other-agent's-private-key [from above via deconstruct]&quot;&quot;</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
instead: separate the two temporally: deconstruct on recv, construct
on non-reception</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
in that case, the cycle can't exist in the same timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
might think to write an accessibleSubterms function as below, except:</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
consider: (k1, enc(k2, enc(n1, invk(k2)), invk(k1)))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
or, worse: (k1, enc(x, invk(k3)), enc(k2, enc(k3, invk(k2)),
invk(k1)))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{
t<font color="#c586c0">.</font>receiver<font color="#c586c0">.</font>agent
<font color="#d4d4d4">=</font> a</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d
<font color="#c586c0">in</font> <font color="#dcdcaa">workspace</font><font color="#ce9178">[</font>t<font color="#ce9178">][</font>Timeslot<font color="#ce9178">]</font>
<font color="#6a9955">-- derived in any micro-tick in this
(reception) timeslot</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#c586c0">or</font>
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
construct encrypted terms (only allow at NON-reception time; see
above)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
NOTE WELL: if ever allow an agent to send/receive at same time, need
rewrite </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">in</font> Ciphertext <font color="#c586c0">and</font>
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d<font color="#c586c0">.</font>encryptionKey
<font color="#c586c0">in</font> (a<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> t<font color="#c586c0">.^</font>next)
<font color="#c586c0">and</font> </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d<font color="#c586c0">.</font>plaintext
<font color="#c586c0">in</font> (a<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> t<font color="#c586c0">.^</font>next)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{a
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
t<font color="#c586c0">.</font>receiver<font color="#c586c0">.</font>agent}
<font color="#6a9955">-- non-reception</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#c586c0">or</font>
</span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">in</font> <font color="#dcdcaa">baseKnown</font><font color="#ce9178">[</font>a<font color="#ce9178">]</font>}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#c586c0"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">or</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
This was a value generated by the name in this timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">in</font> (a<font color="#c586c0">.</font>generated_times)<font color="#c586c0">.</font>t}
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}}
<font color="#6a9955">-- (end big disjunction for learned_times)</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
If you generate something, you do it once only</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
a<font color="#569cd6">:</font> name <font color="#569cd6">|</font>
<font color="#569cd6">all</font> d<font color="#569cd6">:</font> text
<font color="#569cd6">|</font> <font color="#569cd6">lone</font> t<font color="#569cd6">:</font>
Timeslot <font color="#569cd6">|</font> d <font color="#c586c0">in</font>
(a<font color="#c586c0">.</font>generated_times)<font color="#c586c0">.</font>t</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Messages comprise only values known by the sender</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
m<font color="#569cd6">:</font> Timeslot <font color="#569cd6">|</font>
m<font color="#c586c0">.</font>data <font color="#c586c0">in</font>
(((m<font color="#c586c0">.</font>sender)<font color="#c586c0">.</font>agent)<font color="#c586c0">.</font>learned_times)<font color="#c586c0">.</font>(Timeslot
<font color="#c586c0">-</font> m<font color="#c586c0">.^</font>next) </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Always send or receive to the adversary</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
m<font color="#569cd6">:</font> Timeslot <font color="#569cd6">|</font>
m<font color="#c586c0">.</font>sender <font color="#d4d4d4">=</font>
AttackerStrand <font color="#c586c0">or</font> m<font color="#c586c0">.</font>receiver
<font color="#d4d4d4">=</font> AttackerStrand </span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
plaintext relation is acyclic </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
NOTE WELL: if ever add another type of mesg that contains data, add
with + inside ^.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
d<font color="#569cd6">:</font> mesg <font color="#569cd6">|</font> d
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
d<font color="#c586c0">.^</font>(plaintext)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Disallow empty ciphertexts</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
c<font color="#569cd6">:</font> Ciphertext <font color="#569cd6">|</font>
<font color="#569cd6">some</font> c<font color="#c586c0">.</font>plaintext</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(KeyPairs<font color="#c586c0">.</font>pairs)<font color="#c586c0">.</font>PublicKey
<font color="#d4d4d4">=</font> PrivateKey <font color="#6a9955">--
total</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">PrivateKey<font color="#c586c0">.</font>(KeyPairs<font color="#c586c0">.</font>pairs)
<font color="#d4d4d4">=</font> PublicKey <font color="#6a9955">--
total</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
privKey<font color="#569cd6">:</font> PrivateKey <font color="#569cd6">|</font>
{<font color="#569cd6">one</font> pubKey<font color="#569cd6">:</font>
PublicKey <font color="#569cd6">|</font> privKey<font color="#c586c0">-&gt;</font>pubKey
<font color="#c586c0">in</font> KeyPairs<font color="#c586c0">.</font>pairs}
<font color="#6a9955">-- uniqueness</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
priv1<font color="#569cd6">:</font> PrivateKey <font color="#569cd6">|</font>
<font color="#569cd6">all</font> priv2<font color="#569cd6">:</font>
PrivateKey <font color="#c586c0">-</font> priv1 <font color="#569cd6">|</font>
<font color="#569cd6">all</font> pub<font color="#569cd6">:</font>
PublicKey <font color="#569cd6">|</font> priv1<font color="#c586c0">-&gt;</font>pub
<font color="#c586c0">in</font> KeyPairs<font color="#c586c0">.</font>pairs
<font color="#c586c0">implies</font> priv2<font color="#c586c0">-&gt;</font>pub
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
KeyPairs<font color="#c586c0">.</font>pairs</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
at most one long-term key per (ordered) pair of names</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
a<font color="#569cd6">:</font>name<font color="#569cd6">,</font>
b<font color="#569cd6">:</font>name <font color="#569cd6">|</font>
<font color="#569cd6">lone</font> <font color="#dcdcaa">getLTK</font><font color="#ce9178">[</font>a<font color="#569cd6">,</font>b<font color="#ce9178">]</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
assume long-term keys are used for only one agent pair (or unused)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
k<font color="#569cd6">:</font> skey <font color="#569cd6">|</font>
<font color="#569cd6">lone</font> (KeyPairs<font color="#c586c0">.</font>ltks)<font color="#c586c0">.</font>k</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
The Attacker agent is represented by the attacker strand</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">AttackerStrand<font color="#c586c0">.</font>agent
<font color="#d4d4d4">=</font> Attacker</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
If one agent has a key, it is different from any other agent's key</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
a1<font color="#569cd6">,</font> a2<font color="#569cd6">:</font>
name <font color="#569cd6">|</font> { </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(<font color="#569cd6">some</font>
KeyPairs<font color="#c586c0">.</font>owners<font color="#c586c0">.</font>a1
<font color="#c586c0">and</font> a1 <font color="#d4d4d4">!=</font>
a2) <font color="#c586c0">implies</font> </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(KeyPairs<font color="#c586c0">.</font>owners<font color="#c586c0">.</font>a1
<font color="#d4d4d4">!=</font> KeyPairs<font color="#c586c0">.</font>owners<font color="#c586c0">.</font>a2)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
private key ownership is unique </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
p<font color="#569cd6">:</font> PrivateKey <font color="#569cd6">|</font>
<font color="#569cd6">one</font> p<font color="#c586c0">.</font>(KeyPairs<font color="#c586c0">.</font>owners)
</span></font></font></font>
</p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
generation only of text and keys, not complex terms</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
furthermore, only generate if unknown</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
n<font color="#569cd6">:</font> name <font color="#569cd6">|</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">n<font color="#c586c0">.</font>generated_times<font color="#c586c0">.</font>Timeslot
<font color="#c586c0">in</font> text<font color="#c586c0">+</font>Key</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
t<font color="#569cd6">:</font> Timeslot<font color="#569cd6">,</font>
d<font color="#569cd6">:</font> mesg <font color="#569cd6">|</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d
<font color="#c586c0">in</font> n<font color="#c586c0">.</font>generated_times<font color="#c586c0">.</font>t
<font color="#c586c0">implies</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
t2<font color="#569cd6">:</font> t<font color="#c586c0">.~</font>(<font color="#c586c0">^</font>next)
<font color="#569cd6">|</font> { d <font color="#c586c0">not</font>
<font color="#c586c0">in</font> n<font color="#c586c0">.</font>learned_times<font color="#c586c0">.</font>t2
}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
<font color="#dcdcaa">baseKnown</font><font color="#ce9178">[</font>n<font color="#ce9178">]</font>
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
Definition of subterms for some set of terms */</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">fun</font>
<font color="#dcdcaa">subterm</font><font color="#ce9178">[</font>supers<font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg<font color="#ce9178">]</font><font color="#569cd6">:</font>
<font color="#569cd6">set</font> mesg {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
VITAL: if you add a new subterm relation, needs to be added here,
too!</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">supers
<font color="#c586c0">+</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">supers<font color="#c586c0">.^</font>(plaintext)
<font color="#6a9955">-- union on new subterm relations inside parens</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/**
When does a strand 'originate' some term? </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">(Note:
it's vital this definition is about strands, not names.)</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">*/</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">pred</font>
<font color="#dcdcaa">originates</font><font color="#ce9178">[</font>s<font color="#569cd6">:</font>
strand<font color="#569cd6">,</font> d<font color="#569cd6">:</font>
mesg<font color="#ce9178">]</font> {</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
unsigned term t originates on n in N iff</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
term(n) is positive and</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
t subterm of term(n) and</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
whenever n' precedes n on the same strand, t is not subterm of n'</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">some</font>
m<font color="#569cd6">:</font> sender<font color="#c586c0">.</font>s
<font color="#569cd6">|</font> { <font color="#6a9955">-- messages
sent by strand s (positive term) </font></span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">d
<font color="#c586c0">in</font> <font color="#dcdcaa">subterm</font><font color="#ce9178">[</font>m<font color="#c586c0">.</font>data<font color="#ce9178">]</font>
<font color="#6a9955">-- d is a sub-term of m </font></span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">all</font>
m2<font color="#569cd6">:</font> (sender<font color="#c586c0">.</font>s
<font color="#c586c0">+</font> receiver<font color="#c586c0">.</font>s)
<font color="#c586c0">-</font> m <font color="#569cd6">|</font> { <font color="#6a9955">--
everything else on the strand</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
ASSUME: messages are sent/received in same timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{m2
<font color="#c586c0">in</font> m<font color="#c586c0">.^</font>(<font color="#c586c0">~</font>(next))}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#c586c0">implies</font>
</span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">{d
<font color="#c586c0">not</font> <font color="#c586c0">in</font>
<font color="#dcdcaa">subterm</font><font color="#ce9178">[</font>m2<font color="#c586c0">.</font>data<font color="#ce9178">]</font>}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
the agent generates this term</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">pred</font>
<font color="#dcdcaa">generates</font><font color="#ce9178">[</font>s<font color="#569cd6">:</font>
strand<font color="#569cd6">,</font> d<font color="#569cd6">:</font>
mesg<font color="#ce9178">]</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">some</font>
((s<font color="#c586c0">.</font>agent)<font color="#c586c0">.</font>generated_times)<font color="#ce9178">[</font>d<font color="#ce9178">]</font></span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
the attacker eventually learns this field value</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">pred</font>
<font color="#dcdcaa">attacker_learns</font><font color="#ce9178">[</font>s<font color="#569cd6">:</font>
strand<font color="#569cd6">,</font> d<font color="#569cd6">:</font>
mesg<font color="#ce9178">]</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">s<font color="#c586c0">.</font>d
<font color="#c586c0">in</font> Attacker<font color="#c586c0">.</font>learned_times<font color="#c586c0">.</font>Timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
the agent for this strand eventually learns this value</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f"><font color="#569cd6">pred</font>
<font color="#dcdcaa">strand_agent_learns</font><font color="#ce9178">[</font>learner<font color="#569cd6">:</font>
strand<font color="#569cd6">,</font> s<font color="#569cd6">:</font>
strand<font color="#569cd6">,</font> d<font color="#569cd6">:</font>
mesg<font color="#ce9178">]</font> {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">s<font color="#c586c0">.</font>d
<font color="#c586c0">in</font>
(learner<font color="#c586c0">.</font>agent)<font color="#c586c0">.</font>learned_times<font color="#c586c0">.</font>Timeslot</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#cccccc"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/***************************************************************/</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">------------------------------------------------------</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Keeping notes on what didn't work in modeling;</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
everything after this point is not part of the model.</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">------------------------------------------------------</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Problem: (k1, enc(k2, enc(n1, invk(k2)), invk(k1)))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
Problem: (k1, enc(x, invk(k3)), enc(k2, enc(k3, invk(k2)), invk(k1)))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
needs knowledge to grow on the way through the tree, possibly
sideways</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
so this approach won't work</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/*fun
accessibleSubterms[supers: set mesg, known: set mesg]: set mesg {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">let
openable = {c: Ciphertext | getInv[c.encryptionKey] in known} |</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">supers
+ </span></font></font></font>
</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">supers.^(plaintext
&amp; (openable -&gt; mesg))</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}*/</span></font></font></font></p>
<p style="line-height: 0.5cm; margin-bottom: 0cm"><br/>

</p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">/*</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
This is the example of where narrowing would be useful; it currently
causes</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
an error in last-checker (necessarily empty join on a side of an ITE
that isn't</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">--
really used). January 2024</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">run
{</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">some
pub: PublicKey | {</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">some
getInv[pub]</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">}</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<font color="#6a9955"><font face="Droid Sans Mono, monospace, monospace"><font size="2" style="font-size: 10pt"><span style="background: #1f1f1f">*/</span></font></font></font></p>
<p style="font-weight: normal; line-height: 0.5cm; margin-bottom: 0cm">
<br/>

</p>
<p style="line-height: 100%; margin-bottom: 0cm"><br/>

</p>
</body>
</html>