(*
ae := ... like in ImpArr for maximal reuse? (testing)
    vs. adding
    | proc_addr n      a way to get address of proc n in current program
                       - useful for writing programs with absolute addresses
                       - resolved statically, but only after we know whole p
                       - even for random generation difficult to avoid?

be := ... like in ImpArr for maximal reuse? (testing)

c ::= [i₀,...,iₙ]      command is now sequence of instructions

i ::= skip
    | x := ae          assignment to variable (i.e. register)
    | branch be +n     conditional branch (direct, relative)
    | jump n           direct jump (absolute)
                       - since it's direct, can't use with proc_addr
                       - not usable without adding labels and more resolving
                       - alt: make resolve go from procedure-relative
                         to absolute? also want to allow wild jumps though
    | x <- load[ae]    memory load (from flat data memory)
    | store[ae] <- ae' memory store (to flat data memory)
    | call ae          indirect call
    | call_target      allowed target of call (CET)
    | ret              return using protected stack (CET)
    | abort            unclear if needed

p ::= [c₀,...,cₙ]       program is a list of commands for procedure bodies

link p = resolve c₀ p ++ ... ++ resolve cₙ p    program to instruction memory

Sequential semantics with CT observations:
-----------------------------------------

o := OBranch b
   | OLoad a
   | OStore a
   | OCall a
   | ORet a

p |- (pc, r, m, sk, ct) -->^os  (pc', r', m', sk', ct')

p[pc] = skip
---------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[]  (pc+1, r, m, sk, ⊥)

p[pc] = x:=ae   r'=r[x<-aeval r ae]
----------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[]  (pc+1, r', m, sk, ⊥)

p[pc] = branch be +n   b=beval r be   pc'=if b then pc+n else pc+1
------------------------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[OBranch b] (pc', r, m, sk, ⊥)

p[pc] = jump n
-----------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[] (n, r, m, sk, ⊥)
                                 ^--- no observation needed?

p[pc] = x<-load[ae]   a=aeval r ae   r'=r[x<-m[a]]
--------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[OLoad a] (pc+1, r', m, sk, ⊥)

p[pc] = store[ae]<-ae'   a=aeval r ae   n=aeval r ae'   m'=m[a<-n]
------------------------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[OStore a] (pc+1, r, m', sk, ⊥)

p[pc] = call ae   a=aeval r ae
--------------------------------------------------------------
p |- (pc, r, m, sk, ⊥) -->^[OCall a] (a, r, m, (pc+1)::sk, ⊤)

p[pc] = call_target
--------------------------------------------------
p |- (pc, r, m, sk, ⊤) -->^[] (pc+1, r, m, sk, ⊥)
                      ^--- call_target can only run after call?

p[pc] = ret
--------------------------------------------------------
p |- (pc, r, m, a::sk, ⊥) -->^[ORet a] (a, r, m, sk, ⊥)

Speculative semantics:
----------------------

d := DBranch b'
   | DCall a'

p |- (pc,r,m,sk,ct,ms) -->_ds^os (pc',r',m',sk',ms')  (the interesting parts)

p[pc]=branch be +n   b=beval r be   pc'=if b' then pc+n else pc+1   ms'=ms\/b≠b'
--------------------------------------------------------------------------------
p |- (pc,r,m,sk,⊥,ms) -->_[DBranch b']^[OBranch b] (pc',r,m,sk,⊥,ms')

p[pc]=x<-load[ae]   a=aeval r ae   r'=r[x<-m[a]]
-----------------------------------------------------------
p |- (pc,r,m,sk,⊥,ms) -->_[]^[OLoad a] (pc+1,r',m,sk,⊥,ms)

p[pc]=store[ae]<-ae'   a=aeval r ae   n=aeval r ae'   m'=m[a<-n]
----------------------------------------------------------------
p |- (pc,r,m,sk,⊥) -->_[]^[OStore a] (pc+1,r,m',sk,⊥,ms)

p[pc]=call ae   a=aeval r ae   ms'=ms\/a≠a'
-------------------------------------------------------------------------
p |- (pc,r,m,sk,⊥,ms) -->_[DCall a']^[OCall a] (a',r,m,(pc+1)::sk,⊤,ms')

Notes:
- no (mis-)speculation on returns; assuming protected stack
- DLoad a' and DStore a' are gone with memory layout concrete
  + we no longer have that |os|=|ds|, which will impact the proofs
- tentatively went "uniform" on remaining cases, following
  Jonathan's proposal and Santiago's POPL'25 formalization
  + the nice part is that with this we don't add extra rules
  + for forcing DCalls it seems fine to leak `OCall a`,
    since this sequential semantics doesn't get stuck
    immediately when calling an invalid address,
    but only in then next step if the instruction can't be fetched
  + this formulation makes it hard for the attacker to just step?
    still possible, but only by chance and
    attacker doesn't know whether it stepped or not, does it?
  + practically, can we randomly generate directions
    that don't force calls too frequently?
    - can we set this up so that we get the observation(s)
      before we have to issue the direction(s)?
    - probably no big problem with just a few procedures
*)
