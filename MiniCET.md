# Second attempt

Main ideas:
- jumps go to labels
- block-based memory model for the instructions
  + what granularity though?
    block = whole procedure (Linear? Mach?)
         or basic block (LTL? MIR?) <- tentatively went for this below
            + jumps can only go to the beginning of basic blocks
            + but we do allow exiting from anywhere in the block
              * Q (Yonghyun): is that okay?
         or individual instruction (Santiago ASPLOS'25)? – seems extreme
  + (basic) blocks identified by labels?
- pc that's a CompCert-style pointer (label + offset)
- function pointers as first class values
- no longer merging all instructions together at this level

v ::= N n
    | FP l               function pointer to procedure starting at label l

registers and memory store such values, not just numbers (r[x]=v, m[n]=v)

pc ∈ cptr := (l,o)            label(=(basic) block identifier) and offset

p ∈ prog = list (list inst * bool)
                  ^—— basic block
- with lookup written `p[l][o]` where `l` is a label and o is an offset
- so `p[pc] = let '(l,o)=pc in (fst p[l])[o]`
- and `pc+1 = let '(l,o)=pc in (l,o+1)`
- `snd p[l]` stores a bool telling us if the basic block is a procedure start
- static well-formedness check:
  + all labels are defined by the program -- allows us to generate fresh blocks
  + direct branches/jumps don't go to procedure starts -- they are not calls
    * direct calls would be a different instruction, without this requirement
  + &l below only allowed for procedure starts (`snd p[l]` is true)
  + ctarget instruction not already used in source

e, a ::=
    | x                register
    | n                constant
    | e1 + e2          defined only on numbers
    | e1 = e2          defined on numbers and function pointers
    | ...
    | e1 ? e2 : e3     constant-time conditional
    | &l               function pointer, can only be used with call and =

i ::= skip
    | x := e           assignment to variable (i.e. register)
    | branch e l       conditional branch (direct)
    | jump l           direct jump (direct)
    | x <- load[a]     memory load (from flat data memory)
    | store[a] <- e'   memory store (to flat data memory)
    | call e           indirect call
    | ctarget          allowed target of call (CET)
    | ret              return using protected stack (CET)

o := OBranch b
   | OLoad n
   | OStore n
   | OCall l           offset 0 is implicit

d := DBranch b'
   | DCall (l',o')

## Sequential semantics with CT observations

p |- (pc, r, m, sk) -->^os  (pc', r', m', sk')

p[pc] = skip
————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[]  (pc+1, r, m, sk)

p[pc] = x:=e   r'=r[x<-eval r e]
—————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[]  (pc+1, r', m, sk)

p[pc] = branch e l   n=eval r e   b=(n≠0)
pc'=if b then (l,0) else pc+1
                 ^- only branch to beginning of basic block
———————————————————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[OBranch b] (pc', r, m, sk)

p[pc] = jump l
————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[] ((l,0), r, m, sk)
                               ^- only to beginning of basic block
                         ^--- no observation needed
                              (other maybe for the proofs)

p[pc] = x<-load[e]   n=eval r e   r'=r[x<-m[n]]
———————————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[OLoad n] (pc+1, r', m, sk)

p[pc] = store[e]<-e'   n=eval r e   v=eval r e'   m'=m[n<-v]
————————————————————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[OStore n] (pc+1, r, m', sk)

p[pc] = call e   l=eval r e
———————————————————————————————————————————————————————————
p |- (pc, r, m, sk) -->^[OCall l] ((l,0), r, m, (pc+1)::sk)

p[pc] = ctarget
———————————————————————————————————————————
p |- (pc, r, m, sk) -->^[] (pc+1, r, m, sk)

p[pc] = ret
——————————————————————————————————————————————————————
p |- (pc, r, m, pc'::sk) -->^[] (pc', r, m, sk)
                              ^————— no observation, right? (CET)

## Speculative semantics:

p |- (pc,r,m,sk,ct,ms) -->_ds^os (pc',r',m',sk',ct',ms')  (the interesting parts)
                ^———— expecting only call target

p[pc]=branch e l   n=eval r e   b=(n≠0)
pc'=if b' then (l,0) else pc+1   ms'=ms\/b≠b'
——————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DBranch b']^[OBranch b] (pc',r,m,sk,⊥,ms')

p[pc]=x<-load[e]   n=eval r e   r'=r[x<-m[n]]
———————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[]^[OLoad n] (pc+1,r',m,sk,⊥,ms)

p[pc]=store[e]<-e'   n=eval r e   n'=eval r e'   m'=m[n<-n']
———————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥) -->_[]^[OStore n] (pc+1,r,m',sk,⊥,ms)

p[pc]=call e   l=eval r e   ms'=ms\/(l,0)≠pc'
——————————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DCall pc']^[OCall l] (pc',r,m,(pc+1)::sk,⊤,ms')

p[pc] = ctarget
———————————————————————————————————————————————
p |- (pc,r,m,sk,⊤,ms) -->^[] (pc+1,r,m,sk,⊥,ms)
                ^--- ctarget can only run after call? (CET)

p[pc] = ret
—————————————————————————————————————————————————————————
p |- (pc, r, m, pc'::sk, ⊥) -->_[]^[] (pc', r, m, sk, ⊥)
                                 ^————— still uninteresting
                              (since return stack protected)

Should we add step directives for jump? and/or even ret?
- this may help doing induction on directives
- alternatively: could do like Gilles et al always do nad
  add step directives so that |ds|=length of the execution?
  + this would give us something simple to do induction on, but then need to
    account for the fact that the compiler / SLH transformation can change the
    length of the execution

Notes:
- no (mis-)speculation on returns; assuming protected stack
- DLoad a' and DStore a' are gone with memory layout concrete
  + we no longer have that |os|=|ds|, which will impact the proofs
- tentatively went "uniform" on remaining cases, following
  Jonathan's proposal and Santiago's POPL'25+ASPLOS'25 formalizations
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

## Monad used below: M a = nat -> a * prog

return x _ = (x,[])

bind m f c =
  let '(r,p) = m c in
  let '(r',p') = f r (c+|p|) in
  (r',p++p')

add-block bl c = (c,[(bl,false)])

## New attempt at defining Ultimate SLH

uslh :: inst -> M (list inst)

uslh skip = return [skip]
uslh (x:=e) = return [x:=e]
uslh (jump l) = return [jump l]
uslh (ctarget) = return [skip]    these inserted by transformation of basic blocks
                                  (not present in original program)
uslh (ret) = return [ret]         nothing to do here because of CET
uslh (x<-load[e]) =
  let e' := "ms"=1 ? 0 : e in     masking the whole address
  return [x<-load[e']]            - fine that 0 is a valid data memory address? Seems so.
uslh (store[e] <- e) =
  let e' := "ms"=1 ? 0 : e in     masking the whole address
  return [store[e'] <- e]         - fine that 0 is a valid data memory address?
                                    Seems our defense of calls can deal with this,
                                    but the attack is more difficult to model:

TODO: What happens if a code pointer is stored at address 0
      and speculatively overwritten? Spectre 1.1:
      https://secure-compilation.zulipchat.com/#narrow/channel/436285-speculation/topic/Spectre1.2E1/near/459448106
- At a lower level, when the overwritten code pointer is loaded and jumped to,
  we do a jump to an address that's attacker influenced
  + Our current speculative semantics of call would get stuck on `l=eval r e`,
    which doesn't seem like a secure overapproximation of lower-level attacker behavior
  + We can fix this by allowing the attacker to also choose an arbitrary address
    when `n=eval r e`?
    * In theory, we can add an extra Call rule to the speculative semantics
      (about the ms=⊤ precondition see below though):

p[pc]=call e   n=eval r e
———————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,⊤) -->_[DCall pc']^[OCall n] (pc',r,m,(pc+1)::sk,⊤,⊤)

In practice, the single rule corresponding to the two ones looks something like this:

p[pc]=call e     v = eval r e    n=v ==> ms=⊤    ms'=ms\/(l=v ==> (l,0)≠pc')
——————————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DCall pc']^[OCall v] (pc',r,m,(pc+1)::sk,⊤,ms')

      is_true (if_some (to_nat v) (fun _ => ms));;
      let ms' := ms || (if_some (to_fp v)
                          (fun l => negb ((fst pc' =? l) && (snd pc' =? 0)))) in

Is the `n=eval r e ==> ms=⊤` condition needed/helpful/reasonable though?
- It doesn't seem needed or helpful to me, so I removed it

p[pc]=call e     v = eval r e    ms'=ms\/(l=v ==> (l,0)≠pc')
——————————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DCall pc']^[OCall v] (pc',r,m,(pc+1)::sk,⊤,ms')

      let ms' := ms || (if_some (to_fp v)
                          (fun l => negb ((fst pc' =? l) && (snd pc' =? 0)))) in


uslh (branch e l) =
  let e' = "ms"=0 && e in                           masking branch condition
  bind l' <- add-block ["ms" := ~e'?1:"ms"; jump l] updating flag when actually branching
  return ([branch e' l'; "ms" := e'?1:"ms"])        updating flag when not branching

  DONE: also need to update flag when actually branching (solved above)
  + what if multiple branches/jumps go to the same label
    and we add flag updating at that label?
    * update flag wrt multiple boolean conditions? — not correct!
    * create new label/block <—— doing this above

uslh (call e) =
  let e' := "ms"=1 ? &0 : e in    masking the whole address
                                  - fine that &0 is valid function pointer, right?
  return ["callee":=e'; call e']

uslh-blk :: (nat * (list inst * bool)) -> M (list inst * bool)

uslh-blk (_, (bl,false)) =     block is not procedure start
  bind bl' <- concatM (mapM uslh bl)
  return (bl', false)
uslh-blk (l, (bl,true)) =      block is procedure start
  bind bl'<- uslh-blk l (bl,false)
  return ([ctarget; "ms" := "callee" = &l ? "ms" : 1] ++ bl', true)

uslh-prog :: prog -> prog

uslh-prog p =
  let '(p',newp) = (mapM uslh-blk (add-index p)) (length p) in p' ++ newp

### Original monad: M a = nat -> a * nat + some more manual stuff

uslh (branch e l) :  =
  let e' = "ms"=0 && e in             masking branch condition
  bind l' <- fresh_block do           need to track used/free blocks
  return ([branch e' l'; "ms" := e'?1:"ms"],   updating flag when not branching
           (l',["ms" := ~e'?1:"ms"; jump l]))  updating flag when actually branching

### Somewhat better monad: M a = prog -> a * prog

DONE: something quite shady was happening above:
      both mapping over the program AND changing it via state passing

I guess could combine the p1 and p2 at the end:
uslh-prog p = let '(p1,p2) = (mapM uslh-blk (add-index p)) p in update p1 in p2

but there are better ways to express this, for instance:

### Somewhat better still: M a = nat -> a * nat * prog?
                                                   ^————— added blocks (output monad)
                   old-counter ——^            ^————— new-counter

uslh-prog p =
  let '(p',_,newp) = (mapM uslh-blk (add-index p)) (length p) in p' ++ newp

But we have new-counter = old-counter + |newp|, so maybe we don't need it?
- switched to even better monad: `M a = nat -> a * prog` above

# First attempt

ae := ... like in ImpArr for maximal reuse? (testing)
    vs. adding
    | procaddr n       a way to get address of proc n in current program
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
    | ctarget      allowed target of call (CET)
    | ret              return using protected stack (CET)
    | abort            unclear if needed

p ::= [c₀,...,cₙ]       program is a list of commands for procedure bodies

link p = [ctarget, resolve c₀ p] ++         program to instruction memory
          ... ++ [ctarget, resolve cₙ p]

## Sequential semantics with CT observations:

o := OBranch b
   | OLoad a
   | OStore a
   | OCall a
   | ORet a

p |- (pc, r, m, sk, ct) -->^os  (pc', r', m', sk', ct')

p[pc] = skip
——————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[]  (pc+1, r, m, sk, ⊥)

p[pc] = x:=ae   r'=r[x<-aeval r ae]
————————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[]  (pc+1, r', m, sk, ⊥)

p[pc] = branch be +n   b=beval r be   pc'=if b then pc+n else pc+1
——————————————————————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[OBranch b] (pc', r, m, sk, ⊥)

p[pc] = jump n
———————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[] (n, r, m, sk, ⊥)
                             ^--- no observation needed

p[pc] = x<-load[ae]   a=aeval r ae   r'=r[x<-m[a]]
——————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[OLoad a] (pc+1, r', m, sk, ⊥)

p[pc] = store[ae]<-ae'   a=aeval r ae   n=aeval r ae'   m'=m[a<-n]
——————————————————————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[OStore a] (pc+1, r, m', sk, ⊥)

p[pc] = call ae   a=aeval r ae
——————————————————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊥) -->^[OCall a] (a, r, m, (pc+1)::sk, ⊤)

p[pc] = ctarget
——————————————————————————————————————————————————
p |- (pc, r, m, sk, ⊤) -->^[] (pc+1, r, m, sk, ⊥)
                    ^--- ctarget can only run after call?

p[pc] = ret
————————————————————————————————————————————————————————
p |- (pc, r, m, a::sk, ⊥) -->^[ORet a] (a, r, m, sk, ⊥)

## Speculative semantics:

d := DBranch b'
   | DCall a'

p |- (pc,r,m,sk,ct,ms) -->_ds^os (pc',r',m',sk',ms')  (the interesting parts)

p[pc]=branch be +n   b=beval r be   pc'=if b' then pc+n else pc+1   ms'=ms\/b≠b'
————————————————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DBranch b']^[OBranch b] (pc',r,m,sk,⊥,ms')

p[pc]=x<-load[ae]   a=aeval r ae   r'=r[x<-m[a]]
———————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[]^[OLoad a] (pc+1,r',m,sk,⊥,ms)

p[pc]=store[ae]<-ae'   a=aeval r ae   n=aeval r ae'   m'=m[a<-n]
————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥) -->_[]^[OStore a] (pc+1,r,m',sk,⊥,ms)

p[pc]=call ae   a=aeval r ae   ms'=ms\/a≠a'
—————————————————————————————————————————————————————————————————————————
p |- (pc,r,m,sk,⊥,ms) -->_[DCall a']^[OCall a] (a',r,m,(pc+1)::sk,⊤,ms')

## Failed attempt at defining Ultimate SLH

uslh skip = [skip]
uslh (x:=e) = [x:=e]
uslh (jump n) = [jump n]
uslh (ctarget) = [skip]           these should anyway be inserted by linking
                                  (not present in original program)
uslh (ret) = [ret]                - nothing to do here because of CET?
uslh (x<-load[ae]) =
  let ae' := "ms"=1 ? 0 : ae in   masking the whole address
  [x<-load[ae']]                  - fine if this is valid data memory, right?
uslh (store[ae] <- e) =
  let ae' := "ms"=1 ? 0 : ae in   masking the whole address
  [store[ae'] <- e]               - fine if this is valid data memory, right?

uslh (branch be +n) =
  let be' = "ms"=0 && be in             masking branch condition
  [branch be' +n, "ms" := be'?1:"ms"]   updating flag when not branching

  TODO: also need to update flag when actually branching; possible?
  TODO: also need to adjust offset of this and other branches to account for added instructions
  - branching to labels instead of to concrete offsets could help?
    + still, what if multiple branches/jumps go to the same label
      and we add flag updating at that label?
      update flag wrt multiple boolean conditions?
  - I don't (yet) know how to do SLH for unstructured programs;
    + LLVM Machine IR works with a CFG; even that's more structured:
      labeled basic blocks connected by jumps or branches?
    + if this gets too hard it may be easier to do it a bit earlier in the
      compiler? (e.g. like Lucie did, or something in between)

uslh (call ae) =
  let ae' := "ms"=1 ? 0 : ae in   masking the whole address
                                  - fine if 0 is valid call site, right?
  ["callee":=ae', call ae']

  TODO: even if ae is not masked it may go to a different place than before,
        since uslh itself will likely change the instruction memory layout
        - was this Yonghyun's worry yesterday?
        - it seems pretty bad since `ae` can be computed in arbitrary ways,
          not only using nice (potential) features like `proc_addr` or code labels
        - the easiest way out may be to define a language with function
          pointers and in which trying to abuse function pointers
          (e.g. calling random crap) is UB or an error

uslh_prog p :=
  map (fun c => ["ms" := "callee" = get_pc+delta ? "ms" : 1]) p
  - this part seems easiest to define using new get_pc feature,
    otherwise only know what address to check against after the
    modified code gets laid out in memory (linked)
