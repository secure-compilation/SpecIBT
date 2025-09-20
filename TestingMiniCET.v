(** * Testing MiniCET *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String.

From SECF Require Import Utils.
From SECF Require Import ListMaps.

(** The factoring of expressions is taken from the latest SpecCT chapter *)

Inductive binop : Type :=
  | BinPlus
  | BinMinus
  | BinMult
  | BinEq
  | BinLe
  | BinAnd
  | BinImpl.

Definition not_zero (n : nat) : bool := negb (n =? 0).
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition eval_binop_nat (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => bool_to_nat (n1 =? n2)
  | BinLe => bool_to_nat (n1 <=? n2)
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp)
  | ACTIf (b : exp) (e1 e2 : exp)
  | FPtr (l : nat). (* <- NEW: function pointer to procedure at label [l] *)

(** We encode all the previous arithmetic and boolean operations: *)

Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr e1 e2 := BImpl (BNot e1) e2.
Definition BEq := ABin BinEq.
Definition BNeq e1 e2 := BNot (BEq e1 e2).
Definition BLe := ABin BinLe.
Definition BGt e1 e2 := BNot (BLe e1 e2).
Definition BLt e1 e2 := BGt e2 e1.

Hint Unfold eval_binop_nat : core.
Hint Unfold APlus AMinus AMult : core.
Hint Unfold BTrue BFalse : core.
Hint Unfold BAnd BImpl BNot BOr BEq BNeq BLe BGt BLt : core.

(** The notations we use for expressions are the same as in Imp,
    except the notation for [be?e1:e2] and [&l] which are new: *)
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".
Definition msf : string := "msf".
Definition callee : string := "callee".

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.

(* HIDE: BCP: Again, these notations are in flux in PLF... *)
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2)
                 (in custom com at level 20, no associativity).

Notation "'&' l"   := (FPtr l)
                        (in custom com at level 75,
                          l constr at level 0, right associativity).

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

(** Now to the first interesting part, values instead of just numbers: *)

Inductive val : Type :=
  | N (n:nat)
  | FP (l:nat). (* <- NEW: function pointer to procedure at label [l] *)

(** Since type mismatches are now possible, evaluation of expressions can now
    fail, so the [eval] function is in the option monad. *)

Definition to_nat (v:val) : option nat :=
  match v with
  | N n => Some n
  | FP _ => None
  end.

Definition to_fp (v:val) : option nat :=
  match v with
  | FP l => Some l
  | N _ => None
  end.

Definition eval_binop (o:binop) (v1 v2 : val) : option val :=
  match v1, v2 with
  | N n1, N n2 => Some (N (eval_binop_nat o n1 n2))
  | FP l1, FP l2 =>
      match o with
      | BinEq => Some (N (bool_to_nat (l1 =? l2)))
      | _ => None (* Function pointers can only be tested for equality *)
      end
  | _, _ => None (* Type error *)
  end.

Definition reg := total_map val.

Fixpoint eval (st : reg) (e: exp) : option val :=
  match e with
  | ANum n => ret (N n)
  | AId x => ret (apply st x)
  | ABin b e1 e2 =>
      v1 <- eval st e1;;
      v2 <- eval st e2;;
      eval_binop b v1 v2
  | <{b ? e1 : e2}> =>
      v1 <- eval st b;;
      n1 <- to_nat v1;; (* Can't branch on function pointers *)
      if not_zero n1 then eval st e1 else eval st e2
  | <{&l}> => ret (FP l)
  end.

(* PROPERTY: forAll e st, is_some (eval st e) ==> True
   will show we need custom generators *)

Inductive inst : Type :=
  | ISkip
  | IAsgn (x : string) (e : exp)
  | IBranch (e : exp) (l : nat)
  | IJump (l : nat)
  | ILoad (x : string) (a : exp)
  | IStore (a : exp) (e : exp)
  | ICall (fp:exp)
  | ICTarget
  | IRet.

Notation "'skip'"  :=
  ISkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (IAsgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "'branch' e 'to' l"  := (* SOONER: get rid of the [to] *)
  (IBranch e l)
     (in custom com at level 0, e custom com at level 85,
      l constr at level 0, no associativity) : com_scope.
Notation "'jump' l"  :=
  (IJump l)
     (in custom com at level 0,
      l constr at level 0, no associativity) : com_scope.
Notation "x '<-' 'load[' a ']'"  :=
  (ILoad x a)
     (in custom com at level 0, x constr at level 0,
      a custom com at level 85, no associativity) : com_scope.
Notation "'store[' a ']'  '<-' e"  :=
  (IStore a e)
     (in custom com at level 0, a custom com at level 0,
      e custom com at level 85,
         no associativity) : com_scope.
Notation "'call' e" :=
  (ICall e)
    (in custom com at level 89, e custom com at level 99) : com_scope.
Notation "'ctarget'"  :=
  ICTarget (in custom com at level 0) : com_scope.
Notation "'ret'"  :=
  IRet (in custom com at level 0) : com_scope.

Definition prog := list (list inst * bool).

(** The inner [list inst] is a basic block, and the [bool] is telling us if the
    basic block is a procedure start. *)

Notation "'i[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (in custom com at level 89, x custom com at level 99,
      y custom com at level 99, no associativity) : com_scope.

Check <{{ skip }}>.
Check <{{ i[skip ; skip ; skip] }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Check <{ true && ~(false && true) }>.
(* SOONER: need tests for new notations *)
(* Check <{{ if true then skip else skip end }}>. *)
(* Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>. *)
(* Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>. *)
Check <{{ call 0 }}>.
Check <{{ ctarget }}>.
Check <{{ ret }}>.
Check <{{ branch 42 to 42 }}>.
Check <{{X<-load[8]}}>.
Check <{{store[X + Y]<- (Y + 42)}}>.

Definition cptr : Type := nat * nat. (* label(=(basic) block identifier) and offset *)

Definition mem := list val.

Definition cfg : Type := ((cptr*reg)*mem)*list cptr. (* (pc, register set, memory, stack frame) *)

Inductive observation : Type :=
  | OBranch (b:bool)
  | OLoad (n:nat)
  | OStore (n:nat)
  | OCall (l:nat).

Definition obs := list observation.

Definition fetch (p:prog) (pc:cptr) : option inst :=
  let '(l,o) := pc in
  r <- nth_error p l;;
  nth_error (fst r) o.

Notation "p '[[' pc ']]'" := (fetch p pc).

Definition inc (pc:cptr) : cptr :=
  let '(l,o) := pc in (l,o+1).

Notation "pc '+' '1'" := (inc pc).

Definition step (p:prog) (c:cfg) : option (cfg * obs) :=
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{skip}}> | <{{ctarget}}> =>
      ret ((pc+1, r, m, sk), [])
  | <{{x:=e}}> =>
      v <- eval r e;;
      ret ((pc+1, (x !-> v; r), m, sk), [])
  | <{{branch e to l}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      let b := not_zero n in
      ret ((if b then (l,0) else pc+1, r, m, sk), [OBranch b])
  | <{{jump l}}> =>
      ret (((l,0), r, m, sk), [])
  | <{{x<-load[e]}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      v' <- nth_error m n;;
      ret ((pc+1, (x !-> v'; r), m, sk), [OLoad n])      
  | <{{store[e]<-e'}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      v' <- eval r e';;
      ret ((pc+1, r, upd n m v', sk), [OStore n])
  | <{{call e}}> =>
      v <- eval r e;;
      l <- to_fp v;;
      ret (((l,0), r, m, (pc+1)::sk), [OCall l])
  | <{{ret}}> =>
      pc' <- hd_error sk;;
      ret ((pc', r, m, tl sk), [])
  end.

(* Morally state+output monad hidden in here: step p >> steps f' p  *)
Fixpoint steps (f:nat) (p:prog) (c:cfg) : option (cfg * obs) :=
  match f with
  | S f' =>
      co1 <- step p c;;
      let '(c1,o1) := co1 in
      co2 <- steps f' p c1;;
      let '(c2,o2) := co2 in
      ret (c2, o1++o2)
  | 0 => ret (c,[])
  end.

(** SOONER: write down speculative semantics *)

Inductive direction : Type :=
  | DBranch (b':bool)
  | DCall (lo:cptr).

Definition dirs := list direction.

Definition spec_cfg : Type := ((cfg * bool) * bool).

Definition is_true (b:bool) : option unit :=
  if b then Some tt else None.

Definition is_false (b:bool) : option unit :=
  if b then None else Some tt.

Definition is_dbranch (d:direction) : option bool :=
  match d with
  | DBranch b => Some b
  | _ => None
  end.

Definition is_dcall (d:direction) : option cptr :=
  match d with
  | DCall pc => Some pc
  | _ => None
  end.

Definition if_some {a:Type} (o:option a) (f:a->bool) : bool :=
  match o with
  | Some x => f x
  | None => true
  end.

Definition spec_step (p:prog) (sc:spec_cfg) (ds:dirs) : option (spec_cfg * dirs * obs) :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{branch e to l}}> =>
      is_false ct;;
      d <- hd_error ds;;
      b' <- is_dbranch d;;
      v <- eval r e;;
      n <- to_nat v;;
      let b := not_zero n in
      let ms' := ms || negb (Bool.eqb b b') in 
      let pc' := if b' then (l, 0) else (pc+1) in
      ret ((((pc', r, m, sk), ct, ms'), tl ds), [OBranch b])
  | <{{call e}}> =>
      is_false ct;;
      d <- hd_error ds;;
      pc' <- is_dcall d;;
      v <- eval r e;;
      (* Old code: *)
      (* l <- to_fp v;; *)
      (* let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in  *)
      (* New code (see explanation in MiniCET.md; Spectre 1.1): *)
      is_true (if_some (to_nat v) (fun _ => ms));;
      let ms' := ms || (if_some (to_fp v)
                          (fun l => negb ((fst pc' =? l) && (snd pc' =? 0)))) in
      ret ((((pc', r, m, sk), true, ms'), tl ds), [OCall (fst pc')])
  | <{{ctarget}}> =>
      is_true ct;; (* ctarget can only run after call? (CET) Maybe not? *)
      ret (((pc+1, r, m, sk), false, ms), ds, [])
  | _ =>
      is_false ct;;
      co <- step p c;;
      let '(c',o) := co in
      ret ((c',false,ms), ds, o)
  end.

Fixpoint spec_steps (f:nat) (p:prog) (c:spec_cfg) (ds:dirs)
  : option (spec_cfg * dirs * obs) :=
  match f with
  | S f' =>
      cdo1 <- spec_step p c ds;;
      let '(c1,ds1,o1) := cdo1 in
      cdo2 <- spec_steps f' p c1 ds1;;
      let '(c2,ds2,o2) := cdo2 in
      ret (c2,ds2,o1++o2)
  | 0 =>
      None (* Q: Do we need more precise out-of-fuel error here? *)
  end.

(* SOONER: define monad used by uslh *)

Definition M (A: Type) := nat -> A * prog.

Definition uslh_ret {A: Type} (x: A) : M A :=
  fun c => (x, []).

Definition uslh_bind {A B: Type} (m: M A) (f: A -> M B) : M B :=
  fun c =>
    let '(r, p) := m c in
    let '(r', p') := f r (c + Datatypes.length p) in
    (r', p ++ p').

#[export] Instance monadUSLH : Monad M :=
  { ret := @uslh_ret;
    bind := @uslh_bind
  }.

(* No mapM in ExtLib, seems it got removed: https://github.com/rocq-community/coq-ext-lib/commit/ef2e35f43b2d1db4cb64188e9521948fdd1e0527 *)
Definition mapM {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  sequence (List.map f l).

Definition concatM {A: Type} (m: M (list (list A))) : M (list A) :=
  xss <- m;; ret (List.concat xss).

Definition add_block (bl: list inst) (c: nat) := (c, [(bl, false)]).

Definition add_block_M (bl: list inst) : M nat :=
  fun c => add_block bl c.

(* SOONER: Try to use this to define our new uslh *)

Definition uslh_inst (i: inst) : M (list inst) :=
  match i with
  | <{{ctarget}}> => ret [<{{skip}}>]
  | <{{x<-load[e]}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{x<-load[e']}}>]
  | <{{store[e] <- e1}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{store[e'] <- e1}}>]
  | <{{branch e to l}}> =>
      let e' := <{ (msf=0) && e }> in (* if mispeculating always pc+1 *)
      l' <- add_block_M <{{ i[msf := ~e' ? 1 : msf; jump l] }}>;;
      ret <{{ i[branch e' to l'; msf := e' ? 1 : msf] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &0 : e }> in
      ret <{{ i[callee:=e'; call e'] }}>
  | _ => ret [i]
  end.

Definition uslh_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  bl' <- concatM (mapM uslh_inst bl);;
  if is_proc then
    ret (<{{ i[ctarget; msf := callee = &l ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition uslh_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM uslh_blk idx_p (Datatypes.length p) in
  (p' ++ newp).

(* SOONER: Run some unit tests *)

(* Static checks for both source and target programs *)

Definition wf_label (p:prog) (is_proc:bool) (l:nat) : bool :=
  match nth_error p l with
  | Some (_,b) => Bool.eqb is_proc b (* also know l <? List.length p *)
  | None => false
  end.

Fixpoint wf_exp (p:prog) (e : exp) : bool :=
  match e with
  | ANum _ | AId _ => true
  | ABin _ e1 e2  | <{_ ? e1 : e2}> => wf_exp p e1 && wf_exp p e2
  | <{&l}> => wf_label p true l
  end.

Definition wf_inst (p:prog) (i : inst) : bool :=
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> => true
  | <{{_:=e}}> | <{{_<-load[e]}}> | <{{call e}}> => wf_exp p e
  | <{{store[e]<-e'}}> => wf_exp p e && wf_exp p e'
  | <{{branch e to l}}> => wf_exp p e && wf_label p false l
  | <{{jump l}}> => wf_label p false l
  end.

Definition wf_blk (p:prog) (blb : list inst * bool) : bool :=
  forallb (wf_inst p) (fst blb).

Definition wf (p:prog) : bool :=
  forallb (wf_blk p) p.

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

(* May (not) need separate check for no ctarget, only for source *)

(* ** Property testing of MiniCET *)

(* Simple utility function to check if a value is Some.
  TODO: Check if there is an Stdlib or Extlib function with the same
  functionality. *)
Definition is_some {A} (v : option A) : bool := match v with
  | Some _ => true
  | None => false
  end.
  
(** custom tactics *)

Ltac inv H := inversion H; subst; clear H.

(** Generators and shows *)

#[export] Instance genId : Gen string :=
  {arbitrary := (n <- freq [(10, ret 0);
                             (9, ret 1);
                             (8, ret 2);
                             (4, ret 3);
                             (2, ret 4);
                             (1, ret 5)];;
                 ret ("X" ++ show n)%string) }.

#[export] Instance shrinkId : Shrink string :=
  {shrink :=
    (fun s => match get 1 s with
              | Some a => match (nat_of_ascii a - nat_of_ascii "0") with
                          | S n => ["X" ++ show (S n / 2); "X" ++ show (S n - 1)]
                          | 0 => []
                          end
              | None => nil
              end)%string }.
Eval compute in (shrink "X5")%string.
Eval compute in (shrink "X0")%string.

Derive (Arbitrary, Shrink) for binop.
Derive (Arbitrary, Shrink) for exp.
Derive (Arbitrary, Shrink) for inst.

(* Derive Show for binop. *)
(* Derive Show for exp. *)
(* Derive Show for inst. *)

#[export] Instance showBinop : Show binop :=
  {show :=fun op => 
      match op with
      | BinPlus => "+"%string
      | BinMinus => "-"%string  
      | BinMult => "*"%string
      | BinEq => "="%string
      | BinLe => "<="%string
      | BinAnd => "&&"%string
      | BinImpl => "->"%string
      end
  }.

#[export] Instance showExp : Show exp :=
  {show := 
    (let fix showExpRec (e : exp) : string :=
       match e with
       | ANum n => show n
       | AId x => x
       | ABin o e1 e2 => 
           "(" ++ showExpRec e1 ++ " " ++ show o ++ " " ++ showExpRec e2 ++ ")"
       | ACTIf b e1 e2 =>
           "(" ++ showExpRec b ++ " ? " ++ showExpRec e1 ++ " : " ++ showExpRec e2 ++ ")"
       | FPtr l => "&" ++ show l
       end
     in showExpRec)%string
  }.

#[export] Instance showInst : Show inst :=
  {show := 
      (fun i =>
         match i with
         | ISkip => "skip"
         | IAsgn x e => x ++ " := " ++ show e
         | IBranch e l => "branch " ++ show e ++ " to " ++ show l
         | IJump l => "jump " ++ show l
         | ILoad x a => x ++ " <- load[" ++ show a ++ "]"
         | IStore a e => "store[" ++ show a ++ "] <- " ++ show e
         | ICall fp => "call " ++ show fp
         | ICTarget => "ctarget"
         | IRet => "ret"
         end)%string
  }.


Sample (arbitrarySized 1 : G binop).
Sample (arbitrarySized 2 : G binop).
Sample (arbitrarySized 1 : G exp).
Sample (arbitrarySized 1 : G inst).

Derive Show for val.

(* #[export] Instance showExp : Show exp := *)
(*   {show := *)
(*       (let fix showExpRec (a:exp) : string := *)
(*          match a with *)
(*          | AId i => String DoubleQuote (i ++ String DoubleQuote "") *)
(*          | ANum n => show n *)
(*          | ABin bop e1 e2 => "(" ++ showExpRec e1 ++ " " ++ show bop ++ " " ++ showExpRec e2 ++ ")" *)
(*          | ACTIf b e1 e2 => showExpRec b ++ " ? " ++ showExpRec e1 ++ " : " ++ showExpRec e2 *)
(*          | FPtr fp => "&" ++ show fp *)
(*          end *)
(*        in showExpRec)%string *)
(*    }. *)

(* As in [TestingStaticIFC.v], we generate a finite total map which we use as state. *)
#[export] Instance genTotalMap (A:Type) `{Gen A} : Gen (total_map A) :=
  {arbitrary := (d <- arbitrary;;
                 v0 <- arbitrary;;
                 v1 <- arbitrary;;
                 v2 <- arbitrary;;
                 v3 <- arbitrary;;
                 v4 <- arbitrary;;
                 v5 <- arbitrary;;
                 ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
                         ("X3",v3); ("X4",v4); ("X5",v5)])%string)}.

(* [TestingStaticIFC.v]: The ;; notation didn't work with oneOf, probably related to monadic
   bind also using ;;. So I redefined the notation using ;;;. *)
Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.

Derive (Arbitrary, Shrink) for val.
Derive (Arbitrary, Shrink) for binop.
Derive (Arbitrary, Shrink) for exp.

(** The first unit test *)

(* The first property I test is the one proposed by Catalin, which shows how sane our
  generators are: *)
(* "forAll e st, is_some (eval st e) ==> True" *)

(* Tests with generators derived by QuickChick are almost fully discarded: *)
QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll arbitrary (fun (exp : exp) =>
            implication (is_some (eval state exp)) true))).
(* "*** Gave up! Passed only 4988 tests" *)

(* Above, we test if our evaluation succeeds, i.e. "eval" function returns "Some" value.
    From the definition of "eval", it fails in two cases: if the expression contains a binary expression 
    on a function pointer; or if the expression branches on a function pointer.
*)

(* Both branching and operating on function pointers may happen in two cases: when
    a function pointer is directly used, or an identifier which evaluates to a function pointer
    is used. *)

(* To generate expressions which successfully evaluate I restrict these two cases.
    Similar to [TestingStaticIFC], I first define generators for "leaves": expressions of size 0.
    In our case, there are two such generators: one that permits all expressions, and the other which
    only allows non-pointer expressions. *)

Definition is_not_ptr (state : reg) (var : string) :=
  match apply state var with
  | N _ => true
  | FP _ => false
  end.

(* This generator creates leaves as numbers and identifiers, which evaluate to numbers  *)
Definition gen_exp_leaf_no_ptr (state : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
        (let not_ptrs := filter (is_not_ptr state) (map_dom (snd state)) in
         if seq.nilp not_ptrs then [] else
         [liftM AId (elems_ "X0"%string not_ptrs)] ) ).

Sample (P <- arbitrary ;; 
       exp <- gen_exp_leaf_no_ptr P;; 
       ret (P, exp)).

(* This generator allows numbers, function pointers and all variables *)
Definition gen_exp_leaf (state : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;; 
         liftM FPtr arbitrary ;;; 
         (let vars := map_dom (snd state) in
          if seq.nilp vars then [] else
          [liftM AId (elems_ "X0"%string vars)] )).

(* I then define generators for expressions of a given size. Similarly,
    there are two generators: one that allows all expressions, and one which
    produces expressions without pointers. *)

Fixpoint gen_exp_no_ptr (sz : nat) (state : reg) : G exp :=
  match sz with
  | O => gen_exp_leaf_no_ptr state
  | S sz' => 
      freq [ (2, gen_exp_leaf_no_ptr state);
             (sz, liftM3 ABin arbitrary (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state));
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state))
          ]
  end.

Print binop.

Fixpoint gen_exp1 (sz : nat) (state : reg) : G exp :=
  match sz with 
  | O => gen_exp_leaf state
  | S sz' => 
          freq [ 
            (2, gen_exp_leaf state);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => liftM2 (ABin BinEq) (gen_exp1 sz' state) (gen_exp1 sz' state)
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp1 sz' state) (gen_exp1 sz' state))
          ]
  end.

(* Notice, that a "gen_exp" generator calls non-pointer "gen_exp_no_ptr" generator when branching and
  when performing a binary operation other than "BinEq" (equality is allowed on function pointers). *)

Sample (P <- arbitrary;;
        a <- gen_exp1 4 P;;
        ret (P, a)).

QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll (gen_exp1 4 state) (fun (exp : exp) =>
            implication (is_some (eval state exp)) true))).
(* "+++ Passed 10000 tests (382 discards)" *)

(* Better, but we still get discards. These cases are when the equality is generated between pointer
  and non-pointer. The following generator accounts for that: *)

Definition eitherOf {A} (a : G A) (b : G A) : G A := freq [(1, a); (1, b)].

Fixpoint gen_exp (sz : nat) (state : reg) : G exp :=
  match sz with 
  | O => gen_exp_leaf state
  | S sz' => 
          freq [ 
             (2, gen_exp_leaf state);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state))
                    (liftM2 (ABin BinEq) (liftM FPtr arbitrary) (liftM FPtr arbitrary))
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp sz' state) (gen_exp sz' state))
          ]
  end.

(* QuickChick (forAll arbitrary (fun (state : reg) => *)
(*             forAll (gen_exp 4 state) (fun (exp : exp) => *)
(*             implication (is_some (eval state exp)) true))). *)
(* "+++ Passed 10000 tests (0 discards)" *)

(* Now we generate expressions, where we only branch on numbers and identifiers evaluating to numbers,
  and a binary operation allowed for function pointers is only equality. *)

(** Wf Program Generator *)

Fixpoint _gen_partition (fuel n: nat) : G (list nat) :=
  match fuel with
  | 0 => ret [n]
  | S fuel' =>
      match n with
      | O => ret []
      | S O => ret [1]
      | S (S n') => (k <- choose(1, n - 1);;
                     rest <- _gen_partition fuel' (n - k);;
                     ret (k :: rest))
      end
  end.

Definition gen_partition (n: nat) := _gen_partition n n.

Sample (gen_partition 8).

Definition gen_vars (len: nat) : G (list string) :=
  vectorOf len arbitrary.

Sample (gen_vars 5).

Definition ex_vars : list string :=
  ["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string].

Fixpoint proc_hd (pst: list nat) : list nat :=
  match pst with
  | [] => []
  | hd :: tl => 0 :: map (fun x => x + hd) (proc_hd tl)
  end.

Compute (proc_hd [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Definition gen_exp_leaf_wf (vars: list string) (pst: list nat) : G exp :=
  oneOf [liftM ANum arbitrary ;
         liftM FPtr (elems_ 0 (proc_hd pst));
         liftM AId (elems_ "X0"%string vars)].

Fixpoint gen_exp_wf (vars: list string) (sz : nat) (pst: list nat) : G exp :=
  match sz with 
  | O => gen_exp_leaf_wf vars pst
  | S sz' => 
          freq [
             (2, gen_exp_leaf_wf vars pst);
             (sz, binop <- arbitrary;;
                  liftM2 (ABin binop) (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst));
             (sz, liftM3 ACTIf (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst))
          ]
  end.

Definition gen_asgn_wf (vars: list string) (pst: list nat) : G inst :=
  x <- elems_ "X0"%string vars;;
  a <- gen_exp_wf vars 1 pst;;
  ret <{ x := a }>.

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

Definition nat_list_minus (l1 l2 : list nat) : list nat :=
  filter (fun x => negb (existsb (Nat.eqb x) l2)) l1.

Definition gen_branch_wf (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  e <- gen_exp_wf vars 1 pst;;
  l <- elems_ 0 (nat_list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ branch e to l }>.

Sample (gen_branch_wf ex_vars 8 [3; 3; 1; 1]).

Definition gen_jump_wf (pl: nat) (pst: list nat) : G inst :=
  l <- elems_ 0 (nat_list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ jump l }>.

Sample (gen_jump_wf 8 [3; 3; 1; 1]).

Definition gen_load_wf (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  e <- gen_exp_wf vars 1 pst;;
  x <- elems_ "X0"%string vars;;
  ret <{ x <- load[e] }>.

Sample (gen_load_wf ex_vars 8 [3; 3; 1; 1]).

Definition gen_store_wf  (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  e1 <- gen_exp_wf vars 1 pst;;
  e2 <- gen_exp_wf vars 1 pst;;
  ret <{ store[e1] <- e2 }>.

Sample (gen_store_wf ex_vars 8 [3; 3; 1; 1]).

(* Definition gen_exp_leaf_ptr (pl: nat) (rs : reg) : G exp := *)
(*   oneOf (liftM FPtr (choose (0, pl));;; *)
(*          (let ptrs := filter (fun s => negb (is_not_ptr rs s)) (map_dom (snd rs)) in *)
(*           if seq.nilp ptrs then [] else *)
(*           [liftM AId (elems_ "X0"%string ptrs)] )). *)

(* Fixpoint gen_exp_ptr (sz : nat) (pl: nat) (rs : reg) : G exp := *)
(*   match sz with *)
(*   | O => gen_exp_leaf_ptr pl rs *)
(*   | S sz' => *)
(*           freq [ *)
(*              (2, gen_exp_leaf_ptr pl rs); *)
(*              (sz, liftM3 ACTIf (gen_exp_no_ptr sz' rs) (gen_exp_ptr sz' pl rs) (gen_exp_ptr sz' pl rs)) *)
(*           ] *)
(*   end. *)

(* SOONER: fix -> # of procedure is needed. *)
Definition gen_call_wf (pst: list nat) : G inst :=
  (* l <- gen_exp_wf vars pl pst;; *)
  l <- elems_ 0 (proc_hd pst);;
  ret <{ call (FPtr l) }>.

Sample (gen_call_wf [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Sample (vectorOf 1 (gen_call_wf [3; 3; 1; 1])).

Definition gen_inst (gen_asgn : list string -> list nat -> G inst)
                    (gen_branch : list string -> nat -> list nat -> G inst)
                    (gen_jump : nat -> list nat -> G inst)
                    (gen_load : list string -> nat -> list nat -> G inst)
                    (gen_store : list string -> nat -> list nat -> G inst)
                    (gen_call : list nat -> G inst)
                    (vars: list string) (sz:nat) (pl: nat) (c: list nat) : G inst :=
  freq [ (1, ret ISkip);
         (1, ret IRet);
         (sz, gen_asgn vars c);
         (sz, gen_branch vars pl c);
         (sz, gen_jump pl c);
         (sz, gen_load vars pl c);
         (sz, gen_store vars pl c);
         (sz, gen_call c)].

Definition gen_inst_wf (vars: list string) (sz pl: nat) (pst: list nat) : G inst :=
  gen_inst gen_asgn_wf gen_branch_wf gen_jump_wf
           gen_load_wf gen_store_wf gen_call_wf vars sz pl pst.

Sample (gen_inst_wf ex_vars 8 8 [3; 3; 1; 1]).

(* bsz: # of instruction in blk *)
Definition gen_blk_wf (vars: list string) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wf vars bsz pl pst).

Sample (gen_blk_wf ex_vars 8 8 [3; 3; 1; 1]).

(* fsz: # of blocks in procedure *)
(* blk length = 8 *)
Fixpoint _gen_proc_wf (vars: list string) (fsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => blk <- gen_blk_wf vars 3 pl pst;;
             rest <- _gen_proc_wf vars fsz' pl pst;;
             ret ((blk, false) :: rest)
  end.

Sample (_gen_proc_wf ex_vars 3 8 [3; 3; 1; 1]).

(* blk length = 8 *)
Definition gen_proc_wf (vars: list string) (fsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => blk <- gen_blk_wf vars 3 pl pst;;
             rest <- _gen_proc_wf vars fsz' pl pst;;
             ret ((blk, true) :: rest)
  end.

Sample (gen_proc_wf ex_vars 3 3 [3; 3; 1; 1]).

Fixpoint _gen_prog_wf (vars: list string) (pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wf vars hd pl pst;;
              tl_proc <- _gen_prog_wf vars pl pst tl;;
              ret (hd_proc ++ tl_proc)
  end.

Sample (_gen_prog_wf ex_vars 8 [3; 3; 1; 1] [3; 3; 1; 1]).

Definition gen_prog_wf_example :=
  let pl := 8%nat in
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl pst pst.

Sample (gen_prog_wf_example).

Definition gen_prog_wf_example' :=
  let pl := 8%nat in
  let pst := [3;3;1;1] in
  _gen_prog_wf ex_vars pl pst pst.

Definition test_wf_example' : G bool :=
  prog <- gen_prog_wf_example';;
  ret (wf prog).

Sample (vectorOf 1 test_wf_example').

Definition gen_prog_wf :=
  pl <- choose(1, 8);;
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl pst pst.

QuickChick (forAll (gen_prog_wf) (fun (p : prog) =>
            implication (wf p) true)).

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

QuickChick (forAll (gen_prog_wf) (fun (p : prog) =>
            implication (wf (uslh_prog p)) true)).

(* Definition find_failing_block : G (option (nat * (list inst * bool) * prog)) := *)
(*   prog <- gen_prog_wf_example;; *)
(*   let indexed_blocks := combine (seq 0 (Datatypes.length prog)) prog in *)
(*   let failing := filter (fun '(i, blk) => negb (wf_blk prog blk)) indexed_blocks in *)
(*   match failing with *)
(*   | [] => ret None *)
(*   | (i, blk) :: _ => ret (Some (i, blk, prog)) *)
(*   end. *)

(* Sample find_failing_block. *)

(** Relative Security *)

(* YH: Unlike non-interference, the relative security property is formally defined for all input pairs. It does not require input pairs to be public-equivalent.

 However, for the test to be meaningful, the premise of the property must hold.
 This means we must select input pairs for which the original program produces
 identical observations under sequential execution.

  => the taint analysis of TestingFlexSLH will be useful.
 *)

(* From SECF Require Import TestingSpecCT. *)

(* Notation label := TestingSpecCT.label. *)
(* Notation apply := ListMaps.apply. *)
(* Notation join := TestingSpecCT.join. *)

Notation label := bool.
Notation apply := ListMaps.apply.
Definition join (l1 l2 : label) : label := l1 && l2.

Definition pub_vars := total_map label.
Definition pub_arrs := list label. (* true: public, false: secret *)

(* Copied from TestingFlexSLH.v *)

(* For testing relative security we do taint tracking of sequential executions
   (as a variant of Lucie's interpreter). We use this to track which initial
   values of variables and arrays affect CT observations. *)

Definition reg_id := string.
Definition mem_addr := nat.

Definition taint : Type := list (reg_id + mem_addr).

#[export] Instance showTaint : Show (reg_id + mem_addr) :=
  {show := fun x =>
     match x with
     | inl x => show x
     | inr a => show a
     end}.

Definition sum_eqb (s1 s2 : (reg_id + mem_addr)) : bool :=
  match s1, s2 with
  | inl x1, inl x2 => String.eqb x1 x2
  | inr x1, inr x2 => Nat.eqb x1 x2
  | _, _ => false
  end.

Definition join_taints t1 t2 := remove_dupes sum_eqb (t1 ++ t2).

Module TaintTracking.

Definition tcptr := taint.
Definition treg := total_map taint.
Definition tmem := list taint.
Definition tstk := list tcptr.

Definition tcfg := (tcptr * treg * tmem * tstk)%type.
Definition input_st : Type := cfg * tcfg * taint.

Variant output_st (A : Type) : Type :=
  | RStep : A -> obs -> input_st -> output_st A
  | RError : obs -> input_st -> output_st A
  | RTerm : obs -> input_st -> output_st A.

Record evaluator (A : Type) : Type := mkEvaluator
  { evaluate : input_st -> output_st A }.

(* An 'evaluator A'. This is the monad.
   It transforms an input state into an output state, returning an A. *)
(* An interpreter is a special kind of evaluator *)
Definition interpreter: Type := evaluator unit.

(* Generic monad operators *)
#[export] Instance monadEvaluator: Monad evaluator :=
  { ret := fun A value => mkEvaluator A (fun (ist : input_st) => RStep A value [] ist);
    bind := fun A B e f =>
      mkEvaluator B (fun (ist : input_st) =>
        match evaluate A e ist with
        | RStep _ value os1 ist'  =>
            match evaluate B (f value) ist' with
            | RStep _ value os2 ist'' => RStep B value (os1 ++ os2) ist''
            | RError _ os2 ist'' => RError B (os1 ++ os2) ist''
            | RTerm _ os2 ist'' => RTerm B (os1 ++ os2) ist''
            end
        | RError _ os ist' => RError B os ist'
        | RTerm _ os ist' => RTerm B os ist'
        end
      )
  }.

(* Definition get_id_val (name : string): evaluator val := *)
(*   mkEvaluator _ (fun (ist : input_st) => *)
(*     let '(c, _, _) := ist in *)
(*     let '(_, regs, _, _) := c in *)
(*     evaluate _ (ret (apply regs name)) ist *)
(*     ). *)

(* Definition get_mem_val (n : nat): evaluator val := *)
(*   mkEvaluator _ (fun (ist : input_st) => *)
(*     let '(c, _, _) := ist in *)
(*     let '(_, _, m, _) := c in *)
(*     v <- nth_error m n;; *)
(*     evaluate _ (ret v) ist *)
(*   ). *)

Fixpoint _calc_taint_exp (e: exp) (treg: total_map taint) : taint :=
  match e with
  | ANum _ | FPtr _ => []
  | AId x => apply treg x
  | ABin _ e1 e2 => join_taints (_calc_taint_exp e1 treg) (_calc_taint_exp e2 treg)
  | ACTIf e1 e2 e3 => join_taints (_calc_taint_exp e1 treg)
                                 (join_taints (_calc_taint_exp e2 treg) (_calc_taint_exp e3 treg))
  end.

Variant taint_ctx :=
| CMem (n: nat)
| CDefault.

(* None cases are unreachable. *)
Definition taint_step (i: inst) (c: cfg) (tc: tcfg) (tobs: taint) (tctx: taint_ctx) : option (tcfg * taint) :=
  let '(pc, rs, m, s) := c in
  let '(tpc, trs, tm, ts) := tc in
  match i with
  | <{ skip }> | <{ ctarget }> | <{ jump _ }> =>
      match tctx with
      | CDefault => Some (tc, tobs)
      | _ => None
      end
  | <{ x := e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tx := join_taints te tpc in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          Some (tc', tobs)
      | _ => None
      end
  | <{ branch e to l }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts) in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end
  | <{ x <- load[e] }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let tv := nth n tm [] in (* default case is unreachable: step already checked. *)
          let tx := (join_taints (join_taints te tv) tpc) in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          let tobs' := (join_taints (join_taints te tpc) tobs) in
          Some (tc', tobs')
      | _ => None
      end
  | <{ store[e] <- e' }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let te' := (_calc_taint_exp e' trs) in
          let tm_val := join_taints (join_taints te te') tpc in
          let tc' := (tpc, trs, upd n tm tm_val, ts) in
          let tobs' := join_taints (join_taints te tpc) tobs in
          Some (tc', tobs')
      | _ => None
      end
  | <{ call e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let ts' := tpc :: ts in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts') in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end
  | <{ ret }> =>
      match tctx with
      | CDefault =>
          let tpc' := hd [] ts in (* default case is unreachable: step already checked. *)
          let ts' := tl ts in
          let tc' := (tpc', trs, tm, ts') in
          Some (tc', tobs)
      | _ => None
      end
  end.

Definition get_ctx (rs: reg) (i: inst) : option taint_ctx  :=
  match i with
  | <{ x <- load[e] }> =>  v <- eval rs e;;
                         n <- to_nat v;;
                         Some (CMem n)
  | <{ store[e] <- e' }> => v <- (eval rs e);;
                          n <- to_nat v;;
                          Some (CMem n)
  | _ => Some CDefault
  end.

Definition final_cfg (p: prog) (pc: cptr) : bool :=
  match fetch p (inc pc) with
  | Some _ => false
  | None => true
  end.

Definition step_taint_track (p: prog) : evaluator unit :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(c, tc, tobs) := ist in
    let '(pc, rs, m, s) := c in
    let '(tpc, trs, tm, ts) := tc in
    match step p c with
    | Some (c', os) =>
        match (fetch p pc) with
        | Some i => match get_ctx rs i with
                   | Some tctx => match taint_step i c tc tobs tctx with
                                 | Some (tc', tobs') => RStep _ tt os (c', tc', tobs')
                                 | _ => RError _ [] ist (* context is inconsistent. *)
                                 end
                   | _ => RError _ [] ist
                   end
        | _ => RError _ [] ist
        end
    | None => if final_cfg p pc
             then RTerm _ [] ist
             else RError _ [] ist
    end
    ).

Variant exec_result : Type :=
  | ETerm (st: input_st) (os: obs)
  | EError (st: input_st) (os: obs)
  | EOutOfFuel (st: input_st) (os: obs).

Fixpoint steps_taint_track (f: nat) (p: prog) (ist: input_st) (os: obs) : exec_result :=
  match f with
  | O => EOutOfFuel ist os
  | S f' =>
      match evaluate unit (step_taint_track p) ist with
      | RTerm _ os' ist' => ETerm ist' (os ++ os')
      | RError _ os' ist' => EError ist' (os ++ os')
      | RStep _ _ os' ist' => steps_taint_track f' p ist' (os ++ os')
      end
  end.

Fixpoint _init_taint_mem (m: mem) (n: nat) : tmem :=
  match m with
  | [] => []
  | h :: m' => ([inr n]) :: _init_taint_mem m' (S n)
  end.

Definition init_taint_mem (m: mem) : tmem :=
  _init_taint_mem m 0.

End TaintTracking.

Fixpoint split_sum_list {A B : Type} (l : list (A + B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | inl a :: xs => let (la, lb) := split_sum_list xs in (a :: la, lb)
  | inr b :: xs => let (la, lb) := split_sum_list xs in (la, b :: lb)
  end.

Definition taint_tracking (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := TaintTracking.init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (TaintTracking.steps_taint_track f p ist []) with
  | TaintTracking.ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.


(** Better wf program generator *)
(* 1. public/secret
   2. ptr/not ptr
   3. wf          *)

Definition gen_exp_leaf_wf (pl: nat) (state : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
         liftM FPtr (choose (0, pl));;;
         (let vars := map_dom (snd state) in
          if seq.nilp vars then [] else
          [liftM AId (elems_ "X0"%string vars)] )).

Fixpoint gen_exp_wf (sz : nat) (pl: nat) (state : reg) : G exp :=
  match sz with
  | O => gen_exp_leaf_wf pl state
  | S sz' =>
          freq [
             (2, gen_exp_leaf_wf pl state);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state))
                    (liftM2 (ABin BinEq) (liftM FPtr (choose (0, pl))) (liftM FPtr (choose (0, pl))))
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp_wf sz' pl state) (gen_exp_wf sz' pl state))
          ]
  end.

(* YH: 8 sec in my machine *)
(* QuickChick (forAll arbitrary (fun (state : reg) => *)
(*             forAll (gen_exp_wf 4 4 state) (fun (exp : exp) => *)
(*             implication (is_some (eval state exp)) true))). *)


(* Instruction Generator *)

(* forAll e st, is_some (step p cfg) ==> True *)

Definition gen_asgn_wf (pl: nat) (rs: reg) : G inst :=
  let vars := map_dom (snd rs) in
  x <- elems_ "X0"%string vars;;
  a <- gen_exp_wf 1 pl rs;;
  ret <{ x := a }>.

Definition gen_branch_wf (pl: nat) (rs: reg) : G inst :=
  e <- gen_exp_no_ptr 1 rs;;
  l <- choose (0, pl);;
  ret <{ branch e to l }>.

Definition gen_jump_wf (pl: nat) : G inst :=
  l <- choose (0, pl);;
  ret <{ jump l }>.

(* memory length? *)
Definition gen_load_wf (pl: nat) (rs: reg) : G inst :=
  let vars := map_dom (snd rs) in
  e <- gen_exp_no_ptr 1 rs;;
  x <- elems_ "X0"%string vars;;
  ret <{ x <- load[e] }>.

(* memory length? *)
Definition gen_store_wf (pl: nat) (rs: reg) : G inst :=
  e1 <- gen_exp_no_ptr 1 rs;;
  e2 <- gen_exp_wf 1 pl rs;;
  ret <{ store[e1] <- e2 }>.

Definition gen_exp_leaf_ptr (pl: nat) (rs : reg) : G exp :=
  oneOf (liftM FPtr (choose (0, pl));;;
         (let ptrs := filter (fun s => negb (is_not_ptr rs s)) (map_dom (snd rs)) in
          if seq.nilp ptrs then [] else
          [liftM AId (elems_ "X0"%string ptrs)] )).

Fixpoint gen_exp_ptr (sz : nat) (pl: nat) (rs : reg) : G exp :=
  match sz with
  | O => gen_exp_leaf_ptr pl rs
  | S sz' =>
          freq [
             (2, gen_exp_leaf_ptr pl rs);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' rs) (gen_exp_ptr sz' pl rs) (gen_exp_ptr sz' pl rs))
          ]
  end.

(* SOONER: fix -> # of procedure is needed. *)
Definition gen_call_wf (pl: nat) (rs: reg) : G inst :=
  l <- gen_exp_ptr 2 pl rs;;
  ret <{ call l }>.

Definition gen_inst (gen_asgn : nat -> reg -> G inst)
                    (gen_branch : nat -> reg -> G inst)
                    (gen_jump : nat -> G inst)
                    (gen_load : nat -> reg -> G inst)
                    (gen_store : nat -> reg -> G inst)
                    (gen_call : nat -> reg -> G inst)
                    (sz:nat) (pl: nat) (c: reg) : G inst :=
  freq [ (1, ret ISkip);
         (1, ret IRet);
         (sz, gen_asgn pl c);
         (sz, gen_branch pl c);
         (sz, gen_jump pl);
         (sz, gen_load pl c);
         (sz, gen_store pl c);
         (sz, gen_call pl c)].

Definition gen_inst_wf (sz pl: nat) (rs: reg) : G inst :=
  gen_inst gen_asgn_wf gen_branch_wf gen_jump_wf
           gen_load_wf gen_store_wf gen_call_wf sz pl rs.

(* bsz: # of instruction in blk *)
Definition gen_blk_wf (bsz pl: nat) (rs: reg) : G (list inst) :=
  vectorOf bsz (gen_inst_wf bsz pl rs).

(* fsz: # of blocks in procedure *)
Fixpoint _gen_proc_wf (fsz pl: nat) (rs: reg) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => blk <- gen_blk_wf 8 pl rs;;
             rest <- _gen_proc_wf fsz' pl rs;;
             ret ((blk, false) :: rest)
  end.

Definition gen_proc_wf (fsz pl: nat) (rs: reg) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => blk <- gen_blk_wf 8 pl rs;;
             rest <- _gen_proc_wf fsz' pl rs;;
             ret ((blk, true) :: rest)
  end.

Fixpoint _gen_partition (fuel n: nat) : G (list nat) :=
  match fuel with
  | 0 => ret [n]
  | S fuel' =>
      match n with
      | O => ret []
      | S O => ret [1]
      | S (S n') => (k <- choose(1, n - 1);;
                     rest <- _gen_partition fuel' (n - k);;
                     ret (k :: rest))
      end
  end.

Definition gen_partition (n: nat) := _gen_partition n n.

(* Sample (gen_partition 8). *)

Definition gen_val_bounded (pl: nat) (sz: nat) : G val :=
  match sz with
  | O => oneOf [liftM N arbitrary ; liftM FP (choose (0, pl))]
  | S sz' =>
      freq [ (sz, liftM N arbitrary);
             (1, liftM FP (choose (0, pl)))]
  end.

(* register set *)
Definition gen_total_map_bounded (pl: nat) : G (total_map val) :=
  (d <- arbitrary;;
   v0 <- gen_val_bounded pl 4;;
   v1 <- gen_val_bounded pl 4;;
   v2 <- gen_val_bounded pl 4;;
   v3 <- gen_val_bounded pl 4;;
   v4 <- gen_val_bounded pl 4;;
   v5 <- gen_val_bounded pl 4;;
   ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
           ("X3",v3); ("X4",v4); ("X5",v5)])%string).

(* Sample (rs <- gen_total_map_bounded 8;; *)
(*         i <- gen_inst_wf 8 8 rs;;  *)
(*         ret (rs, i)). *)

Fixpoint _gen_prog_wf (pl: nat) (pst: list nat) (rs: reg) : G (list (list inst * bool)) :=
  match pst with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wf hd pl rs;;
              tl_proc <- _gen_prog_wf pl tl rs;;
              ret (hd_proc ++ tl_proc)
  end.

Definition gen_prog_wf :=
  pl <- choose(1, 10);;
  pst <- gen_partition pl;;
  rs <- gen_total_map_bounded pl;;
  _gen_prog_wf pl pst rs.
