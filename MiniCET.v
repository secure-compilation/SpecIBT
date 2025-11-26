(** * Define MiniCET *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From Stdlib Require Import String.

From SECF Require Import Utils.
From SECF Require Import MapsFunctor.
Require Import Stdlib.Classes.EquivDec.

Declare Custom Entry com.
Declare Scope com_scope.

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

(* Inductive val : Type := *)
(*   | N (n:nat) *)
(*   | FP (l:nat). (* <- NEW: function pointer to procedure at label [l] *) *)

(** Since type mismatches are now possible, evaluation of expressions can now
    fail, so the [eval] function is in the option monad. *)

Definition to_nat (v:val) : option nat :=
  match v with
  | N n => Some n
  | _ => None
  end.

Definition to_fp (v:val) : option nat :=
  match v with
  | FP l => Some l
  | _ => None
  end.

Definition eval_binop (o:binop) (v1 v2 : val) : val :=
  match v1, v2 with
  | N n1, N n2 => N (eval_binop_nat o n1 n2)
  | FP l1, FP l2 =>
      match o with
      | BinEq => N (bool_to_nat (l1 =? l2))
      | _ => UV (* Function pointers can only be tested for equality *)
      end
  | _, _ => UV (* Type error; treating UV as a 3rd type; reasonable?
                  - alternative: make && and || short-circuiting *)
  end.

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

Inductive observation : Type :=
  | OBranch (b:bool)
  | OLoad (n:nat)
  | OStore (n:nat)
  | OCall (l: nat).

Definition obs := list observation.

Definition observation_eqb (os1 : observation) (os2 : observation) : bool :=
  match os1, os2 with
  | OBranch b, OBranch b' => Bool.eqb b b'
  | OLoad i, OLoad i' => (i =? i')
  | OStore i, OStore i' => (i =? i')
  | OCall v, OCall v' => (v =? v')
  | _, _ => false
  end.

Definition obs_eqb (o1 : obs) (o2 : obs) : bool :=
  forallb (fun '(os1, os2) => observation_eqb os1 os2) (List.combine o1 o2).

Definition fetch (p:prog) (pc:cptr) : option inst :=
  let '(l,o) := pc in
  r <- nth_error p l;;
  nth_error (fst r) o.

Notation "p '[[' pc ']]'" := (fetch p pc).

Definition inc (pc:cptr) : cptr :=
  let '(l,o) := pc in (l,o+1).

Notation "pc '+' '1'" := (inc pc).

Inductive direction : Type :=
  | DBranch (b':bool)
  | DCall (lo:cptr).

Definition dirs := list direction.

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

(* Writer monad *)
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

(* No mapM in ExtLib, seems it got removed: https://github.com/rocq-community/Stdlib-ext-lib/commit/ef2e35f43b2d1db4cb64188e9521948fdd1e0527 *)
(* YH: We can use mapGen from QuickChick library instead.  *)
Definition mapM {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  sequence (List.map f l).

Fixpoint foldM {A B: Type} (f : B -> A -> M B) (acc : B) (l: list A) : M B :=
  match l with
  | nil => ret acc
  | hd :: tl => el <- f acc hd;; foldM f el tl
  end.

Fixpoint fold_rightM {A B : Type} (f : A -> B -> M B) (l : list A) (init : B) : M B :=
  match l with
  | [] => ret init
  | hd :: tl => r <- fold_rightM f tl init;; f hd r
  end.

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
  let e' := <{ (msf=1) ? 0 : e }> in (* if misspeculating always leak False *)
      l' <- add_block_M <{{ i[(msf := ((~e') ? 1 : msf)); jump l] }}>;;
      ret <{{ i[branch e' to l'; (msf := (e' ? 1 : msf))] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &0 : e }> in
      ret <{{ i[callee:=e'; call e'] }}>
  | _ => ret [i]
  end.

Definition uslh_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  bl' <- concatM (mapM uslh_inst bl);;
  if is_proc then
    ret (<{{ i[ctarget; msf := (callee = &l) ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition uslh_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM uslh_blk idx_p (Datatypes.length p) in
  (p' ++ newp).

Fixpoint group_by_proc_impl (p: prog) (current_proc_acc: prog) : list prog :=
  match p with
  | [] => match current_proc_acc with
         | [] => []
         | _ => [rev current_proc_acc]
         end
  | (blk, is_proc) :: tl =>
      if is_proc then
        match current_proc_acc with
        | [] => group_by_proc_impl tl [(blk, is_proc)]
        | _ => (rev current_proc_acc) :: group_by_proc_impl tl [(blk, is_proc)]
        end
      else group_by_proc_impl tl ((blk, is_proc) :: current_proc_acc)
  end.

Definition group_by_proc (p: prog) : list prog :=
  group_by_proc_impl p [].

Definition sample_prog_for_grouping : prog := [
  (nil, true);  (* Proc 1, Blk 0 *)
  (nil, false); (* Proc 1, Blk 1 *)
  (nil, false); (* Proc 1, Blk 2 *)
  (nil, true);  (* Proc 2, Blk 3 *)
  (nil, false); (* Proc 2, Blk 4 *)
  (nil, true)   (* Proc 3, Blk 5 *)
].

Compute (group_by_proc sample_prog_for_grouping).

Compute (Datatypes.length (group_by_proc sample_prog_for_grouping)).

Definition proc_map := (fun (x: prog) => Datatypes.length x).

Definition pst_calc (p: prog) : list nat := (map proc_map (group_by_proc p)).

Compute (pst_calc sample_prog_for_grouping).

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

(* Additional wf definitions *)

Definition nonempty_block (blk: list inst * bool) : bool :=
  negb (seq.nilp (fst blk)).

Definition nonempty_block_prog (p: prog) : bool :=
  forallb nonempty_block p.

Definition block_terminator (blk: list inst * bool) : bool :=
  match (rev (fst blk)) with
  | [] => true (* unreachable *)
  | ihd::itl =>
      match ihd with
      | IRet | IJump _ => true
      | _ => false
      end
  end.

Definition block_terminator_prog (p: prog) : bool :=
  forallb block_terminator p.

Definition wf_direction (pc: cptr) (p: prog) (d: direction) : bool :=
  match d, p[[pc]] with
  | DBranch b, Some (IBranch e l) => is_some p[[(l, 0)]]
  (* We can ignore the fall-through case. See no_branch_end_prog *)
  | DCall pc', Some (ICall e) => is_some p[[pc']]
  | _, _ =>  false
  end.

Definition wf_dirs (pc: cptr) (p: prog) (ds: dirs) : bool :=
  forallb (wf_direction pc p) ds.

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

(* May (not) need separate check for no ctarget, only for source *)

(* Some Auxiliary functions *)

Definition nonempty_mem (m : mem) :Prop := (0 < Datatypes.length m)%nat.

Fixpoint e_unused (x:string) (e:exp) : Prop :=
  match e with
  | ANum n      => True
  | AId y       => y <> x
  | FPtr _      => True
  | ACTIf e1 e2 e3 => e_unused x e1 /\ e_unused x e2 /\ e_unused x e3
  | ABin _ e1 e2 => e_unused x e1 /\ e_unused x e2
  end.

Fixpoint i_unused (x:string) (i:inst) : Prop :=
  match i with
  | <{{skip}}> | <{{jump _}}> | <{{ret}}> | <{{ctarget}}> => True
  | <{{y := e}}> => y <> x /\ e_unused x e
  | <{{branch e to l}}> => e_unused x e
  | <{{y <- load[i]}}> => y <> x /\ e_unused x i
  | <{{store[i] <- e}}> => e_unused x i /\ e_unused x e
  | <{{call e}}> => e_unused x e
  end.

Definition b_unused (x: string) (blk: list inst) : Prop :=
  Forall (fun i => i_unused x i) blk.

Definition unused_prog (x: string) (p:prog) : Prop :=
  let '(bs, cts) := split p in
  Forall (fun b => b_unused x b) bs.

Definition no_ct_inst (i: inst) : Prop :=
  match i with
  | <{{ctarget}}> => False
  | _ => True
  end.

Definition no_ct_blk (blk: list inst) : Prop :=
  Forall no_ct_inst blk.

Definition no_ct_prog (p:prog) : Prop :=
  let '(bs, cts) := split p in
  Forall no_ct_blk bs.

Inductive state A : Type :=
  | S_Running (a: A)
  | S_Undef
  | S_Fault
  | S_Term.
Arguments S_Running {A} a.
Arguments S_Undef {A}.
Arguments S_Fault {A}.
Arguments S_Term {A}.

Instance state_Monad : Monad state.
Proof.
  constructor.
  - intros T t.
    now apply S_Running.
  - intros T U st f.
    destruct st eqn: H.
    + now apply f.
    + apply S_Undef.
    + apply S_Fault.
    + apply S_Term.
Defined.

Module MiniCETCommon (M: TMap).

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

Definition reg := M.t val.

Fixpoint eval (st : reg) (e: exp) : val :=
  match e with
  | ANum n => N n
  | AId x => M.t_apply st x
  | ABin b e1 e2 => eval_binop b (eval st e1) (eval st e2)
  | <{b ? e1 : e2}> =>
      match to_nat (eval st b) with (* Can't branch on function pointers *)
      | Some n1 => if not_zero n1 then eval st e1 else eval st e2
      | None => UV
      end
  | <{&l}> => FP l
  end.


Definition cfg : Type := ((cptr*reg)*mem)*list cptr. (* (pc, register set, memory, stack frame) *)

Definition spec_cfg : Type := ((cfg * bool) * bool).

(* ret with empty stackframe *)
Definition final_spec_cfg (p: prog) (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in
  let '(pc, rs, m, stk) := c in
  match fetch p pc with
  | Some i => match i with
             | IRet => if seq.nilp stk then true else false (* Normal Termination *)
             | ICTarget => if ct
                          then false (* Call target block: Unreachable *)
                          else true (* TODO: Do we need to distinguish fault and normal termination? *)
             | _ => false
             end
  | None => false
  end.

End MiniCETCommon.

Module MiniCETTest1.

Module MCC := MiniCETCommon(ListTotalMap).
Import MCC.

Definition step (p:prog) (c:cfg) : option (cfg * obs) :=
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{skip}}> | <{{ctarget}}> =>
      ret ((pc+1, r, m, sk), [])
  | <{{x:=e}}> =>
      ret ((pc+1, (x !-> eval r e; r), m, sk), [])
  | <{{branch e to l}}> =>
      n <- to_nat (eval r e);;
      let b := not_zero n in
      ret ((if b then (l,0) else pc+1, r, m, sk), [OBranch b])
  | <{{jump l}}> =>
      ret (((l,0), r, m, sk), [])
  | <{{x<-load[e]}}> =>
      n <- to_nat (eval r e);;
      v' <- nth_error m n;;
      ret ((pc+1, (x !-> v'; r), m, sk), [OLoad n])
  | <{{store[e]<-e'}}> =>
      n <- to_nat (eval r e);;
      ret ((pc+1, r, upd n m (eval r e'), sk), [OStore n])
  | <{{call e}}> =>
      l <- to_fp (eval r e);;
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

(** Speculative semantics *)

Definition spec_step (p:prog) (sc:spec_cfg) (ds:dirs) : option (spec_cfg * dirs * obs) :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{branch e to l}}> =>
      is_false ct;;
      if seq.nilp ds then
        trace "Branch: Directions are empty!" None
      else
      d <- hd_error ds;;
      b' <- is_dbranch d;;
      n <- to_nat (eval r e);;
      let b := not_zero n in
      let ms' := ms || negb (Bool.eqb b b') in
      let pc' := if b' then (l, 0) else (pc+1) in
      ret ((((pc', r, m, sk), ct, ms'), tl ds), [OBranch b])
  | <{{call e}}> =>
      is_false ct;;
      if seq.nilp ds then
        trace "Call: Directions are empty!" None
      else
      d <- hd_error ds;;
      pc' <- is_dcall d;;
      l <- to_fp (eval r e);;
      let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in
      ret ((((pc', r, m, (pc+1)::sk), true, ms'), tl ds), [OCall l])
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
      ret (c, ds, []) (* JB: executing for 0 steps should be just the identity... *)
      (* None *) (* Q: Do we need more precise out-of-fuel error here? *)
  end.

(* YH: What do you think about moving the writer monad-related code to Util.v *)

End MiniCETTest1.
