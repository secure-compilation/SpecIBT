From Coq Require Import Strings.String.
From SECF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. (* Import Nat. *)
From Coq Require Import Lia.
From SECF Require Export Imp.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String. 

Definition Map A := list (string * A).

Fixpoint map_get {A} (m : Map A) x : option A :=
  match m with
  | [] => None
  | (k, v) :: m' => if x = k ? then Some v else map_get m' x
  end.

Definition map_set {A} (m:Map A) (x:string) (v:A) : Map A := (x, v) :: m.

Definition total_map (X:Type) : Type := X * Map X.

Definition apply {A:Type} (m : total_map A) (x:string) : A := 
  match m with
  | (d, lm) => match map_get lm x with
               | Some v => v
               | None => d
               end
  end.

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  match m with
  | (d, lm) => (d, map_set lm x v)
  end.

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Definition pub_vars := total_map bool.

Definition join_noalias (l1 l2 : bool) : bool := l1 && l2.

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P '|-a-' a \IN l" (at level 40).
(* TERSE: /HIDEFROMHTML *)

Inductive aexp_has_label (P:pub_vars) : aexp -> bool -> Prop :=
  | T_Num : forall n,
       P |-a- (ANum n) \IN true
  | T_Id : forall x,
       P |-a- (AId x) \IN (apply P x)
  | T_Plus : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 + a2 }> \IN (join_noalias l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 - a2 }> \IN (join_noalias l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 * a2 }> \IN (join_noalias l1 l2)

where "P '|-a-' a '\IN' l" := (aexp_has_label P a l).

#[export] Instance genId : Gen string :=
  {arbitrary := (n <- freq [(10, ret 0);
                             (9, ret 1);
                             (8, ret 2);
                             (4, ret 3);
                             (2, ret 4);
                             (1, ret 5)];;
                 ret ("X" ++ show n)%string) }.

Derive ArbitrarySizedSuchThat for (fun a => aexp_has_label P a l).
Check GenSizedSuchThataexp_has_label :
    forall (P:pub_vars) (l:bool),
      GenSizedSuchThat aexp (fun a:aexp => P |-a- a \IN l).

Derive ArbitrarySizedSuchThat for (fun l => aexp_has_label P a l).
Check GenSizedSuchThataexp_has_label0 :
    forall (P:pub_vars) (a:aexp),
      GenSizedSuchThat bool (fun l:bool => P |-a- a \IN l).

Derive DecOpt for (aexp_has_label P a l).
Check DecOptaexp_has_label :
    forall (P:pub_vars) (a:aexp) (l:bool),
      DecOpt (P |-a- a \IN l).

Definition join (l1 l2 : bool) : bool := l1 && l2.

Reserved Notation "P '|-b-' b \IN l" (at level 40).

Inductive bexp_has_label (P:pub_vars) : bexp -> bool -> Prop :=
  | T_True :
       P |-b- <{ true }> \IN true
  | T_False :
       P |-b- <{ false }> \IN true
  | T_Eq : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 = a2 }> \IN (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 <> a2 }> \IN (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 <= a2 }> \IN (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 > a2 }> \IN (join l1 l2)
  | T_Not : forall b l,
       P |-b- b \IN l ->
       P |-b- <{ ~b }> \IN l
  | T_And : forall b1 l1 b2 l2,
       P |-b- b1 \IN l1 ->
       P |-b- b2 \IN l2 ->
       P |-b- <{ b1 && b2 }> \IN (join l1 l2)

where "P '|-b-' b '\IN' l" := (bexp_has_label P b l).

Derive ArbitrarySizedSuchThat for (fun b => bexp_has_label P b l).
Check GenSizedSuchThatbexp_has_label :
    forall (P:pub_vars) (l:bool),
      GenSizedSuchThat bexp (fun b:bexp => P |-b- b \IN l).

Derive ArbitrarySizedSuchThat for (fun l => bexp_has_label P b l).
Check GenSizedSuchThatbexp_has_label0 :
    forall (P:pub_vars) (b:bexp),
      GenSizedSuchThat bool (fun l:bool => P |-b- b \IN l).

Derive DecOpt for (bexp_has_label P b l).
Check DecOptaexp_has_label :
    forall (P:pub_vars) (a:aexp) (l:bool),
      DecOpt (P |-a- a \IN l).

Definition can_flow (l1 l2 : bool) : bool := l1 || negb l2.

Reserved Notation "P '|-pc-' c" (at level 40).

Inductive pc_well_typed (P:pub_vars) : com -> Prop :=
  | PCWT_Com :
      P |-pc- <{ skip }>
  | PCWT_Asgn : forall x a l,
      P |-a- a \IN l ->
      can_flow l (apply P x) = true ->
      P |-pc- <{ x := a }>
  | PCWT_Seq : forall c1 c2,
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ c1 ; c2 }>
  | PCWT_If : forall b c1 c2,
      P |-b- b \IN true ->
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ if b then c1 else c2 end }>
  | PCWT_While : forall b c1,
      P |-b- b \IN true ->
      P |-pc- c1 ->
      P |-pc- <{ while b do c1 end }>

where "P '|-pc-' c" := (pc_well_typed P c).

Derive DecOpt for (pc_well_typed P c).
Check DecOptpc_well_typed :
  forall (P:pub_vars) (c:com), DecOpt (P |-pc- c).

Derive ArbitrarySizedSuchThat for (fun c => pc_well_typed P c).
(* Using notation above causes: *)
(* Error: Anomaly "File "plugin/depDriver.ml",
   line 265, characters 6-11: Pattern matching failed." *)
Check GenSizedSuchThatpc_well_typed :
  forall P:pub_vars, GenSizedSuchThat com (fun c => P |-pc- c).

Reserved Notation "P ',,' pc '|--' c" (at level 40).

Inductive well_typed (P:pub_vars) : bool -> com -> Prop :=
  | WT_Com : forall pc,
      P ,, pc |-- <{ skip }>
  | WT_Asgn : forall pc x a l,
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P x) = true ->
      P ,, pc |-- <{ x := a }>
  | WT_Seq : forall pc c1 c2,
      P ,, pc |-- c1 ->
      P ,, pc |-- c2 ->
      P ,, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P ,, (join pc l) |-- c1 ->
      P ,, (join pc l) |-- c2 ->
      P ,, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \IN l ->
      P ,, (join pc l) |-- c1 ->
      P ,, pc |-- <{ while b do c1 end }>

where "P ',,' pc '|--' c" := (well_typed P pc c).

Derive DecOpt for (well_typed P pc c).
Check DecOptwell_typed :
  forall (P:pub_vars) (pc:bool) (c:com), DecOpt (P ,, pc |-- c).

Derive ArbitrarySizedSuchThat for (fun c => well_typed P pc c).
(* Using notation above causes: *)
(* Error: Anomaly "File "plugin/depDriver.ml",
   line 265, characters 6-11: Pattern matching failed." *)
Check GenSizedSuchThatwell_typed :
  forall (P:pub_vars) (pc:bool), GenSizedSuchThat com (fun c => P,, pc |-- c).

QuickChickDebug Debug On.

Definition state := total_map nat.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => apply st x (* <--- NEW: apply is now needed here *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Derive ArbitrarySizedSuchThat for (fun s2 => ceval c s1 s2).
Check GenSizedSuchThatceval :
  forall c s1, GenSizedSuchThat state (fun s2 => ceval c s1 s2).

Sample ((GenSizedSuchThatceval <{skip}> (0, [])).(arbitrarySizeST) 2).
