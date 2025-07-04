(** * SpecCT: Speculative Constant-Time *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Cryptographic constant-time *)

(** Cryptographic constant-time (CCT) is a software countermeasure
    against cache-based timing attacks, a class of side-channel
    attacks that exploit the latency between cache hits and cache
    misses to retrieve cryptographic keys and other secrets. In
    addition to ensuring program counter security, CCT requires
    programmers to not perform memory accesses depending on secrets.

    To model this we will make the Imp language more realistic by adding arrays.
    We need such an extension, since otherwise variable accesses in the
    original Imp map to memory operations at constant locations, which
    thus cannot depend on secrets, so CCT trivially holds for all
    programs in Imp. Array indices on the other hand are computed at
    runtime, which leads to accessing memory addresses that can depend
    on secrets, making CCT non-trivial for Imp with arrays.

    For instance, here is a simple program that is pc secure (since it does no
    branches), but not constant-time secure (since it's accesses memory based on
    secret information):
[[
   x <- a[secret]
]]
*)

(** ** Constant-time conditional *)

(** But first, we extend the arithmetic expressions of Imp with an [b ? e1 : e2]
    conditional that executes in constant time (for instance using a special
    constant-time conditional move instruction). This constant-time conditional
    will be used in one of our countermeasures below, but it complicates things
    a bit, since it makes arithmetic and boolean expressions mutually inductive. *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ACTIf (b:bexp) (a1 a2:aexp) (* <--- NEW *)
with bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Scheme aexp_bexp_ind := Induction for aexp Sort Prop
with bexp_aexp_ind := Induction for bexp Sort Prop.
Combined Scheme aexp_bexp_mutind from aexp_bexp_ind,bexp_aexp_ind.

(* SOONER: Looking at Jonathan Baumann's BSc thesis, I got a new idea about how
   to do expressions without introducing mutual inductives: could just drop the
   bools and make everything work on integers like in C (where nonzero means
   true). Moreover, could also refactor the semantics at least for binary
   operators to just one ABinOp parameterized constructor, so that there is less
   duplication in proofs / less need for automation. And BNot can just be
   encoded in terms of ACTIf or better in terms of ABinOp. We should, however,
   avoid bitwise operations since we are working with nats. We can just add
   BImpl for boolean implication. Like this: *)
(* HIDE *)
Module MergedExps.
(* A small set of binary operators *)
Inductive binop : Type :=
  | BinPlus
  | BinMinus
  | BinMult
  | BinEq
  | BinLe
  | BinAnd
  | BinImpl.

(* We define their semantics directly on nats. For boolean operators we are
   careful to allow other representations of true (any non-zero number).  *)
Definition eval_binop (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => if n1 =? n2 then 1 else 0
  | BinLe => if n1 <=? n2 then 1 else 0
  | BinAnd => if (n1 =? 0) || (n2 =? 0) then 0 else 1
  | BinImpl => if negb (n1 =? 0) && (n2 =? 0) then 0 else 1
  end.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o:binop) (a1 a2 : aexp) (* <--- REFACTORED *)
  | ACTIf (b:aexp) (a1 a2:aexp). (* <--- NEW *)

(* We can recover all the previous operations: *)
Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr a1 a2 := BImpl (BNot a1) a2.
Definition BEq := ABin BinEq.
Definition BNeq a1 a2 := BNot (BEq a1 a2).
Definition BLe := ABin BinLe.
Definition BGt a1 a2 := BNot (BLe a1 a2).
End MergedExps.
(* /HIDE *)

(** ** Typing Constant-time Conditionals *)

(** Typing of arithmetic and boolean expressions will also become
    mutually inductive. *)

(** [[[
        P|-b- be \in l   P |-a- a1 \in l1    P |-a- a2 \in l2
        ----------------------------------------------------- (T_CTIf)
                 P |-a- be?a1:a2 \in join l (join l1 l2)
]]]
*)

(* TERSE: HIDEFROMHTML *)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition A : string := "A".
Definition AP : string := "AP".
Definition AS : string := "AS".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

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
Notation "be '?' a1 ':' a2"  := (ACTIf be a1 a2)
                 (in custom com at level 20, no associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.
(* TERSE: /HIDEFROMHTML *)

(** ** Now back to adding arrays *)

Inductive com : Type :=
  | Skip
  | Asgn (x : string) (e : aexp)
  | Seq (c1 c2 : com)
  | If (be : bexp) (c1 c2 : com)
  | While (be : bexp) (c : com)
  | ARead (x : string) (a : string) (i : aexp) (* <--- NEW *)
  | AWrite (a : string) (i : aexp) (e : aexp)  (* <--- NEW *)
  | Call (p:aexp). (* <--- NEW *)

(* HIDE: CH: Originally wanted to take a:aexp and compute the accessed array,
   but our maps only have string keys, so had to settle with a:string for
   now. Seems this still completely okay in retrospect though. *)

(* HIDE: CH: One alternative (also pointed out by Sven Argo) is that if
   we generalize/duplicate our map library beyond strings we can just
   make memory a single big array of numbers indexed by dynamically
   computed numbers. This would be a lower-level variant of Imp and
   one advantage over the variant with arrays is that our state would
   be a single map, not two. One advantage of the array variant is
   that we can use our existing variables as registers that can be
   accessed without triggering observable events, so our
   noninterference for expressions doesn't change, which is good.  *)

(* HIDE: CH: Maybe a good way to get the best of both worlds would
   be to use a type system to combine the two states into one, yet to
   keep accessing the arrays only with the special ARead and AWrite
   operations above. This would make this part of the chapter depend
   on types, while currently we manged to avoid that dependency, at
   the cost of duplicating the state. If avoiding the dependency is
   important we could dynamically prevent nat vs array type confusion
   for now and only return later to prevent it using static typing?
   Anyway, for now everything seems fine as is and it also matches
   what papers like Spectre Declassified (see below) already do. *)

(* TERSE: HIDEFROMHTML *)

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.
Notation "'call' e" :=
  (Call e)
    (in custom com at level 89, e custom com at level 99) : com_scope.

(* HIDE *)
Check <{{ skip }}>.
Check <{{ (skip ; skip) ; skip }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Definition func (c : com) : com := <{{ c ; skip }}>.
Check <{{ skip; func <{{ skip }}> }}>.
Definition func2 (c1 c2 : com) : com := <{{ c1 ; c2 }}>.
Check <{{ skip ; func2 <{{skip}}> <{{skip}}> }}>.
Check <{ true && ~(false && true) }>.
Check <{{ if true then skip else skip end }}>.
Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>.
Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>.
Check <{{ call 0 }}>.
(* /HIDE *)

Notation "x '<-' a '[[' i ']]'"  :=
  (ARead x a i)
     (in custom com at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  :=
  (AWrite a i e)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com_scope.

Definition state := total_map nat.
Definition astate := total_map (list nat).

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{b ? a1 : a2}> => if beval st b then aeval st a1
          (* ^- NEW -> *)            else aeval st a2
  end
with beval (st : state) (b : bexp) : bool :=
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

Fixpoint upd (i:nat) (ns:list nat) (n:nat) : list nat :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', n' :: ns' => n' :: upd i' ns' n
  | _, _ => ns
  end.
(* TERSE: /HIDEFROMHTML *)

(* NEW *)
Definition prog := list com.

(** ** Observations *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OARead (a : string) (i : nat)
  | OAWrite (a : string) (i : nat)
  | OCall (i : nat).

Definition obs := list observation.

(** * Speculative constant-time *)

(** This part is based on the "Spectre Declassified" paper from IEEE SP 2023,
    just in simplified form. *)

(** The observations are the same as above, so we can just reuse them. *)

Print observation.

(** We additionally add adversary provided directions to our semantics, which
    control speculation behavior. *)

Inductive direction :=
| DStep
| DForce
| DLoad (a : string) (i : nat)
| DStore (a : string) (i : nat)
| DForceCall (j : nat).

Definition dirs := list direction.

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H.
  - auto.
  - simpl in H; apply prefix_cons in H. apply IH in H. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof.
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

Ltac split4 := split; [|split; [| split] ].

(** All results about [slh] assume that the original [c] doesn't
    already use the variable ["b"] needed by the [slh] translation. *)

Fixpoint a_unused (x:string) (a:aexp) : Prop :=
  match a with
  | ANum n      => True
  | AId y       => y <> x
  | <{a1 + a2}>
  | <{a1 - a2}>
  | <{a1 * a2}> => a_unused x a1 /\ a_unused x a2
  | <{b ? a1 : a2}> => b_unused x b /\ a_unused x a1 /\ a_unused x a2
  end
with b_unused (x:string) (b:bexp) : Prop :=
  match b with
  | <{true}>
  | <{false}>     => True
  | <{a1 = a2}>
  | <{a1 <> a2}>
  | <{a1 <= a2}>
  | <{a1 > a2}>   => a_unused x a1 /\ a_unused x a2
  | <{~ b1}>      => b_unused x b1
  | <{b1 && b2}>  => b_unused x b1 /\ b_unused x b2
  end.

Fixpoint unused (x:string) (c:com) : Prop :=
  match c with
  | <{{skip}}> => True
  | <{{y := e}}> => y <> x /\ a_unused x e
  | <{{c1; c2}}> => unused x c1 /\ unused x c2
  | <{{if be then c1 else c2 end}}> =>
      b_unused x be /\ unused x c1 /\ unused x c2
  | <{{while be do c end}}> => b_unused x be /\ unused x c
  | <{{y <- a[[i]]}}> => y <> x /\ a_unused x i
  | <{{a[i] <- e}}> => a_unused x i /\ a_unused x e
  | <{{call e}}> => a_unused x e
  end.

Open Scope string_scope.

(** As a warm-up we prove that [sel_slh] properly updates the variable "b". *)

(** Proving this by induction on [com] or [spec_eval] leads to induction
    hypotheses, that are not strong enough to prove the [While] or [Spec_While]
    case. Therefore we will prove it by induction on the program size
    ([prog_size]) of a tupel [(c :com)] and [(ds :dirs)]. *)

Fixpoint com_size (c :com) :nat :=
  match c with
  | <{{ c1; c2 }}> => 1 + (com_size c1) + (com_size c2)
  (* For conditionals the maximum of both branches is tighter, but a
     looser bound based on blindly "counting all constructors"
     (commented here) works just as well, and is easier to explain on
     paper *)
  | <{{ if be then ct else cf end }}> => 1 + max (com_size ct) (com_size cf)
  (* | <{{ if be then ct else cf end }}> => 1 + (com_size ct) + (com_size cf) *)
  | <{{ while be do cw end }}> => 1 + (com_size cw)
  | <{{ skip }}> => 1
  (* Size 2 for base cases is used in a previous version, 1 actually
     works for all proofs *)
  (* | _  => 2 *)
  | _  => 1
  end.

Definition prog_size (c :com) (ds :dirs) :nat := com_size c + length ds.

(** The induction principle on [prog_size] *)

Lemma prog_size_ind :
  forall P : com -> dirs -> Prop,
  (forall c ds,
    ( forall c' ds',
      prog_size c' ds' < prog_size c ds ->
      P c' ds') -> P c ds  ) ->
  (forall c ds, P c ds).
Proof.
  intros.
  remember (fun c_ds => P (fst c_ds) (snd c_ds)) as P'.
  replace (P c ds) with (P' (c, ds)) by now rewrite HeqP'.
  eapply measure_induction with (f:=fun c_ds => prog_size (fst c_ds) (snd c_ds)). intros. rewrite HeqP'.
  apply H. intros.
  remember (c', ds') as c_ds'.
  replace (P c' ds') with (P' c_ds') by now rewrite Heqc_ds', HeqP'.
  apply H0. now rewrite Heqc_ds'.
Qed.

(** The proof of [sel_slh_flag] *)

Lemma prog_size_monotonic: forall c1 ds1 c2 ds2,
  (com_size c1 < com_size c2 /\ length ds1 <= length ds2 ) \/
  (com_size c1 <= com_size c2 /\ length ds1 < length ds2) ->
  prog_size c1 ds1 < prog_size c2 ds2.
Proof.
  intros c1 ds1 c2 ds2 [ [Hcom Hdir] | [Hcom Hdir] ];
  unfold prog_size; lia.
Qed.

(** Based on the Lemma [prog_size_monotonic] we can build a tactic to solve
    the subgoals in the form of [prog_size c' ds' < prog_size c ds],
    which will be produced by [prog_size_ind].*)

Ltac prog_size_auto :=
  try ( apply prog_size_monotonic; left; split; simpl;
        [| repeat rewrite app_length]; lia );
  try ( apply prog_size_monotonic; right; split; simpl;
        [| repeat rewrite app_length]; lia);
  try ( apply prog_size_monotonic; left; split; simpl;
        [auto | repeat rewrite app_length; lia] ).

Lemma aeval_beval_unused_update : forall X st n,
  (forall ae, a_unused X ae ->
    aeval (X !-> n; st) ae = aeval st ae) /\
  (forall be, b_unused X be ->
    beval (X !-> n; st) be = beval st be).
Proof.
  intros X st n. apply aexp_bexp_mutind; intros;
  simpl in *; try reflexivity;
  try (
    rewrite H; [| tauto]; rewrite H0; [| tauto]; reflexivity
  ).
  - rewrite t_update_neq; eauto.
  - rewrite H; [| tauto]. rewrite H0; [| tauto]. rewrite H1; [| tauto].
    reflexivity.
  - rewrite H; auto.
Qed.

Lemma aeval_unused_update : forall X st ae n,
  a_unused X ae ->
  aeval (X !-> n; st) ae = aeval st ae.
Proof. intros X st ae n. apply aeval_beval_unused_update. Qed.

Lemma beval_unused_update : forall X st be n,
  b_unused X be ->
  beval (X !-> n; st) be = beval st be.
Proof. intros X st be n. apply aeval_beval_unused_update. Qed.
