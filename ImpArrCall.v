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
  | AWrite (a : string) (i : aexp) (e : aexp)  (* <--- NEW *).

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

(** ** Observations *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OARead (a : string) (i : nat)
  | OAWrite (a : string) (i : nat).

Definition obs := list observation.

(** We define an instrumented big-step operational semantics based on these
   observations. *)

(** [[[

          ----------------------------------------     (CTE_Skip)
          <(st , ast)> =[ skip ]=> <(st, ast, [])>

                            aeval st e = n
      --------------------------------------------------    (CTE_Asgn)
      <(st, ast)> =[ x := e ]=> <(x !-> n; st, ast, [])>

            <(st, ast)> =[ c1 ]=> <(st', ast', os1)>
            <(st', ast')> =[ c2 ]=> <(st'', ast'', os2)>
      -----------------------------------------------------   (CTE_Seq)
      <(st, ast)>  =[ c1 ; c2 ]=> <(st'', ast'', os1 ++ os2)>

                  beval st b = true
                  <(st, ast)> =[ c1 ]=> <(st', ast', os1)>
  ---------------------------------------------------------------------------   (* CTE_IfTrue *)
  <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', [OBranch true] ++ os1)>

                  beval st b = false
                  <(st, ast)> =[ c2 ]=> <(st', ast', os1)>
  ----------------------------------------------------------------------------    (* CTE_IfFalse *)
  <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', [OBranch false] ++ os1)>

  <(st,ast)> =[ if b then c; while b do c end else skip end ]=> <(st', ast', os)>
  -------------------------------------------------------------------------------   (* CTE_While *)
              <(st,ast)> =[ while b do c end ]=> <(st', ast', os)>

                    aeval st ie = i
                    i < length (ast a)
  --------------------------------------------------------------------------------    (* CTE_AREad *)
  <(st, ast)> =[ x <- a[[ie]] ]=> <(x !-> nth i (ast a) 0; st, ast, [OARead a i])>

                                aeval st e = n
                                aeval st ie = i
                                i < length (ast a)
    -------------------------------------------------------------------------------   (* CTE_Write *)
    <(st, ast)> =[ a[ie] <- e ]=> <(st, a !-> upd i (ast a) n; ast, [OAWrite a i])>


]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation
         "'<(' st , ast ')>' '=[' c ']=>' '<(' stt , astt , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive cteval : com -> state -> astate -> state -> astate -> obs -> Prop :=
  | CTE_Skip : forall st ast,
      <(st , ast)> =[ skip ]=> <(st, ast, [])>
  | CTE_Asgn  : forall st ast e n x,
      aeval st e = n ->
      <(st, ast)> =[ x := e ]=> <(x !-> n; st, ast, [])>
  | CTE_Seq : forall c1 c2 st ast st' ast' st'' ast'' os1 os2,
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)>  ->
      <(st', ast')> =[ c2 ]=> <(st'', ast'', os2)> ->
      <(st, ast)>  =[ c1 ; c2 ]=> <(st'', ast'', os1++os2)>
  | CTE_IfTrue : forall st ast st' ast' b c1 c2 os1,
      beval st b = true ->
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', [OBranch true] ++ os1)>
  | CTE_IfFalse : forall st ast st' ast' b c1 c2 os1,
      beval st b = false ->
      <(st, ast)> =[ c2 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', [OBranch false] ++ os1)>
  | CTE_While : forall b st ast st' ast' os c,
      <(st,ast)> =[ if b then c; while b do c end else skip end ]=>
        <(st', ast', os)> -> (* <^- Nice trick; from small-step semantics *)
      <(st,ast)> =[ while b do c end ]=> <(st', ast', os)>
  | CTE_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast)> =[ x <- a[[ie]] ]=> <(x !-> nth i (ast a) 0; st, ast, [OARead a i])>
  | CTE_Write : forall st ast a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast)> =[ a[ie] <- e ]=> <(st, a !-> upd i (ast a) n; ast, [OAWrite a i])>

  where "<( st , ast )> =[ c ]=> <( stt , astt , os )>" := (cteval c st ast stt astt os).
(* TERSE: /HIDEFROMHTML *)

(** ** Constant-time security definition *)

(* TERSE: HIDEFROMHTML *)
Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.
Definition pub_arrs := total_map label.

Definition pub_equiv (P : total_map label) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, P x = true -> s1 x = s2 x.

Lemma pub_equiv_refl : forall {X:Type} (P : total_map label) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall {X:Type} (P : total_map label) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof. unfold pub_equiv. intros X P s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall {X:Type} (P : total_map label) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof.
  unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
  rewrite H12; try rewrite H23; auto.
Qed.

Definition ct_secure P PA c :=
  forall st1 st2 ast1 ast2 st1' st2' ast1' ast2' os1 os2,
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    <(st1, ast1)> =[ c ]=> <(st1', ast1', os1)> ->
    <(st2, ast2)> =[ c ]=> <(st2', ast2', os2)> ->
    os1 = os2.

(** ** Example pc secure program that is not constant-time secure *)

Definition ct_insecure_prog :=
   <{{ X <- A[[Y]] }}> .

(* This program is trivially pc secure, because it does not branch at all.
   But it is not constant-time secure, if Y is a secret variable. This is
   shown below. *)

Example ct_insecure_prog_is_not_ct_secure : exists P PA,
  ~ (ct_secure P PA ct_insecure_prog) .
Proof.
  remember (X!-> public; Y!-> secret; _!-> public) as P.
  remember (A!-> secret; _!-> public) as PA.
  exists P. exists PA. unfold ct_secure, ct_insecure_prog; intros H.
  remember (Y!-> 1; _ !-> 0) as st1.
  remember (Y!-> 2; _ !-> 0) as st2.
  remember (A!-> [1;2;3]; _!-> []) as ast.
  assert (Heval1: <(st1, ast)> =[ct_insecure_prog]=> <(X!->2; st1, ast, [OARead A 1])>).
  { unfold ct_insecure_prog; subst.
    replace (X !-> 2; Y !-> 1; _ !-> 0)
      with (X !-> nth 1 ((A!-> [1;2;3]; _!-> []) A) 0; Y !-> 1; _ !-> 0)
        by (reflexivity).
    eapply CTE_ARead; simpl; auto. }
  assert (Heval2: <(st2, ast)> =[ct_insecure_prog]=> <(X!->3; st2, ast, [OARead A 2])>).
  { unfold ct_insecure_prog; subst.
    replace (X !-> 3; Y !-> 2; _ !-> 0)
      with (X !-> nth 2 ((A!-> [1;2;3]; _!-> []) A) 0; Y !-> 2; _ !-> 0)
        by (reflexivity).
      eapply CTE_ARead; simpl; auto. }
  subst. eapply H in Heval2; eauto.
  - inversion Heval2.
  - intros x Hx. destruct (String.eqb_spec Y x) as [Heq | Hneq].
    + subst. rewrite t_update_neq in Hx; [| discriminate].
      rewrite t_update_eq in Hx. discriminate.
    + do 2 (rewrite t_update_neq; [| assumption]). reflexivity.
  - apply pub_equiv_refl.
Qed.
(* TERSE: /HIDEFROMHTML *)

(** ** Type system for cryptographic constant-time programming *)

(* TERSE: HIDEFROMHTML *)

Definition join (l1 l2 : label) : label := l1 && l2.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

Reserved Notation "P '|-a-' a \in l" (at level 40).
Reserved Notation "P '|-b-' b \in l" (at level 40).

Inductive aexp_has_label (P:pub_vars) : aexp -> label -> Prop :=
  | T_Num : forall n,
       P |-a- (ANum n) \in public
  | T_Id : forall X,
       P |-a- (AId X) \in (P X)
  | T_Plus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 + a2 }> \in (join l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 - a2 }> \in (join l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ a1 * a2 }> \in (join l1 l2)
  | T_CTIf : forall be l a1 l1 a2 l2,
       P |-b- be \in l ->
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-a- <{ be ? a1 : a2 }> \in (join l (join l1 l2))

where "P '|-a-' a '\in' l" := (aexp_has_label P a l)

with bexp_has_label (P:pub_vars) : bexp -> label -> Prop :=
  | T_True :
       P |-b- <{ true }> \in public
  | T_False :
       P |-b- <{ false }> \in public
  | T_Eq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 = a2 }> \in (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <> a2 }> \in (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 <= a2 }> \in (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       P |-a- a1 \in l1 ->
       P |-a- a2 \in l2 ->
       P |-b- <{ a1 > a2 }> \in (join l1 l2)
  | T_Not : forall b l,
       P |-b- b \in l ->
       P |-b- <{ ~b }> \in l
  | T_And : forall b1 l1 b2 l2,
       P |-b- b1 \in l1 ->
       P |-b- b2 \in l2 ->
       P |-b- <{ b1 && b2 }> \in (join l1 l2)

where "P '|-b-' b '\in' l" := (bexp_has_label P b l).

Scheme aexp_bexp_has_label_ind := Induction for aexp_has_label Sort Prop
with bexp_aexp_has_label_ind := Induction for bexp_has_label Sort Prop.
Combined Scheme aexp_bexp_has_label_mutind
  from aexp_bexp_has_label_ind,bexp_aexp_has_label_ind.

Theorem noninterferent_aexp_bexp : forall P s1 s2,
  pub_equiv P s1 s2 ->
  (forall a l, P |-a- a \in l ->
   l = public -> aeval s1 a = aeval s2 a) /\
  (forall b l, P |-b- b \in l ->
   l = public -> beval s1 b = beval s2 b).
Proof.
  intros P s1 s2 Heq. apply (aexp_bexp_has_label_mutind P);
    simpl; intros;
    (repeat match goal with
    | [Heql : join _ _ = public |- _] =>
      let G1 := fresh "G1" in
      let G2 := fresh "G2" in
      destruct (join_public Heql) as [G1 G2];
      rewrite G1 in *; rewrite G2 in *
    end); try reflexivity; eauto; firstorder;
    (repeat match goal with
    | [IH : aeval s1 ?a = aeval s2 ?a |- _] => rewrite IH
    end);
    (repeat match goal with
    | [IH : beval s1 ?b = beval s2 ?b |- _] => rewrite IH
    end); reflexivity.
Qed.

Theorem noninterferent_aexp : forall {P s1 s2 a},
  pub_equiv P s1 s2 ->
  P |-a- a \in public ->
  aeval s1 a = aeval s2 a.
Proof.
  intros P s1 s2 a Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

Theorem noninterferent_bexp : forall {P s1 s2 b},
  pub_equiv P s1 s2 ->
  P |-b- b \in public ->
  beval s1 b = beval s2 b.
Proof.
  intros P s1 s2 b Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

(* TERSE: /HIDEFROMHTML *)

(** [[[
                         ------------------                 (CT_Skip)
                         P ;; PA |-ct- skip

             P |-a- a \in l    can_flow l (P X) = true
             -----------------------------------------      (CT_Asgn)
                       P ;; PA |-ct- X := a

               P ;; PA |-ct- c1    P ;; PA |-ct- c2
               ------------------------------------          (CT_Seq)
                       P ;; PA |-ct- c1;c2

  P |-b- b \in public    P ;; PA |-ct- c1    P ;; PA |-ct- c2
  ----------------------------------------------------------- (CT_If)
               P ;; PA |-ct- if b then c1 else c2

                  P |-b- b \in public    P |-ct- c
                  --------------------------------         (CT_While)
                  P ;; PA |-ct- while b then c end

      P |-a- i \in public   can_flow (PA a) (P x) = true
      --------------------------------------------------   (CT_ARead)
                  P ;; PA |-ct- x <- a[[i]]

P |-a- i \in public   P |-a- e \in l   can_flow l (PA a) = true
--------------------------------------------------------------- (CT_AWrite)
                   P ;; PA |-ct- a[i] <- e
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P ';;' PA '|-ct-' c" (at level 40).

Inductive ct_well_typed (P:pub_vars) (PA:pub_arrs) : com -> Prop :=
  | CT_Skip :
      P ;; PA |-ct- <{{ skip }}>
  | CT_Asgn : forall X a l,
      P |-a- a \in l ->
      can_flow l (P X) = true ->
      P ;; PA |-ct- <{{ X := a }}>
  | CT_Seq : forall c1 c2,
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ c1 ; c2 }}>
  | CT_If : forall b c1 c2,
      P |-b- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- c2 ->
      P ;; PA |-ct- <{{ if b then c1 else c2 end }}>
  | CT_While : forall b c1,
      P |-b- b \in public ->
      P ;; PA |-ct- c1 ->
      P ;; PA |-ct- <{{ while b do c1 end }}>
  | CT_ARead : forall x a i,
      P |-a- i \in public ->
      can_flow (PA a) (P x) = true ->
      P ;; PA |-ct- <{{ x <- a[[i]] }}>
  | CT_AWrite : forall a i e l,
      P |-a- i \in public ->
      P |-a- e \in l ->
      can_flow l (PA a) = true ->
      P ;; PA |-ct- <{{ a[i] <- e }}>

where "P ;; PA '|-ct-' c" := (ct_well_typed P PA c).
(* TERSE: /HIDEFROMHTML *)

(** ** Final theorems: noninterference and constant-time security *)

Theorem ct_well_typed_noninterferent :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1)> =[ c ]=> <(s1', a1', os1)> ->
    <(s2, a2)> =[ c ]=> <(s2', a2', os2)> ->
    pub_equiv P s1' s2' /\ pub_equiv PA a1' a2'.
(* FOLD *)
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - split; auto.
  - split; auto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      eapply noninterferent_aexp; eauto.
      subst. rewrite Hy in H11.
      unfold can_flow in H11. simpl in H11.
      destruct l; try discriminate. auto.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto. now destruct (PA a).
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* NEW CASE: AWrite *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy.
    destruct (String.eqb_spec a y) as [Hay | Hay].
    + rewrite Hay. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto.
      erewrite (noninterferent_aexp Heq); eauto. now destruct l.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hay).
      apply Haeq. apply Hy.
Qed.
(* /FOLD *)

Theorem ct_well_typed_ct_secure : forall P PA c,
  P ;; PA |-ct- c ->
  ct_secure P PA c.
(* FOLD *)
Proof.
  unfold ct_secure.
  intros P PA c Hwt st1 st2 ast1 ast2 st1' st2' ast1' ast2' os1 os2
    Heq Haeq Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent ast2'. generalize dependent ast2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* NEW CASE: AWrite *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.
(* /FOLD *)

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
| DStore (a : string) (i : nat).

Definition dirs := list direction.

Reserved Notation
         "'<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_eval : com -> state -> astate -> bool -> dirs ->
                             state -> astate -> bool -> obs -> Prop :=
  | Spec_Skip : forall st ast b,
      <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Spec_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Spec_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Spec_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, b, ds)> =[ match beval st be with
                       | true => c1
                       | false => c2 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (beval st be)] ++ os1)>
  | Spec_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, true, ds)> =[ match beval st be with
                       | true => c2 (* <-- branches swapped *)
                       | false => c1 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (beval st be)] ++ os1)>
  | Spec_While : forall be st ast b ds st' ast' b' os c,
      <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Spec_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Spec_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i' (ast a') 0; st, ast, true, [OARead a i])>
  | Spec_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>
  | Spec_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (ast a') n; ast, true, [OAWrite a i])>

  where "<( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (spec_eval c st ast b ds stt astt bb os).

(* HIDE: This semantics already lost one property of Imp: only nonterminating
   executions don't produce a final state. Now if the input directions don't
   match what the program expects or if we non-speculatively access arrays out
   of bounds we also get stuck, which for our big-step semantics can't be
   distinguished from nontermination. This is probably not a problem for now,
   but just wanted to mention it. *)

(* HIDE: Making non-speculative out-of-bounds array accesses stuck is a design
   decision that matches Spectre Declassified. For languages like Jasmin they
   use static analysis to verify that programs are non-speculatively safe, so
   only speculative executions can cause OOB accesses. *)

(* HIDE: Without fences the speculation bit [b] is mostly a form of
   instrumentation that doesn't affect the semantics, except for adding some
   stuckness for the [_U] rules, corresponding to non-speculative OOB accesses. *)

(* LATER: Could also add fences, but they are not needed for SLH, beyond for
   enforcing that the speculation flag starts false, which can also be assumed.
   Fences would add
   a bit of complexity to the big-step semantics, since they behave like a halt
   instruction that prematurely ends execution, which means adding at least one
   more rule for sequencing (basically an error monad, but with a (halt) bit of
   cleverness we can probably avoid extra rules for if and while, since we're
   just threading through things). We likely don't want to treat this stuckness
   as not producing a final state though, since a stuck fence should be a final
   state in their small-step semantics (actually they messed that up,
   see next point). *)

(* LATER: Could prove this semantics equivalent to the small-step one from the
   two IEEE SP 2023 papers. The fact that their rule [Seq-Skip] requires a step
   seems wrong if first command in the sequence is already skip. Also the way
   they define final results seem wrong for stuck fences, and that would either
   need to be fixed to include stuck fences deep inside as final results
   or to bubble up stuck fences to the top (error monad, see prev point). *)

(* HIDE: One design decision here is to neither consume DSteps not to generate
   dummy observations for skip and (register) assignment commands. This leads to
   simpler proofs (e.g. no need for erasure) and it also seems sensible: it's
   not like a skip takes the same time as an assignment anyway, so making these
   things observable with the same dummy event seems anyway questionable! *)

(* LATER: Could add the declassify construct from Spectre Declassified, but for
   now trying to keep things simple. If we add that then the RNI notion of
   Definition 2 relies on the small-step semantics to stop at the first force
   directive. Doing that with a big-step semantics seems trickier. We could
   build a version that halts early on the first force? *)

(** ** Speculative constant-time security definition *)

Definition spec_ct_secure P PA c :=
  forall st1 st2 ast1 ast2 st1' st2' ast1' ast2' b1' b2' os1 os2 ds,
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    <(st1, ast1, false, ds)> =[ c ]=> <(st1', ast1', b1', os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(st2', ast2', b2', os2)> ->
    os1 = os2.

(** ** Example constant-time program that is insecure under speculative execution. *)

Definition spec_insecure_prog :=
  <{{ if Z <= 0 then
        X <- AP[[Z]];
        if X <= 5 then Y := 1 else Y := 0 end
      else skip end }}> .

Example spec_insecure_prog_is_ct_and_spec_insecure :
 exists P PA,
  P ;; PA |-ct- spec_insecure_prog /\ ~ (spec_ct_secure P PA spec_insecure_prog) .
Proof.
  exists (X!-> public; Y!-> public; Z!-> public; _ !-> secret).
  exists  (AP!-> public; AS!-> secret; _ !-> public).
  split; unfold spec_insecure_prog.
  - repeat econstructor;
    replace (public) with (join public public) at 4 by reflexivity;
    repeat constructor.
  - intros H.
    remember (Z!-> 1; _ !-> 0) as st.
    remember (AP!-> [1]; AS!-> [1;3]; _ !-> []) as ast1.
    remember (AP!-> [1]; AS!-> [1;7]; _ !-> []) as ast2.
    remember (DForce :: ([DLoad "AS" 1] ++ [DStep])) as ds.
    remember (([OBranch false] ++ ([OARead "AP" 1]) ++ [OBranch true])) as os1.
    remember (([OBranch false] ++ ([OARead "AP" 1])++ [OBranch false])) as os2.
    assert (Heval1:
    <(st, ast1, false, ds )> =[ spec_insecure_prog ]=> <( Y!-> 1; X!-> 3; st, ast1, true, os1)>).
    { unfold spec_insecure_prog; subst.
      eapply Spec_If_F. eapply Spec_Seq.
      - eapply Spec_ARead_U; simpl; eauto.
      - replace ([OBranch true]) with ([] ++ [OBranch true]) by reflexivity.
        eapply Spec_If; simpl. eapply Spec_Asgn; eauto. }
    assert (Heval2:
      <(st, ast2, false, ds )> =[ spec_insecure_prog ]=> <( Y!-> 0; X!-> 7; st, ast2, true, os2)>).
      { unfold spec_insecure_prog; subst.
        eapply Spec_If_F. eapply Spec_Seq.
        - eapply Spec_ARead_U; simpl; eauto.
        - replace ([OBranch false]) with ([] ++ [OBranch false]) by reflexivity.
          eapply Spec_If; simpl. eapply Spec_Asgn; eauto. }
    subst. eapply H in Heval1.
    + eapply Heval1 in Heval2. inversion Heval2.
    + eapply pub_equiv_refl.
    + intros x Hx. destruct (String.eqb_spec "AP" x) as [HeqAP | HneqAP];
      destruct (String.eqb_spec "AS" x) as [HeqAS | HneqAS].
      * subst. do 2 rewrite t_update_eq. reflexivity.
      * subst. do 2 rewrite t_update_eq. reflexivity.
      * subst. rewrite t_update_neq in Hx; [| assumption].
        rewrite t_update_eq in Hx. discriminate.
      * do 4 (rewrite t_update_neq; [| assumption]). reflexivity.
Qed.

(* HIDE: Just to warm up formalized the first lemma in the Spectre Declassified
   paper: Lemma 1: structural properties of execution *)

Lemma speculation_bit_monotonic : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof. intros c s a b ds s' a' b' os Heval Hb. induction Heval; eauto. Qed.

(* HIDE: This one is weaker for big-step semantics, but it's still helpful below *)
Lemma speculation_needs_force : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

(* HIDE: Also this one is weaker for big-step semantics *)
Lemma unsafe_access_needs_speculation : forall c s a b ds s' a' b' os ax i,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  In (DLoad ax i) ds \/ In (DStore ax i) ds ->
  b = true \/ In DForce ds.
Proof.
  intros c s a b ds s' a' b' os ax i Heval Hin.
  induction Heval; simpl in *; try tauto; try (firstorder; discriminate).
  - destruct Hin as [Hin | Hin].
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_introl _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_introl _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          (* slightly more interesting case, the rest very boring *)
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
    + (* very symmetric, mostly copy paste *)
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_intror _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_intror _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
Qed.

(** We can recover sequential execution from [spec_eval] if there is no
    speculation, so all directives are [DStep] and speculation flag starts [false]. *)

Definition seq_spec_eval (c :com) (st :state) (ast :astate)
    (st' :state) (ast' :astate) (os :obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(st, ast, false, ds)> =[ c ]=> <(st', ast', false, os)>.

(* Sequential execution is equivalent to constant-time evaluation, i.e. [cteval].  *)

Lemma cteval_equiv_seq_spec_eval : forall c st ast st' ast' os,
  seq_spec_eval c st ast st' ast' os <-> <(st, ast)> =[ c ]=> <(st', ast', os)> .
Proof.
  intros c st ast st' ast' os. unfold seq_spec_eval. split; intros H.
  - (* -> *)
    destruct H as [ds [Hstep Heval] ].
    induction Heval; try (now econstructor; eauto).
    + (* Spec_Seq *) eapply CTE_Seq.
      * eapply IHHeval1. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (left; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
      * eapply IHHeval2. intros d HdIn.
        assert (L: In d ds1 \/ In d ds2) by (right; assumption).
        eapply in_or_app in L. eapply Hstep in L. assumption.
    + (* Spec_If *) destruct (beval st be) eqn:Eqbe.
      * eapply CTE_IfTrue; [assumption |].
        eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn. apply Hstep in HdIn. assumption.
      * eapply CTE_IfFalse; [assumption |].
        eapply IHHeval. intros d HdIn.
        apply (in_cons DStep d) in HdIn. apply Hstep in HdIn. assumption.
    + (* Spec_IF_F; contra *) exfalso.
      assert (L: ~(DForce = DStep)) by discriminate. apply L.
      apply (Hstep DForce). apply in_eq.
    + (* Spec_ARead_U; contra *) exfalso.
      assert (L: ~(DLoad a' i' = DStep)) by discriminate. apply L.
      apply (Hstep (DLoad a' i')). apply in_eq.
    + (* Spec_AWrite_U; contra *) exfalso.
      assert (L: ~(DStore a' i' = DStep)) by discriminate. apply L.
      apply (Hstep (DStore a' i')). apply in_eq.
  - (* <- *)
    induction H.
    + (* CTE_Skip *)
      exists []; split; [| eapply Spec_Skip].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Asgn *)
      exists []; split; [| eapply Spec_Asgn; assumption].
      simpl. intros d Contra; destruct Contra.
    + (* CTE_Seq *)
      destruct IHcteval1 as [ds1 [Hds1 Heval1] ].
      destruct IHcteval2 as [ds2 [Hds2 Heval2] ].
      exists (ds1 ++ ds2). split; [| eapply Spec_Seq; eassumption].
      intros d HdIn. apply in_app_or in HdIn. destruct HdIn as [Hin1 | Hin2].
      * apply Hds1 in Hin1. assumption.
      * apply Hds2 in Hin2. assumption.
    + (* CTE_IfTrue *)
      destruct IHcteval as [ds [Hds Heval] ]. exists (DStep :: ds). split.
      * intros d HdIn. apply in_inv in HdIn.
        destruct HdIn as [Heq | HIn]; [symmetry; assumption | apply Hds; assumption].
      * rewrite <- H. eapply Spec_If. rewrite H; simpl. assumption.
    + (* CTE_IfFalse *)
      destruct IHcteval as [ds [Hds Heval] ]. exists (DStep :: ds). split.
      * intros d HdIn. apply in_inv in HdIn.
        destruct HdIn as [Heq | HIn]; [symmetry; assumption | apply Hds; assumption].
      * rewrite <- H. eapply Spec_If. rewrite H; simpl. assumption.
    + (* CTE_While *)
      destruct IHcteval as [ds [Hds Heval] ]. exists ds.
      split; [assumption |]. eapply Spec_While; assumption.
    + (* CTE_ARead *)
      exists [DStep]. split.
      * simpl. intros d HdIn. destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_ARead; assumption.
    + (* CTE_AWrite *)
      exists [DStep]. split.
      * simpl. intros d HdIn. destruct HdIn as [Heq | Contra]; [| destruct Contra].
        symmetry. assumption.
      * eapply Spec_Write; assumption.
Qed.

(* HIDE: This is Lemma 2 from Spectre Declassified *)

Lemma ct_well_typed_seq_spec_eval_ct_secure :
  forall P PA c st1 st2 ast1 ast2 st1' st2' ast1' ast2' os1 os2,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    seq_spec_eval c st1 ast1 st1' ast1' os1 ->
    seq_spec_eval c st2 ast2 st2' ast2' os2 ->
    os1 = os2.
Proof.
  intros P PA c st1 st2 ast1 ast2 st1' st2' ast1' ast2' os1 os2 Hwt
    HP HPA Heval1 Heval2.
  apply cteval_equiv_seq_spec_eval in Heval1, Heval2.
  apply ct_well_typed_ct_secure in Hwt. eapply Hwt; eauto.
Qed.

(** Selective SLH transformation that we will show enforces speculative
    constant-time security. *)

Fixpoint sel_slh (P:pub_vars) (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ sel_slh P c1; sel_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then "b" := (be ? "b" : 1); sel_slh P c1
               else "b" := (be ? 1 : "b"); sel_slh P c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be do "b" := (be ? "b" : 1); sel_slh P c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
      if P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
             else <{{x <- a[[i]]}}>
  | <{{a[i] <- e}}> => <{{a[i] <- e}}>
  end)%string.

(** To prove this transformation secure, Spectre Declassified uses an idealized
    semantics, capturing selective speculative load hardening more abstractly. *)

(* HIDE: We had to fix their ideal semantics for the proofs to go though: (1) in
   (Ideal_ARead) we are allowing mis-speculated in-bound reads; (2) we removed
   (Ideal_ARead_Prot), by merging it with the other two rules and producing the
   correct direction; and (3) removed harmful preconditions in both cases. *)

Reserved Notation
         "P '|-' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval (P:pub_vars) :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      P |- <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      P |- <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      P |- <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      P |- <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      P |- <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, b, ds)> =[ match beval st be with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (beval st be)] ++ os1 )>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, true, ds)> =[ match beval st be with
                                    | true => c2 (* <-- branches swapped *)
                                    | false => c1 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (beval st be)] ++ os1)>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      P |- <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      P |- <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < length (ast a) ->
      P |- <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> if b && P x then 0 else nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> if P x then 0 else nth i' (ast a') 0; st, ast, true, [OARead a i])>
  | Ideal_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      P |- <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>
  | Ideal_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (ast a') n; ast, true, [OAWrite a i])>

  where "P |- <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval P c st ast b ds stt astt bb os).

(* We show that on sequential executions this is equivalent to [seq_spec_eval] *)

Lemma seq_eval_ideal_eval_ind1 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof.
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - (* Seq *)
    assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Ideal_Seq.
    * apply IHspec_eval1; eauto using in_or_app.
    * apply IHspec_eval2; eauto using in_or_app.
  - (* If *) simpl in Hds; eauto.
  - (* If_F *) simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - (* ARead *)
    destruct b eqn:Eqb; [discriminate |].
    replace (x !-> nth i (ast a) 0; st)
      with (x !-> if b && P x then 0 else nth i (ast a) 0; st)
        by (rewrite Eqb; simpl; reflexivity).
    rewrite <- Eqb. eapply Ideal_ARead; eauto.
  - (* AREad_U *) discriminate.
Qed.

Lemma speculation_needs_force_ideal : forall P c s a b ds s' a' b' os,
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros P c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Lemma seq_eval_ideal_eval_ind2 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof. (* proof really the same as gen1 *)
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - (* Seq *)
    assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force_ideal in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Spec_Seq.
    * apply IHideal_eval1; eauto using in_or_app.
    * apply IHideal_eval2; eauto using in_or_app.
  - (* IF *) simpl in Hds; eauto.
  - (* If_F *) simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - (* ARead *)
    destruct b eqn:Eqb; [discriminate |]; simpl.
    eapply Spec_ARead; eauto.
  - discriminate.
Qed.

(* HIDE: This is Lemma 3 from Spectre Declassified *)

Definition seq_ideal_eval (P:pub_vars) (c:com) (s:state) (a:astate)
    (s':state) (a':astate) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    P |- <(s, a, false, ds)> =[ c ]=> <(s', a', false, os)>.

Lemma seq_spec_eval_ideal_eval : forall P c s a s' a' os,
  seq_spec_eval c s a s' a' os <->
  seq_ideal_eval P c s a s' a' os.
Proof.
  intros P c s a s' a' os. unfold seq_spec_eval, seq_ideal_eval.
  split; intros [ds [Hds H] ]; exists ds; (split; [ apply Hds |]).
  - apply seq_eval_ideal_eval_ind1; eauto.
  - eapply seq_eval_ideal_eval_ind2; eauto.
Qed.

(** Let's now prove that the idealized semantics does enforce speculative constant-time *)

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

Lemma pub_equiv_update_public : forall P {A:Type}
    (t1 t2 : total_map A) (X :string) (a1 a2 :A),
  pub_equiv P t1 t2 ->
  P X = public ->
  a1 = a2 ->
  pub_equiv P (X!-> a1; t1) (X!-> a2; t2).
Proof.
  intros P A t1 t2 X a1 a2 Hequiv Hpub Ha1a2 x Hx.
  destruct (String.eqb_spec X x) as [Heq | Hneq].
  - subst. do 2 rewrite t_update_eq. reflexivity.
  - do 2 (rewrite t_update_neq;[| auto]). eapply Hequiv; eauto.
Qed.

Lemma pub_equiv_update_secret : forall P {A:Type}
    (t1 t2 : total_map A) (X :string) (a1 a2 :A),
  pub_equiv P t1 t2 ->
  P X = secret ->
  pub_equiv P (X!-> a1; t1) (X!-> a2; t2).
Proof.
  intros P A t1 t2 X a1 a2 Hequiv Hsec x Hx.
  destruct (String.eqb_spec X x) as [Heq | Hneq].
  - subst. rewrite Hsec in Hx. discriminate.
  -  do 2 (rewrite t_update_neq;[| auto]). eapply Hequiv; eauto.
Qed.

Lemma ct_well_typed_ideal_noninterferent_general :
  forall P PA c st1 st2 ast1 ast2 b st1' st2' ast1' ast2' b1' b2' os1 os2 ds1 ds2,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    (b = false -> pub_equiv PA ast1 ast2) ->
    (prefix ds1 ds2 \/ prefix ds2 ds1) -> (* <- interesting generalization *)
    P |- <(st1, ast1, b, ds1)> =[ c ]=> <(st1', ast1', b1', os1)> ->
    P |- <(st2, ast2, b, ds2)> =[ c ]=> <(st2', ast2', b2', os2)> ->
    pub_equiv P st1' st2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv PA ast1' ast2') /\
      ds1 = ds2.  (* <- interesting generalization *)
Proof.
  intros P PA c st1 st2 ast1 ast2 b st1' st2' ast1' ast2' b1' b2' os1 os2 ds1 ds2
    Hwt Heq Haeq Hds Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent ast2'. generalize dependent ast2.
  generalize dependent os2. generalize dependent b2'.
  generalize dependent ds2.
  induction Heval1; intros ds2X Hds b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) auto.
  - (* Asgn *) split4; auto.
    destruct (P x) eqn:EqPx.
    + eapply pub_equiv_update_public; eauto.
      eapply noninterferent_aexp; eauto.
      destruct l; [auto | simpl in H14; discriminate].
    + eapply pub_equiv_update_secret; eauto.
  - (* Seq *)
    destruct Hds as [Hpre | Hpre]; apply prefix_app in Hpre as Hds1.
    + (* prefix (ds1 ++ ds2) (ds0 ++ ds3) *)
      eapply IHHeval1_1 in Hds1; eauto.
      destruct Hds1 as [ Hstates [Hbits [Hastates Hdirections] ] ]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder. subst. reflexivity.
    + (* prefix (ds0 ++ ds3) (ds1 ++ ds2) *)
      eapply IHHeval1_1 with (ds2:=ds0) in H13; eauto; [| tauto].
      destruct H13 as [ Hstates [Hbits [Hastates Hdirections] ] ]. subst.
      eapply prefix_append_front in Hpre as Hds2.
      eapply IHHeval1_2 in H14; eauto. firstorder; subst; reflexivity.
  - (* If *)
    assert(G : P ;; PA |-ct- (if beval st be then c1 else c2)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + specialize (IHHeval1 G _ Gds _ _ _ Haeq _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* IF; contra *)
    apply prefix_or_heads in Hds; inversion Hds.
  - (* IF; contra *)
     apply prefix_or_heads in Hds; inversion Hds.
  - (* If_F; analog to If *)
    assert(G : P ;; PA |-ct- (if beval st be then c2 else c1)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + assert(GG: true = false -> pub_equiv PA ast a2). (* <- only difference *)
      { intro Hc. discriminate. }
      specialize (IHHeval1 G _ Gds _ _ _ GG _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* While *) eapply IHHeval1; try eassumption. repeat constructor; eassumption.
  - (* ARead *) split4; eauto.
    destruct (P x) eqn:EqPx; simpl.
    + eapply pub_equiv_update_public; eauto.
      destruct b2' eqn:Eqb2'; simpl; [reflexivity |].
      unfold can_flow in H18. eapply orb_true_iff in H18.
      destruct H18 as [Hapub | Contra]; [| simpl in Contra; discriminate].
      eapply Haeq in Hapub; [| reflexivity]. rewrite Hapub.
      eapply noninterferent_aexp in Heq; eauto. rewrite Heq.
      reflexivity.
    + eapply pub_equiv_update_secret; eauto.
  - (* ARead_U *) split4; eauto.
    + destruct (P x) eqn:EqPx.
      * simpl. eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* ARead *) split4; eauto.
    + destruct (P x) eqn:EqPx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds.
  - (* Aread_U *) split4; eauto.
    + destruct (P x) eqn:EqPx.
      * eapply pub_equiv_update_public; eauto.
      * eapply pub_equiv_update_secret; eauto.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
  - (* Write *) split4; eauto. intro Hb2'.
    destruct (PA a) eqn:EqPAa.
    + eapply pub_equiv_update_public; eauto.
      destruct l eqn:Eql.
      * eapply noninterferent_aexp in H19, H20; eauto. rewrite H19, H20.
        apply Haeq in Hb2'. apply Hb2' in EqPAa. rewrite EqPAa. reflexivity.
      * simpl in H21. discriminate.
    + eapply pub_equiv_update_secret; eauto.
  - (* Write_U; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* Write; contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* Write_U; contra *) split4; eauto.
    + intro contra. discriminate contra.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
Qed.

Lemma ct_well_typed_ideal_noninterferent :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    pub_equiv P s1' s2' /\ b1' = b2' /\ (b1' = false -> pub_equiv PA a1' a2').
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  eapply ct_well_typed_ideal_noninterferent_general in Heval2; eauto; try tauto.
  left. apply prefix_refl.
Qed.

(** This corollary (used below) also follows from [noninterferent_general] *)
Corollary aux : forall P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2',
  ds2 ++ ds2' = ds1 ++ ds1' ->
  P ;; PA |-ct- c ->
  pub_equiv P s1 s2 ->
  (b = false -> pub_equiv PA a1 a2) ->
  P |- <(s1, a1, b, ds1)> =[ c ]=> <(st1, ast1, b1, os1)>  ->
  P |- <(s2, a2, b, ds2)> =[ c ]=> <(st2, ast2, b2, os2)> ->
  ds1 = ds2 /\ ds1' = ds2'.
Proof.
  intros P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2'
    Hds Hwt Heq Haeq Heval1 Heval2.
  pose proof Hds as H.
  symmetry in H.
  apply app_eq_prefix in H.
  eapply ct_well_typed_ideal_noninterferent_general in H;
    [ | | | | apply Heval1 | apply Heval2]; try eassumption.
  - destruct H as [ _ [ _ [ _ H] ] ]. subst. split; [reflexivity|].
    apply app_inv_head in Hds. congruence.
Qed.

Theorem ideal_spec_ct_secure :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2. generalize dependent b2'.
  induction Heval1; intros b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) reflexivity.
  - (* Skip *) reflexivity.
  - (* Seq *) eapply aux in H1; [| | | | apply Heval1_1 | apply H5 ]; eauto.
    destruct H1 as [H1 H1']. subst.
    assert(NI1 : pub_equiv P st' st'0 /\ b' = b'0 /\ (b' = false -> pub_equiv PA ast' ast'0)).
    { eapply ct_well_typed_ideal_noninterferent; [ | | | eassumption | eassumption]; eauto. }
    destruct NI1 as [NI1eq [NIb NIaeq] ]. subst.
    erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
  - (* If *) f_equal.
    + f_equal. eapply noninterferent_bexp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      erewrite noninterferent_bexp; eassumption.
  - (*If_F *) f_equal.
    + f_equal. eapply noninterferent_bexp in Heq; [| eassumption].
      rewrite Heq. reflexivity.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      * intro contra. discriminate contra.
      * erewrite noninterferent_bexp; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* ARead *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.

(** We now prove that the idealized semantics is equivalent to [sel_slh]
    transformation (Lemma 6 and the more precise Lemma 7). *)

(** All results about [sel_slh] below assume that the original [c] doesn't
    already use the variable ["b"] needed by the [sel_slh] translation. *)

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
  end.

Open Scope string_scope.

(* HIDE *)

(* Even something as simple as [sel_slh_flag] below turns out to be hard
   to prove by induction on [com] or [spec_eval], in the [While] or [Spec_While] case,
   since it has the flavour of backwards compiler correctness (BCC).
   Therefore we use the induction principal [prog_size_ind], which
   is statet further below. *)

(* CH: Here are a couple of failed attempts at generalizing to while loops. *)

(** We start with a failed syntactic generalization *)

Lemma sel_slh_flag_gen : forall cc P s a (b:bool) ds s' a' (b':bool) os,
  <(s, a, b, ds)> =[ cc ]=> <(s', a', b', os)> ->
  forall sc,
    cc = sel_slh P sc ->
    unused "b" sc ->
    s "b" = (if b then 1 else 0) ->
    s' "b" = (if b' then 1 else 0).
Proof.
  intros cc P s a b ds s' a' b' os H. induction H; intros sc Heq Hunused Hsb.
  6:{ (* No chance to prove the following to instantiate the IH:
      <{{ if be then c; while be do c end else skip end }}> = sel_slh P sc *)
      admit. }
Abort.

(** Failed generalization by equivalence *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall s a b ds s' a' b' os,
        (<(s, a, b, ds)> =[ c1 ]=> <(s', a', b', os)>)
    <-> (<(s, a, b, ds)> =[ c2 ]=> <(s', a', b', os)>).

Lemma cequiv_refl : forall c,
  cequiv c c.
Admitted.

Lemma cequiv_trans : forall c1 c2 c3,
  cequiv c1 c2 ->
  cequiv c2 c3 ->
  cequiv c1 c3.
Admitted.

Lemma cequiv_while_step : forall be c,
  cequiv <{{if be then c; while be do c end else skip end}}>
         <{{while be do c end}}>.
Admitted.

Lemma sel_slh_flag_gen : forall cc P s a (b:bool) ds s' a' (b':bool) os,
  <(s, a, b, ds)> =[ cc ]=> <(s', a', b', os)> ->
  forall sc,
    cequiv cc (sel_slh P sc) ->
    unused "b" sc ->
    s "b" = (if b then 1 else 0) ->
    s' "b" = (if b' then 1 else 0).
Proof.
  intros cc P s a b ds s' a' b' os H. induction H; intros sc Hequiv Hunused Hsb.
  6:{ (* While case now provable *)
  eapply IHspec_eval; eauto. eapply cequiv_trans; eauto.
  apply cequiv_while_step. }
  3:{ (* But the Seq case is now problematic *) admit. }
Admitted.

Lemma sel_slh_flag : forall sc P st ast (b:bool) ds st' ast' (b':bool) os,
  unused "b" sc ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ sel_slh P sc ]=> <(st', ast', b', os)> ->
  st' "b" = (if b' then 1 else 0).
Proof.
  intros c P s a b ds s' a' b' os Hunused Hsb Heval.
  eapply sel_slh_flag_gen; eauto. apply cequiv_refl.
Abort.
(* /HIDE *)

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

(** To properly apply [prog_size_ind], we need to state [sel_slh_flag]
    as a proposition of type [com -> dirs -> Prop]. Therefore we define the
    following: *)

Definition sel_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall P st ast (b:bool) st' ast' (b':bool) os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ sel_slh P c ]=> <(st', ast', b', os)> ->
  st' "b" = (if b' then 1 else 0).

Lemma sel_slh_flag : forall c ds,
  sel_slh_flag_prop c ds.
Proof.
  eapply prog_size_ind. unfold sel_slh_flag_prop.
  intros c ds IH P st ast b st' ast' b' os Hunused Hstb Heval.
  destruct c; simpl in *; try (now inversion Heval; subst; eauto).
  - (* Asgn *)
    inversion Heval; subst. rewrite t_update_neq; tauto.
  - (* Seq *)
    inversion Heval; subst; clear Heval.
    apply IH in H1; try tauto.
    + apply IH in H10; try tauto. prog_size_auto.
    + prog_size_auto.
  - (* IF *)
    inversion Heval; subst; clear Heval.
    + (* Spec_If *)
      destruct (beval st be) eqn:Eqnbe.
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { prog_size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
      * (* analog to true case *)
        inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { prog_size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. assumption. }
    + (* Spec_If_F; analog to Spec_If case *)
      destruct (beval st be) eqn:Eqnbe.
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { prog_size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. reflexivity. }
      * inversion H10; subst; clear H10.
        inversion H1; subst; clear H1.
        apply IH in H11; try tauto.
        { prog_size_auto. }
        { rewrite t_update_eq. simpl. rewrite Eqnbe. reflexivity. }
  - (* While *)
      inversion Heval; subst; clear Heval.
      inversion H1; subst; clear H1.
      inversion H11; subst; clear H11.
      + (* non-speculative *)
        destruct (beval st be) eqn:Eqnbe.
        * inversion H12; subst; clear H12.
          assert(Hwhile: <(st'1, ast'1, b'1, (ds0 ++ ds2)%list)>
              =[ sel_slh P <{{while be do c end}}> ]=> <(st', ast', b', (os3++os2)%list)> ).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { prog_size_auto. }
          { clear Hwhile; clear H11.
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2. simpl in H12.
            apply IH in H12; try tauto.
            - prog_size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. assumption. }
        * inversion H12; subst; clear H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. assumption.
      + (* speculative; analog to non_speculative case *)
        destruct (beval st be) eqn:Eqnbe.
        * inversion H12; subst; clear H12.
          inversion H10; subst; simpl.
          rewrite t_update_eq, Eqnbe; simpl. reflexivity.
        * inversion H12; subst; clear H12.
          assert(Hwhile: <(st'1, ast'1, b'1, (ds0 ++ ds2)%list)>
              =[sel_slh P <{{while be do c end}}>]=> <(st', ast', b', (os3++os2)%list )>).
          { simpl. eapply Spec_Seq; eassumption. }
          apply IH in Hwhile; eauto.
          { prog_size_auto. }
          { clear Hwhile; clear H11.
            inversion H1; subst; clear H1.
            inversion H2; subst; clear H2. simpl in H12.
            apply IH in H12; try tauto.
            - prog_size_auto.
            - rewrite t_update_eq, Eqnbe; simpl. reflexivity. }
  - (* ARead *)
    destruct (P x) eqn:Eqnbe.
    + inversion Heval; subst; clear Heval.
      inversion H10; subst; clear H10.
      rewrite t_update_neq; [| tauto].
      inversion H1; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
    + inversion Heval; subst;
      try (rewrite t_update_neq; [assumption| tauto]).
Qed.

(** We now prove that [sel_slh] implies the ideal semantics. *)

(* HIDE *)
(* CH: no longer used in [sel_slh_ideal], but maybe still useful (TBD) *)
Lemma ideal_unused_same : forall P st ast b ds c st' ast' b' os X,
  unused X c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  st' X = st X.
Proof.
  intros P st ast b ds c st' ast' b' os X Hu Heval.
  induction Heval; simpl in Hu; try reflexivity; try (rewrite t_update_neq; tauto).
  - (* Seq *) rewrite IHHeval2; [| tauto]. rewrite IHHeval1; [| tauto]. reflexivity.
  - (* If *) destruct ( beval st be)  eqn:Dbe.
    + apply IHHeval; tauto.
    + apply IHHeval; tauto.
  - (* If_F *) destruct ( beval st be)  eqn:Dbe.
    + apply IHHeval; tauto.
    + apply IHHeval; tauto.
  - (* While *) apply IHHeval. simpl. tauto.
Qed.
(* /HIDE *)

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

Lemma ideal_unused_overwrite: forall P st ast b ds c st' ast' b' os X n,
  unused X c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  P |- <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os X n Hu H.
  induction H; simpl in Hu.
  - (* Skip *) econstructor.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    econstructor. rewrite aeval_unused_update; tauto.
  - (* Seq *)
    econstructor.
    + apply IHideal_eval1; tauto.
    + apply IHideal_eval2; tauto.
  - (* If *)
    rewrite <- beval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite beval_unused_update; [ | tauto].
    destruct ( beval st be) eqn:D; apply IHideal_eval; tauto.
  - (* If_F *)
    rewrite <- beval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite beval_unused_update; [ | tauto].
    destruct ( beval st be) eqn:D; apply IHideal_eval; tauto.
  - (* While *)
    econstructor. apply IHideal_eval. simpl; tauto.
  - (* ARead *)
    rewrite t_update_permute; [| tauto]. econstructor; [ | assumption].
    rewrite aeval_unused_update; tauto.
  - (* ARead_U *)
    rewrite t_update_permute; [| tauto]. econstructor; try assumption.
    rewrite aeval_unused_update; tauto.
  - (* AWrite *)
    econstructor; try assumption.
    + rewrite aeval_unused_update; tauto.
    + rewrite aeval_unused_update; tauto.
  - (* AWrite_U *)
    econstructor; try assumption.
    + rewrite aeval_unused_update; tauto.
    + rewrite aeval_unused_update; tauto.
Qed.

Lemma ideal_unused_update : forall P st ast b ds c st' ast' b' os X n,
  unused X c ->
  P |- <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)> ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(X !-> st X; st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os X n Hu Heval.
  eapply ideal_unused_overwrite with (X:=X) (n:=(st X)) in Heval; [| assumption].
  do 2 rewrite t_update_shadow in Heval. rewrite t_update_same in Heval. assumption.
Qed.

Lemma ideal_unused_update_rev : forall P st ast b ds c st' ast' b' os X n,
  unused X c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(X!-> st X; st', ast', b', os)> ->
  P |- <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os X n Hu H.
  eapply ideal_unused_overwrite in H; [| eassumption].
  rewrite t_update_shadow in H. eassumption.
Qed.

Definition sel_slh_ideal_prop (c: com) (ds :dirs) :Prop :=
  forall P st ast (b: bool) st' ast' b' os,
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ sel_slh P c ]=> <(st', ast', b', os)> ->
    P |- <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

Lemma sel_slh_ideal : forall c ds,
  sel_slh_ideal_prop c ds.
Proof.
  apply prog_size_ind. unfold sel_slh_ideal_prop.
  intros c ds IH P st ast b st' ast' b' os Hunused Hstb Heval.
  destruct c; simpl in *; inversion Heval; subst; clear Heval;
  try (destruct (P x); discriminate).
  - (* Skip *)
    rewrite t_update_same. apply Ideal_Skip.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    rewrite t_update_same.
    constructor. reflexivity.
  - (* Seq *)
    eapply Ideal_Seq.
    + apply IH in H1; try tauto.
      * eassumption.
      * prog_size_auto.
    + apply sel_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * prog_size_auto.
  (* IF *)
  - (* non-speculative *)
    destruct (beval st be) eqn:Eqnbe; inversion H10;
    inversion H1; subst; clear H10; clear H1; simpl in *.
    + apply IH in H11; try tauto.
      * replace (OBranch true) with (OBranch (beval st be))
          by (rewrite <- Eqnbe; reflexivity).
        apply Ideal_If. rewrite Eqnbe.
        rewrite Eqnbe in H11. rewrite t_update_same in H11. apply H11.
      * prog_size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
    + (* analog to true case *)
      apply IH in H11; try tauto.
      * replace (OBranch false) with (OBranch (beval st be))
          by (rewrite <- Eqnbe; reflexivity).
        apply Ideal_If. rewrite Eqnbe. rewrite Eqnbe in H11.
        rewrite t_update_same in H11. apply H11.
      * prog_size_auto.
      * rewrite t_update_eq. rewrite Eqnbe. assumption.
  - (* speculative *)
    destruct (beval st be) eqn:Eqnbe; inversion H10; inversion H1;
    subst; simpl in *; clear H10; clear H1; rewrite Eqnbe in H11.
    + replace (OBranch true) with (OBranch (beval st be))
         by (rewrite <- Eqnbe; reflexivity).
      apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * prog_size_auto.
    + (* analog to true case *)
      replace (OBranch false) with (OBranch (beval st be))
        by (rewrite <- Eqnbe; reflexivity).
      apply Ideal_If_F. rewrite Eqnbe. apply IH in H11; try tauto.
      * rewrite t_update_eq in H11.
        apply ideal_unused_update in H11; try tauto.
      * prog_size_auto.
  - (* While *)
    eapply Ideal_While.
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11; simpl in *.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl.
      apply Ideal_If.
      destruct (beval st be) eqn:Eqnbe.
      * inversion H12; subst; clear H12.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2; simpl in *.
        assert(Hwhile: <(st'1, ast'1, b'1, ds2)>
          =[ sel_slh P <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        do 2 rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13. rewrite t_update_same in H13.
          apply IH in H13; try tauto.
          - eassumption.
          - prog_size_auto. }
        { apply IH in Hwhile; auto.
          - eapply ideal_unused_update_rev; eauto.
          - prog_size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite t_update_eq. rewrite Eqnbe. assumption. }
      * inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqnbe. do 2 rewrite t_update_same.
        apply Ideal_Skip.
    + (* speculative; analog to non_speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl.
      apply Ideal_If_F.
      destruct (beval st be) eqn:Eqnbe.
      * inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqnbe. rewrite t_update_shadow. rewrite t_update_same.
        apply Ideal_Skip.
      * inversion H12; subst; clear H12.
        inversion H1; subst; clear H1.
        inversion H2; subst; clear H2; simpl in *.
        assert(Hwhile: <(st'1, ast'1, b'1, ds2)>
          =[ sel_slh P <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
        { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          replace os2 with (os2 ++ [])%list by (rewrite app_nil_r; reflexivity).
          eapply Spec_Seq; eassumption. }
        do 2 rewrite app_nil_r. eapply Ideal_Seq.
        { rewrite Eqnbe in H13.
          apply IH in H13; try tauto.
          - rewrite t_update_eq in H13.
            apply ideal_unused_update in H13; [| tauto].
            eassumption.
          - prog_size_auto. }
        { apply IH in Hwhile; auto.
          - rewrite Eqnbe in H13.
            apply IH in H13; try tauto.
            + apply ideal_unused_update_rev; eauto.
            + prog_size_auto.
          - prog_size_auto.
          - apply sel_slh_flag in H13; try tauto.
            rewrite Eqnbe. rewrite t_update_eq. reflexivity. }
  (* ARead *)
  - (* Spec_ARead; public *)
    destruct (P x) eqn:Heq; try discriminate H.
    injection H; intros; subst; clear H.
    inversion H1; clear H1; subst. rewrite <- app_nil_r in *.
    inversion H0; clear H0; subst; simpl in *.
    * (* Ideal_ARead *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      rewrite t_update_eq. simpl.
      rewrite <- Hstb at 1. rewrite t_update_same.
      replace ((if b' then 1 else 0) =? 1)%nat with (b' && P x)
        by (rewrite Heq; destruct b'; simpl; reflexivity).
       eapply Ideal_ARead; eauto.
    * (* Ideal_ARead_U *)
      rewrite t_update_neq; [| tauto]. rewrite Hstb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      simpl. rewrite <- Hstb at 1. rewrite t_update_same.
      replace (x !-> 0; st) with (x !-> if P x then 0 else nth i' (ast' a') 0; st)
        by (rewrite Heq; reflexivity).
      eapply Ideal_ARead_U; eauto.
  - (* Spec_ARead; secret*)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> nth (aeval st i) (ast' a) 0; st)
      with (x !-> if b' && P x then 0 else nth (aeval st i) (ast' a) 0; st)
        by (rewrite Heq; destruct b'; reflexivity).
    eapply Ideal_ARead; eauto.
  - (* Spec_Read_U *)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    replace (x !-> nth i' (ast' a') 0; st)
      with (x !-> if P x then 0 else nth i' (ast' a') 0; st)
        by (rewrite Heq; reflexivity).
    eapply Ideal_ARead_U; eauto.
  (* AWrite *)
  - (* Spec_Write *)
    rewrite t_update_same. apply Ideal_Write; tauto.
  - (* Spec_Write_U *)
    rewrite t_update_same. apply Ideal_Write_U; tauto.
Qed.

(** Finally, we use this to prove spec_ct_secure for sel_slh. *)

Theorem sel_slh_spec_ct_secure :
  forall P PA c st1 st2 ast1 ast2 st1' st2' ast1' ast2' b1' b2' os1 os2 ds,
    P ;; PA |-ct- c ->
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    <(st1, ast1, false, ds)> =[ sel_slh P c ]=> <(st1', ast1', b1', os1)> ->
    <(st2, ast2, false, ds)> =[ sel_slh P c ]=> <(st2', ast2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c st1 st2 ast1 ast2 st1' st2' ast1' ast2' b1' b2' os1 os2 ds
    Hwt Hunused Hs1b Hs2b Hequiv Haequiv Heval1 Heval2.
  eapply sel_slh_ideal in Heval1; try assumption.
  eapply sel_slh_ideal in Heval2; try assumption.
  eapply ideal_spec_ct_secure; eauto.
Qed.

(* HIDE *)
(* HIDE: The less useful for security direction of the idealized semantics being
   equivalent to [sel_slh]; easier to prove even for while, since it has the
   flavor of forwards compiler correctness (FCC). This becomes useful
   if we want to proof BCC by using FCC. *)

Lemma spec_seq_assoc3 : forall st ast b ds c1 c2 c3 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2); c3 ]=> <( st', ast', b', os )>.
Proof.
  intros st ast b ds c1 c2 c3 st' ast' b' os Heval.
  inversion Heval; subst; clear Heval. inversion H10; subst; clear H10.
  replace (os1++os0++os3)%list with ((os1++os0)++os3)%list
    by (rewrite app_assoc; reflexivity).
  replace (ds1++ds0++ds3)%list with ((ds1++ds0)++ds3)%list
    by (rewrite app_assoc; reflexivity).
  repeat eapply Spec_Seq; eassumption.
Qed.

Lemma spec_seq_assoc4 : forall st ast b ds c1 c2 c3 c4 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3; c4 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2; c3); c4 ]=> <( st', ast', b', os )>.
Proof.
  intros st ast b ds c1 c2 c3 c4 st' ast' b' os Heval.
  inversion Heval; subst; clear Heval. inversion H10; subst; clear H10.
  inversion H12; subst; clear H12.
  replace (ds1++ds0++ds2++ds4)%list with ((ds1++ds0++ds2)++ds4)%list
    by (do 2 rewrite <- app_assoc; reflexivity).
  replace (os1++os0++os2++os4)%list with ((os1++os0++os2)++os4)%list
    by (do 2 rewrite <- app_assoc; reflexivity).
  repeat eapply Spec_Seq; eassumption.
Qed.

Lemma spec_seq_skip_r : forall st ast b ds c st' ast' b' os,
  <(st, ast, b, ds)> =[ c; skip ]=> <(st', ast', b', os)> ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)>.
Proof.
  intros st ast b ds c st' ast' b' os Heval.
  rewrite <- (app_nil_r ds) in Heval.
  replace os with ([] ++ os)%list by reflexivity.
  inversion Heval; inversion H10; subst; simpl.
  do 2 rewrite app_nil_r in H1; subst.
  rewrite app_nil_r. assumption.
Qed.

Lemma ideal_sel_slh : forall P st ast b ds c st' ast' b' os,
  unused "b" c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  <("b" !-> (if b then 1 else 0); st, ast, b, ds)> =[ sel_slh P c ]=>
    <("b" !-> (if b' then 1 else 0); st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os Hunused Heval.
  induction Heval; simpl in *.
  - (* Skip *) constructor.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    econstructor. rewrite aeval_unused_update; tauto.
  - (* Seq *)
    econstructor.
      + eapply IHHeval1. tauto.
      + eapply IHHeval2. tauto.
  - (* If *)
    replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + (* true *)
      rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      econstructor.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
    + (* false ; provable in the same way as the true case *)
      rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
  - (* If_f ; provable in the same way as the If case *)
    replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If_F. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
    + rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
  - (* While (most difficult case) *)
    assert(G : b_unused "b" be /\
      (unused "b" c /\ b_unused "b" be /\ unused "b" c) /\ True) by tauto.
    specialize (IHHeval G). clear G.
    inversion IHHeval; clear IHHeval; subst.
    + (* no misspeculation in while execution (Spec_If) *)
      rewrite beval_unused_update in H10; [ | tauto].
      destruct (beval st be) eqn:Eqbeval.
      * (* true *)
        apply spec_seq_assoc4 in H10.
        inversion H10; subst.
        assert (L: ds2 = [] /\ os2 = []).
        { inversion H11; subst; auto. }
        destruct L; subst.
        replace (DStep::ds1++[])%list with ((DStep::ds1)++[])%list
          by (rewrite app_comm_cons; reflexivity).
        replace ([OBranch (beval ("b" !-> (if b then 1 else 0); st) be)] ++ os0 ++ [])%list
          with (([OBranch (beval ("b" !-> (if b then 1 else 0); st) be)] ++ os0) ++ [])%list
            by (rewrite <- app_assoc; reflexivity).
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc3. assumption.
      * (* false *)
        eapply spec_seq_skip_r in H10. inversion H10; subst.
        rewrite <- (app_nil_l [OBranch _ ]). rewrite <- (app_nil_r [DStep]). rewrite H6.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply Spec_Skip.
    + (* mispeculation in while execution (Spec_If_f) ;
         provable analog to the no misspeculation case *)
      rewrite beval_unused_update in H10; [ | tauto].
      destruct (beval st be) eqn:Eqbeval.
      * (* true *)
        eapply spec_seq_skip_r in H10. inversion H10; subst.
        rewrite <- (app_nil_l [OBranch _ ]). rewrite <- (app_nil_r [DForce]). rewrite H6.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If_F.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply Spec_Skip.
      * (* false *)
        apply spec_seq_assoc4 in H10.
        inversion H10; subst.
        assert (L: ds2 = [] /\ os2 = []).
        { inversion H11; subst; auto. }
        destruct L; subst.
        replace (DForce::ds1++[])%list with ((DForce::ds1)++[])%list
          by (rewrite app_comm_cons; reflexivity).
        replace ([OBranch (beval ("b" !-> (if b then 1 else 0); st) be)] ++ os0 ++ [])%list
          with (([OBranch (beval ("b" !-> (if b then 1 else 0); st) be)] ++ os0) ++ [])%list
            by (rewrite app_assoc; reflexivity).
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If_F.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc3. assumption.
  - (* ARead *)
    rewrite t_update_permute; [| tauto].
    destruct (P x) eqn:EqPx.
    + (* public *)
      rewrite <- (app_nil_r [DStep]); rewrite <- (app_nil_r [OARead _ _]).
      eapply Spec_Seq.
      * apply Spec_ARead; [| tauto]. rewrite aeval_unused_update; tauto.
      * destruct b eqn:Eqb; simpl.
        { (* speculating *)
          replace (x !-> 0; "b" !-> 1; st)
            with (x !-> aeval
                          (x !-> nth i (ast a) 0; "b" !-> 1; st)
                          <{{("b" = 1) ? 0 : x }}> ;
                  x !-> nth i (ast a) 0; "b" !-> 1; st).
          + eapply Spec_Asgn. reflexivity.
          + simpl. rewrite t_update_neq; [| tauto].
            rewrite t_update_eq; simpl.
            rewrite t_update_shadow.
            reflexivity. }
        { (* non speculating *)
          replace (x !-> nth i (ast a) 0; "b" !-> 0; st)
            with (x !-> aeval
                      (x !-> nth i (ast a) 0; "b" !-> 0; st)
                      <{{("b" = 1) ? 0 : x }}> ;
                  x !-> nth i (ast a) 0; "b" !-> 0; st)
              at 2.
            + eapply Spec_Asgn. reflexivity.
            + simpl. rewrite t_update_neq; [| tauto].
              do 2 rewrite t_update_eq; simpl.
              rewrite t_update_shadow.
              reflexivity. }
    + (* secret *)
      rewrite andb_false_r.
      eapply Spec_ARead; eauto.
      rewrite aeval_unused_update; tauto.
  - (* ARead_U *)
    rewrite t_update_permute; [| tauto].
    destruct (P x) eqn:EqPx.
    + (* public *)
      rewrite <- (app_nil_r [DLoad _ _]); rewrite <- (app_nil_r [OARead _ _]).
      eapply Spec_Seq.
      * apply Spec_ARead_U;  try tauto. rewrite aeval_unused_update; tauto.
      * replace (x !-> 0; "b" !-> 1; st)
          with (x !-> aeval
                        (x !-> nth i' (ast a') 0; "b" !-> 1; st)
                        <{{("b" = 1) ? 0 : x }}> ;
                x!-> nth i' (ast a') 0; "b" !-> 1; st).
        { eapply Spec_Asgn. reflexivity. }
        { simpl. rewrite t_update_neq; [| tauto].
          rewrite t_update_eq; simpl.
          rewrite t_update_shadow.
          reflexivity. }
    + (* secret *)
      eapply Spec_ARead_U; try tauto. rewrite aeval_unused_update; tauto.
  - (* AWrite *) constructor; try rewrite aeval_unused_update; tauto.
  - (* AWrite_U *) constructor; try rewrite aeval_unused_update; tauto.
Qed.

(* HIDE: Moving syntactic constraints about ds and os out of the conclusions of
   rules and into equality premises could make this proof script less
   verbose. Maybe just define "smart constructors" for that? *)

(** ** BCC by flipping the direction and using FCC. *)

(** To proof BCC by contraposition and using FCC, we need two additional properties:
      1. Totality for [ideal_eval] (see [ideal_total])
      2. Determinism for [spec_eval] (see [spec_eval_deterministic])  *)

(* The totality is not currently true, but could be made true by extending the final
   configurations with errors for wrong directions or out of bounds accesses. *)
Axiom ideal_total : forall P c st ast b ds, exists stt astt bb os,
  P |- <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>.

Lemma spec_eval_deterministic_gen : forall c st ast b ds1 ds2 stt1 astt1 bb1 os1 stt2 astt2 bb2 os2,
  <( st , ast , b , ds1 )> =[ c ]=> <( stt1 , astt1 , bb1 , os1 )> ->
  <( st , ast , b , ds2 )> =[ c ]=> <( stt2 , astt2 , bb2 , os2 )> ->
  (prefix ds1 ds2 \/ prefix ds2 ds1) ->
  stt1 = stt2 /\ astt1 = astt2 /\ bb1 = bb2 /\ os1 = os2 /\ ds1 = ds2.
Proof.
  intros c st ast b ds1 ds2 stt1 astt1 bb1 os1 stt2 astt2 bb2 os2 Heval1.
  generalize dependent os2; generalize dependent bb2;
  generalize dependent astt2; generalize dependent stt2;
  generalize dependent ds2.
  induction Heval1; intros ds2' stt2 astt2 bb2 os2' Heval2 Hpre;
  try (now inversion Heval2; subst; auto).
  - (* Spec_Seq *)
    inversion Heval2; subst.
    destruct Hpre as [Hpre | Hpre]; apply prefix_app in Hpre as L; destruct L as [Hds1 | Hds0].
    + apply IHHeval1_1 in H1; subst; auto.
      destruct H1 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst.
      apply IHHeval1_2 in H10; subst; auto.
      * destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
      * apply prefix_append_front in Hpre; left; auto.
    + apply IHHeval1_1 in H1; subst; auto.
      destruct H1 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst.
      apply IHHeval1_2 in H10; subst; auto.
      * destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
      * apply prefix_append_front in Hpre; left; auto.
    + apply IHHeval1_1 in H1; subst; auto.
      destruct H1 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst.
      apply IHHeval1_2 in H10; subst; auto.
      * destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
      * apply prefix_append_front in Hpre; right; auto.
    + apply IHHeval1_1 in H1; subst; auto.
      destruct H1 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst.
      apply IHHeval1_2 in H10; subst; auto.
      * destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
      * apply prefix_append_front in Hpre; right; auto.
  - (* Spec_If *)
    inversion Heval2; subst.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_cons in Hpre;
      apply IHHeval1 in H10; auto;
      destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
  - (* Spec_If_F *)
    inversion Heval2; subst.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_cons in Hpre;
      apply IHHeval1 in H10; auto;
      destruct H10 as [Hst [Hast [Hb [Hos Hds] ] ] ]; subst; auto.
  - (* Spec_ARead *)
    inversion Heval2; subst.
    * auto.
    * destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
  - (* Spec_ARead_U *)
    inversion Heval2; subst; auto.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      inversion Hpre; subst; auto.
  - (* Spec_Write *)
    inversion Heval2; subst.
    * auto.
    * destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
  - (* Spec_Write_U *)
    inversion Heval2; subst.
    * destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      discriminate Hpre.
    * destruct Hpre as [Hpre | Hpre]; apply prefix_heads in Hpre;
      inversion Hpre; subst; auto.
Qed.

Lemma spec_eval_deterministic : forall c st ast b ds stt1 astt1 bb1 os1 stt2 astt2 bb2 os2,
  <( st , ast , b , ds )> =[ c ]=> <( stt1 , astt1 , bb1 , os1 )> ->
  <( st , ast , b , ds )> =[ c ]=> <( stt2 , astt2 , bb2 , os2 )> ->
  stt1 = stt2 /\ astt1 = astt2 /\ bb1 = bb2 /\ os1 = os2.
Proof.
  intros c st ast b ds stt1 astt1 bb1 os1 stt2 astt2 bb2 os2 Heval1 Heval2.
  eapply spec_eval_deterministic_gen in Heval2; [| eapply Heval1 |].
  - tauto.
  - left; apply prefix_refl.
Qed.

Require Import ClassicalFacts.

Lemma decidability_ouput_tuple : forall (st st' : state) (ast ast' :astate)
  (b b' :bool) (os os' :obs),
  excluded_middle ->
  (st, ast, b, os) = (st', ast', b', os') \/ ~ ((st, ast, b, os) = (st', ast', b', os')).
Proof. auto. Qed.

Lemma sel_slh_ideal' : forall c P st ast (b:bool) ds st' ast' (b':bool) os,
  excluded_middle ->
  unused "b" c ->
  <("b"!-> (if b then 1 else 0); st, ast, b, ds)> =[ sel_slh P c ]=> <(st', ast', b', os)> ->
  P |- <("b"!-> (if b then 1 else 0); st, ast, b, ds)> =[ c ]=>
    <("b" !-> (if b then 1 else 0); st', ast', b', os)>.
Proof.
  intros c P st ast b ds st' ast' b' os Hexc Hunused Heval.
  assert (Ldet : forall st1 ast1 (b1 :bool) os1,
    ("b" !-> (if b1 then 1 else 0); st1, ast1, b1, os1) <> (st', ast', b', os)   ->
    ~ <("b" !-> (if b then 1 else 0); st, ast, b, ds )> =[ (sel_slh P c) ]=>
          <("b"!-> (if b1 then 1 else 0); st1, ast1, b1, os1 )> ).
    { intros st1 ast1 b1 os2 Hneq Hev.
          eapply spec_eval_deterministic in Hev; [| eapply Heval].
          destruct Hev as [ Hst [ Hast [ Hb Hos ] ] ]. subst. eauto. }
  assert(LFcc : forall st1 ast1 (b1 : bool) os1,
    ("b" !-> (if b1 then 1 else 0); st1, ast1, b1, os1) <> (st', ast', b', os)   ->
    ~ P |- <( st, ast, b, ds )> =[ c ]=> <(st1, ast1, b1, os1 )>).
    { intros st1 ast1 b1 os2 Hneq Hev.
      eapply Ldet; [apply Hneq |].
      apply ideal_sel_slh; auto. }
  assert(Ltot: exists st1 ast1 b1 os1,
    P |- <(st, ast, b, ds )> =[ c ]=> <(st1, ast1, b1, os1 )> ).
    { eapply ideal_total. }
  destruct Ltot as [ st1 [ ast1 [ b1 [ os1 Hev1 ] ] ] ].
  assert (Leq : ("b" !-> (if b1 then 1 else 0); st1, ast1, b1, os1) = (st', ast', b', os) ).
    { destruct (decidability_ouput_tuple ("b" !-> (if b1 then 1 else 0); st1) st' ast1 ast'
        b1 b' os1 os ); auto.
      apply LFcc in H. apply H in Hev1. destruct Hev1. }
  inversion Leq. subst. rewrite t_update_shadow.
  eapply ideal_unused_overwrite in Hev1; eauto.
Qed.

(* /HIDE *)

(* TERSE: /HIDEFROMHTML *)

(** * Speculative constant-time interpreter *)

(* TERSE: HIDEFROMHTML *)
Module SpecCTInterpreter.

(** Since the construction of directions for proofs of examples is very time consuming,
    we want to have an alternative. This alternative is an interpreter which, if it is sound
    can be used to easily proof examples. *)

Definition prog_st : Type :=  state * astate * bool * dirs * obs.

Inductive output_st (A : Type): Type :=
| OST_Error : output_st A
| OST_OutOfFuel : output_st A
| OST_Finished : A -> prog_st -> output_st A.

Definition evaluator (A : Type): Type := prog_st -> (output_st A).
Definition interpreter : Type := evaluator unit.

Definition ret {A : Type} (value : A) : evaluator A :=
  fun (pst: prog_st) => OST_Finished A value pst.

Definition bind {A : Type} {B : Type} (e : evaluator A) (f : A -> evaluator B): evaluator B :=
  fun (pst: prog_st) =>
    match e pst with
    | OST_Finished _ value (st', ast', b', ds', os1)  =>
        match (f value) (st', ast', b', ds', os1) with
        | OST_Finished _ value (st'', ast'', b'', ds'', os2) =>
            OST_Finished B value (st'', ast'', b'', ds'', os2)
        | ret => ret
        end
    | OST_Error _ => OST_Error B
    | OST_OutOfFuel _ => OST_OutOfFuel B
    end.

Notation "e >>= f" := (bind e f) (at level 58, left associativity).
Notation "e >> f" := (bind e (fun _ => f)) (at level 58, left associativity).

(** ** Funtions for execution of com instructions *)

Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  fun (pst : prog_st) =>
    let
      '(st, _, _, _, _) := pst
    in
      ret (st name) pst.

Definition set_var (name : string) (value : nat) : interpreter :=
  fun (pst: prog_st) =>
    let
      '(st, ast, b, ds, os) := pst
    in
      let
        new_st := (name !-> value; st)
      in
        finish (new_st, ast, b, ds, os).

Definition get_arr (name : string): evaluator (list nat) :=
  fun (pst: prog_st) =>
    let
      '(_, ast, _, _, _) := pst
    in
      ret (ast name) pst.

Definition set_arr (name : string) (value : list nat) : interpreter :=
  fun (pst : prog_st) =>
    let '(st, ast, b, ds, os) := pst in
    let new_ast := (name !-> value ; ast) in
    finish (st, new_ast, b, ds, os).

Definition start_speculating : interpreter :=
  fun (pst : prog_st) =>
    let '(st, ast, _, ds, os) := pst in
    finish (st, ast, true, ds, os).

Definition is_speculating : evaluator bool :=
  fun (pst : prog_st) =>
    let '(_, _, b, _, _) := pst in
    ret b pst.

Definition eval_aexp (a : aexp) : evaluator nat :=
  fun (pst: prog_st) =>
    let '(st, _, _, _, _) := pst in
    let v := aeval st a in
    ret v pst.

Definition eval_bexp (be : bexp) : evaluator bool :=
  fun (pst : prog_st) =>
    let '(st, _, _, _, _) := pst in
    let v := beval st be in
    ret v pst.

Definition raise_error : interpreter :=
  fun _ => OST_Error unit.

Definition observe (o : observation) : interpreter :=
  fun (pst : prog_st) =>
    let '(st, ast, b, ds, os) := pst in
    OST_Finished unit tt (st, ast, b, ds, (os ++ [o])%list).

Definition fetch_direction : evaluator (option direction) :=
  fun (pst : prog_st) =>
    let '(st, ast, b, ds, os) := pst in
    match ds with
    | d::ds' =>
        ret (Some d) (st, ast, b, ds', os)
    | [] => ret None (st, ast, b, [], os)
    end.

(** ** The speculative constant-time interpreter *)

Fixpoint spec_eval_engine_aux (fuel : nat) (c : com) : interpreter :=
  match fuel with
  | O => fun _ => OST_OutOfFuel unit
  | S fuel =>
    match c with
    | <{ skip }> => finish
    | <{ x := e }> => eval_aexp e >>= fun v => set_var x v
    | <{ c1 ; c2 }> =>
        spec_eval_engine_aux fuel c1 >>
        spec_eval_engine_aux fuel c2
    | <{ if be then ct else cf end }> =>
        eval_bexp be >>= fun bool_value => observe (OBranch bool_value) >> fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if bool_value then spec_eval_engine_aux fuel ct
              else spec_eval_engine_aux fuel cf
          | Some DForce =>
              start_speculating >>
              if bool_value then spec_eval_engine_aux fuel cf
              else spec_eval_engine_aux fuel ct
          | _ => raise_error
          end
    | <{ while be do c end }> =>
        spec_eval_engine_aux fuel <{if be then c; while be do c end else skip end}>
    | <{ x <- a[[ie]] }> =>
        eval_aexp ie >>= fun i => observe (OARead a i) >> get_arr a >>=
        fun arr_a => is_speculating >>= fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_var x (nth i arr_a 0)
              else raise_error
          | Some (DLoad a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat && (i' <? List.length arr_a')%nat && b then
                  set_var x (nth i' arr_a' 0)
                else raise_error
          | _ => raise_error
          end
    | <{ a[ie] <- e }> =>
        eval_aexp ie >>= fun i => observe (OAWrite a i) >> get_arr a >>=
        fun arr_a => eval_aexp e >>= fun n => is_speculating >>= fun b => fetch_direction >>=
        fun dop =>
          match dop with
          | Some DStep =>
              if (i <? List.length arr_a)%nat then set_arr a (upd i arr_a n)
              else raise_error
          | Some (DStore a' i') =>
              get_arr a' >>= fun arr_a' =>
                if negb (i <? List.length arr_a)%nat && (i' <? List.length arr_a')%nat && b then
                  set_arr a' (upd i' arr_a' n)
                else raise_error
          | _ => raise_error
          end
    end
end.

(* In principle, could also define spec_eval_engine without fuel,
   but in practice it's quite complicated: *)
(* Program Fixpoint spec_eval_engine_aux (fuel : nat) (c : com) (ds : dirs) :  *)
(*   state * astate * bool -> ds':dirs{length ds' <= length ds} * output_st {measure (com_size c + length ds)} *)
(* ... *)
(*     | <{ c1 ; c2 }> => *)
(*         let '(ds', k) := spec_eval_engine_aux ds c1 in *)
(*         k >> spec_eval_engine_aux ds' c2 *)

Definition compute_fuel (c :com) (ds :dirs) :=
  (* Reducing the fuel in the base cases of com_size does not break
     any proofs, but some of the tests below need a bit more to finish
     reducing (adding 2 is enough) *)
  2 +
    match ds with
    | [] => com_size c
    | _ => length ds * com_size c
    end.

Definition spec_eval_engine (c : com) (st : state) (ast : astate) (b : bool) (ds : dirs)
      : option (state * astate * bool * obs) :=
    match spec_eval_engine_aux (compute_fuel c ds) c (st, ast, b, ds, []) with
    | OST_Finished _ _ (st', ast', b', ds', os) =>
        if ((length ds') =? 0)%nat then Some (st', ast', b', os)
        else None
    | _ => None
    end.

(* HIDE *)

(* Testing *)

Definition st_test :state := (X!-> 1; _!-> 0).
Definition ast_test :astate := (AP!->[1]; AS!-> [1;2]; _!-> []).

Example test_interpreter_1 : (spec_eval_engine <{{skip}}> st_test ast_test false []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_2 : (spec_eval_engine <{{skip}}> st_test ast_test true []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_3 : (spec_eval_engine <{{Y := 2}}> st_test ast_test false []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_4 : (spec_eval_engine <{{Y := 2}}> st_test ast_test true []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_5 : (spec_eval_engine <{{Y := 2; Z := 3}}> st_test ast_test false []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_6 : (spec_eval_engine <{{Y := 2; Z := 3}}> st_test ast_test true []) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_7 : (spec_eval_engine <{{if X <= 5 then skip else skip end}}> st_test ast_test false [DStep]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_8 : (spec_eval_engine <{{if X <= 5 then skip else skip end}}> st_test ast_test true [DForce]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_9 : (spec_eval_engine <{{while X <= 1 do X := X + 1 end}}> st_test ast_test false [DStep; DStep]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_10 : (spec_eval_engine <{{while X <= 1 do X := X + 1 end}}> st_test ast_test true [DStep; DStep]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_11 : (spec_eval_engine <{{while X <= 1 do X := X + 1 end}}> st_test ast_test false [DForce]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_12 : (spec_eval_engine <{{while X <= 1 do X := X + 1 end}}> st_test ast_test true [DForce]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_13 : (spec_eval_engine <{{ Y <- AP[[0]] }}> st_test ast_test false [DStep]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_14 : (spec_eval_engine <{{Y <- AP[[1]]}}> st_test ast_test true [DLoad AS 1]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

Example test_interpreter_15 : (spec_eval_engine <{{AP[0] <- 1}}> st_test ast_test false [DStep]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.
Example test_interpreter_16 : (spec_eval_engine <{{AP[1] <- 1}}> st_test ast_test true [DStore AS 1]) <> None.
Proof. unfold spec_eval_engine; simpl; intro H; inversion H. Qed.

(* /HIDE *)

(** ** Soundness of the interpreter*)

Lemma ltb_reflect : forall n m :nat,
  reflect (n < m) (n <? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite ltb_lt. reflexivity.
Qed.

Lemma eqb_reflect: forall n m :nat,
  reflect (n = m ) (n =? m)%nat.
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Lemma spec_eval_engine_aux_sound : forall n c st ast b ds os st' ast' b' ds' os' u,
  spec_eval_engine_aux n c (st, ast, b, ds, os)
    = OST_Finished unit u (st', ast', b', ds', os') ->
  (exists dsn osn,
  (dsn++ds')%list = ds /\ (os++osn)%list = os' /\
      <(st, ast, b, dsn)> =[ c ]=> <(st', ast', b', osn)> ).
Proof.
  induction n as [| n' IH]; intros c st ast b ds os st' ast' b' ds' os' u Haux;
  simpl in Haux; [discriminate |].
  destruct c as [| X e | c1 c2 | be ct cf | be cw | X a ie | a ie e ] eqn:Eqnc;
  unfold ">>=" in Haux; simpl in Haux.
  - (* Skip *)
    inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Skip.
  - (* Asgn *)
    simpl in Haux. inversion Haux; subst.
    exists []; exists []; split;[| split].
    + reflexivity.
    + rewrite app_nil_r. reflexivity.
    + apply Spec_Asgn. reflexivity.
  - destruct (spec_eval_engine_aux _ c1 _) eqn:Hc1;
    try discriminate; simpl in Haux.
    destruct p as [ [ [ [stm astm] bm] dsm] osm]; simpl in Haux.
    destruct (spec_eval_engine_aux _ c2 _) eqn:Hc2;
    try discriminate; simpl in Haux.
    destruct p as [ [ [ [stt astt] bt] dst] ost]; simpl in Haux.
    apply IH in Hc1. destruct Hc1 as [ds1 [ os1 [Hds1 [Hos1 Heval1] ] ] ].
    apply IH in Hc2. destruct Hc2 as [ds2 [ os2 [Hds2 [Hos2 Heval2] ] ] ].
    inversion Haux; subst. exists (ds1++ds2)%list; exists (os1++os2)%list;
    split; [| split].
    + rewrite <- app_assoc. reflexivity.
    + rewrite <- app_assoc. reflexivity.
    + eapply Spec_Seq; eauto.
  - (* IF *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (beval st be) eqn:Eqnbe.
      * destruct (spec_eval_engine_aux _ ct _ ) eqn:Hct; try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt astt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DStep :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { rewrite <- Eqnbe. apply Spec_If. rewrite Eqnbe. apply Heval. }
      * destruct (spec_eval_engine_aux _ cf _ ) eqn:Hcf; try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt astt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DStep :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { rewrite <- Eqnbe. apply Spec_If. rewrite Eqnbe. apply Heval. }
    + (* DForce *)
      destruct (beval st be) eqn:Eqnbe.
      * destruct (spec_eval_engine_aux _ cf _ ) eqn:Hcf; try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt astt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hcf.
        destruct Hcf as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DForce :: dst); exists ([OBranch true]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { rewrite <- Eqnbe. apply Spec_If_F. rewrite Eqnbe. apply Heval. }
      * destruct (spec_eval_engine_aux _ ct _ ) eqn:Hct; try discriminate; simpl in Haux.
        destruct p as [ [ [ [stt astt] bt] dst] ost]; simpl in Haux.
        inversion Haux; subst. apply IH in Hct.
        destruct Hct as [dst [ ost [Hds [Hos Heval] ] ] ].
        exists (DForce :: dst); exists ([OBranch false]++ost)%list; split;[| split].
        { simpl. rewrite Hds. reflexivity. }
        { rewrite app_assoc. rewrite Hos. reflexivity. }
        { rewrite <- Eqnbe. apply Spec_If_F. rewrite Eqnbe. apply Heval. }
  - (* While *)
    apply IH in Haux. destruct Haux as [dst [ ost [Hds [Hos Heval] ] ] ].
    exists dst; exists ost; split; [| split]; eauto.
    apply Spec_While. apply Heval.
  - (* ARead *)
    destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
    destruct d eqn:Eqnd; try discriminate; simpl in Haux.
    + (* DStep *)
      destruct (aeval st ie <? Datatypes.length (ast a))%nat eqn:Eqnindex; try discriminate.
      destruct (observe (OARead a (aeval st ie)) (st, ast, b, ds_tl, os)) eqn:Eqbobs; try discriminate;
      simpl in Haux. inversion Haux; subst.
      eexists [DStep]; eexists [OARead a (aeval st ie)]; split;[| split]; try reflexivity.
      eapply Spec_ARead; eauto. destruct (ltb_reflect (aeval st ie) (length (ast' a))) as [Hlt | Hgeq].
      * apply Hlt.
      * discriminate.
    + (* DForce *)
      destruct (negb (aeval st ie <? Datatypes.length (ast a))%nat) eqn:Eqnindex1;
      destruct ((i <? Datatypes.length (ast a0))%nat) eqn:Eqnindex2;
      destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
      eexists [DLoad a0 i ]; eexists [OARead a (aeval st ie)]; split;[| split]; try reflexivity.
      eapply Spec_ARead_U; eauto.
      * destruct (ltb_reflect (aeval st ie) (length (ast' a))) as [Hlt | Hgeq].
        { discriminate. }
        { apply not_lt in Hgeq. apply Hgeq. }
      * destruct (ltb_reflect i (length (ast' a0))) as [Hlt | Hgeq].
        { apply Hlt. }
        { discriminate. }
  - (* AWrite *)
  destruct ds as [| d ds_tl] eqn:Eqnds; simpl in Haux; try discriminate.
  destruct d eqn:Eqnd; try discriminate; simpl in Haux.
  + (* DStep *)
    destruct ((aeval st ie <? Datatypes.length (ast a))%nat) eqn:Eqnindex; try discriminate.
    destruct (observe (OAWrite a (aeval st ie)) (st, ast, b, ds_tl, os)) eqn:Eqbobs; try discriminate;
    simpl in Haux. inversion Haux; subst.
    eexists [DStep]; eexists [OAWrite a (aeval st' ie)]; split;[| split]; try reflexivity.
    eapply Spec_Write; eauto. destruct (ltb_reflect (aeval st' ie) (length (ast a))) as [Hlt | Hgeq].
    * apply Hlt.
    * discriminate.
  + (* DForce *)
    destruct  (negb (aeval st ie <? Datatypes.length (ast a))%nat) eqn:Eqnindex1;
    destruct (i <? Datatypes.length (ast a0))%nat eqn:Eqnindex2;
    destruct b eqn:Eqnb; try discriminate; simpl in Haux. inversion Haux; subst.
    eexists [DStore a0 i]; eexists [OAWrite a (aeval st' ie)]; split;[| split]; try reflexivity.
    eapply Spec_Write_U; eauto.
    * destruct (ltb_reflect (aeval st' ie) (length (ast a))) as [Hlt | Hgeq].
      { discriminate. }
      {  apply not_lt in Hgeq. apply Hgeq. }
    * destruct (ltb_reflect i (length (ast a0))) as [Hlt | Hgeq].
      { apply Hlt. }
      { discriminate. }
Qed.

Theorem spec_eval_engine_sound: forall c st ast b ds st' ast' b' os',
  spec_eval_engine c st ast b ds = Some (st', ast', b', os') ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os')> .
Proof.
  intros c st ast b ds st' ast' b' os' Hengine.
  unfold spec_eval_engine in Hengine.
  destruct (spec_eval_engine_aux _ c _) eqn:Eqnaux;
  try discriminate. destruct p as [ [ [ [stt astt] bt] dst] ost].
  destruct ((Datatypes.length dst =? 0)%nat) eqn:Eqnds; try discriminate.
  apply spec_eval_engine_aux_sound in Eqnaux.
  destruct Eqnaux as [dsn [osn [Hdsn [Hosn Heval] ] ] ].
  inversion Hengine; subst. rewrite app_nil_l.
  destruct (eqb_reflect (length dst) 0) as [Heq | Hneq].
  + apply length_zero_iff_nil in Heq. rewrite Heq. rewrite app_nil_r. apply Heval.
  + discriminate.
Qed.

Definition spec_insecure_prog_2 :=
  <{{ X := 0;
      Y := 0;
      while Y <= 2 do
        Z <- AP[[Y]];
        X := X + Z;
        Y := Y + 1
      end;
      if X <= 42 then W := 1 else W := 0 end  }}> .

Example spec_insecure_prog_2_is_ct_and_spec_insecure :
  exists P PA,
    P ;; PA |-ct- spec_insecure_prog_2 /\ ~ (spec_ct_secure P PA spec_insecure_prog_2) .
Proof.
  exists (X!-> public; Y!-> public; Z!-> public; _ !-> secret).
  exists  (AP!-> public; AS!-> secret; _ !-> public).
  split; unfold spec_insecure_prog.
  - repeat econstructor;
    replace (public) with (join public public) at 4 by reflexivity;
    repeat constructor.
  - remember (_ !-> 0) as st.
    remember (AP!-> [1;2;3]; AS!-> [40;41;42;43]; _ !-> []) as ast1.
    remember (AP!-> [1;2;3]; AS!-> [4;5;6;7]; _ !-> []) as ast2.
    remember ([DStep; DStep; DStep; DStep; DStep; DStep; DForce; DLoad AS 3; DStep; DStep]) as ds.
    intros Hsecure.
    assert (L: exists stt1 astt1 bt1 os1 stt2 astt2 bt2 os2,
      <(st, ast1, false, ds )> =[ spec_insecure_prog_2 ]=> <( stt1, astt1, bt1, os1)> /\
      <(st, ast2, false, ds )> =[ spec_insecure_prog_2 ]=> <( stt2, astt2, bt2, os2)> /\
      os1 <> os2 ).
    { eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      split; [| split].
      - apply spec_eval_engine_sound. unfold spec_insecure_prog_2, spec_eval_engine;
        subst; simpl; reflexivity.
      - apply spec_eval_engine_sound. unfold spec_insecure_prog_2, spec_eval_engine;
        subst; simpl; reflexivity.
      - intros Contra; inversion Contra. }
    destruct L as [stt1 [astt1 [bt1 [os1 [stt2 [astt2 [bt2 [os2 [Heval1 [Heval2 Hneq] ] ] ] ] ] ] ] ] ].
    eapply Hsecure in Heval1; eauto.
    + apply pub_equiv_refl.
    + intros x Hx. destruct (String.eqb_spec "AP" x) as [HeqAP | HneqAP];
      destruct (String.eqb_spec "AS" x) as [HeqAS | HneqAS].
      * subst. do 2 rewrite t_update_eq. reflexivity.
      * subst. do 2 rewrite t_update_eq. reflexivity.
      * subst. rewrite t_update_neq in Hx; [| assumption].
        rewrite t_update_eq in Hx. discriminate.
      * subst. do 4 (rewrite t_update_neq; [| assumption]). reflexivity.
Qed.

End SpecCTInterpreter.
