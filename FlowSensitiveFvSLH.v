(** * Flow-Sensitive, Flexible Value SLH *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT UltimateSLH_optimized FiSLH FvSLH.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
Set Default Goal Selector "!".

(** * Flow-sensitive IFC tracking for flex_slh *)

(* Since we want to apply flex_slh to all programs, without rejecting anything
   as "ill-typed", we implement flow-sensitive static IFC tracking: *)

Inductive acom : Type :=
  | ASkip
  | AAsgn (x : string) (e : aexp)
  | ASeq (c1 c2 : acom) (P : pub_vars) (PA : pub_arrs)
  | AIf (be : bexp) (lbe : label) (c1 c2 : acom)
  | AWhile (be : bexp) (lbe : label) (c : acom) (P : pub_vars) (PA : pub_arrs)
  | AARead (x : string) (lx : label) (a : string) (i : aexp)  (li : label)
  | AAWrite (a : string) (i : aexp) (li : label) (e : aexp)
  | ABranch (lbl:label) (c:acom).

Declare Custom Entry acom.

Notation "'<[' e ']>'" := e (at level 0, e custom acom at level 99) : com_scope.
Notation "( x )" := x (in custom acom, x at level 99) : com_scope.
Notation "x" := x (in custom acom at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom acom at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Notation "'skip'"  :=
  ASkip (in custom acom at level 0) : com_scope.
Notation "x := y"  :=
  (AAsgn x y)
    (in custom acom at level 0, x constr at level 0,
      y custom acom at level 85, no associativity) : com_scope.
Notation "x ; '@(' P ',' PA ')' y" :=
  (ASeq x y P PA)
    (in custom acom at level 90, right associativity) : com_scope.
Notation "'if' x '@' lbe 'then' y 'else' z 'end'" :=
  (AIf x lbe y z)
    (in custom acom at level 89, x custom acom at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x '@' lbe 'do' y '@(' P ',' PA ')' 'end'" :=
  (AWhile x lbe y P PA)
    (in custom acom at level 89, x custom acom at level 99, y at level 99) : com_scope.
Notation "x '@@' lx '<-' a '[[' i '@' li ']]'"  :=
  (AARead x lx a i li)
     (in custom acom at level 0, x constr at level 0,
      a at level 85, i custom acom at level 85, no associativity) : com_scope.
Notation "a '[' i '@' li  ']'  '<-' e"  :=
  (AAWrite a i li e)
     (in custom acom at level 0, a constr at level 0,
      i custom acom at level 0, e custom acom at level 85,
         no associativity) : com_scope.
Notation "'branch' l c"  :=
  (ABranch l c) (in custom acom at level 91, l constr at level 0, c custom acom) : com_scope.

Fixpoint erase (ac:acom) : com :=
  match ac with
  | <[ skip ]> => <{skip}>
  | <[ X := ae ]> => <{X := ae}>
  | <[ ac1 ;@(P, PA) ac2 ]> => <{ erase ac1; erase ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> => <{ if be then erase ac1
                                                      else erase ac2 end }>
  | <[ while be @ lbe do ac1 @(P,PA) end ]> => <{ while be do erase ac1 end }>
  | <[ X@@lx <- a[[i@li]] ]> => <{ X <- a[[i]] }>
  | <[ a[i@li] <- e ]> => <{ a[i] <- e }>
  | <[ branch l ac1 ]> => <{ erase ac1 }>
  end.

Definition join_pub_vars (P1 P2: pub_vars) : pub_vars :=
  fun x => join (P1 x) (P2 x).

Definition less_precise (P1 P2:pub_vars) : Prop :=
  forall x, can_flow (P2 x) (P1 x) = true.

Lemma pub_equiv_less_precise : forall (P P':pub_vars) {A:Type} (x1 x2:total_map A),
  pub_equiv P x1 x2 ->
  less_precise P' P ->
  pub_equiv P' x1 x2.
Proof.
  intros. intros x P'x. unfold less_precise, can_flow in H0. specialize (H0 x). apply H.
  now rewrite P'x, orb_false_r in H0.
Qed.

Lemma can_flow_trans : forall a b c, can_flow a b = true -> can_flow b c = true -> can_flow a c = true.
Proof.
  intros a b c H1 H2. destruct a, b, c; tauto.
Qed.
Lemma can_flow_refl : forall a, can_flow a a = true.
Proof.
  now destruct a.
Qed.

Lemma less_precise_refl : forall P, less_precise P P.
Proof. intros P x. now destruct (P x). Qed.

Lemma less_precise_trans : forall P P' P'',
  less_precise P' P ->
  less_precise P'' P' ->
  less_precise P'' P.
Proof.
  intros P P' P'' H1 H2 x.
  specialize (H1 x). specialize (H2 x).
  eapply can_flow_trans; eassumption.
Qed.

Lemma filter_less_precise_nil P P' l:
  less_precise P' P ->
  filter P l = nil -> filter P' l = nil.
Proof.
  intros. induction l.
  - reflexivity.
  - simpl in *. destruct (P a) eqn: HPa; [congruence|].
    specialize (H a). rewrite HPa in H. destruct (P' a); simpl in H; [congruence | tauto].
Qed.

Lemma less_precise_join_l : forall P1 P2,
  less_precise (join_pub_vars P1 P2) P1.
Proof.
  intros P1 P2 x. unfold join_pub_vars. now destruct (P1 x).
Qed.
Lemma less_precise_join_r : forall P1 P2,
  less_precise (join_pub_vars P1 P2) P2.
Proof.
  intros P1 P2 x. unfold join_pub_vars. now destruct (P1 x), (P2 x).
Qed.

Lemma join_pub_vars_eq P: join_pub_vars P P = P.
Proof.
  apply functional_extensionality.
  intros. unfold join_pub_vars. now destruct (P x).
Qed.

Lemma join_pub_vars_assoc P P' P'':
  join_pub_vars (join_pub_vars P P') P'' = join_pub_vars P (join_pub_vars P' P'').
Proof.
  apply functional_extensionality.
  intros. unfold join_pub_vars. now destruct (P x), (P' x), (P'' x).
Qed.

Lemma join_pub_vars_less_precise P P':
  join_pub_vars P P' = P <-> less_precise P P'.
Proof.
  split.
  - intros H x. rewrite <- H. unfold join_pub_vars. now destruct (P' x), (P x).
  - intros H. apply functional_extensionality. unfold join_pub_vars.
    intro x. specialize (H x). now destruct (P x), (P' x).
Qed.

Definition str_nodup := nodup string_dec.

Lemma filter_nodup {A} dec P (l: list A):
  filter P (nodup dec l) = nodup dec (filter P l).
Proof.
  induction l.
  - reflexivity.
  - simpl. destruct (in_dec dec a l).
    + destruct (P a) eqn: Heq2.
      * rewrite IHl. assert (In a (filter P l)) by now apply filter_In.
        simpl. now destruct (in_dec dec a (filter P l)).
      * assumption.
    + simpl. destruct (P a).
      * assert (~ In a (filter P l)) by now intros Hin%filter_In. simpl.
        destruct (in_dec dec a (filter P l)). 1: contradiction. now f_equal.
      * assumption.
Qed.

Lemma nodup_nil {A} dec (l: list A):
  nodup dec l = [] <-> l = [].
Proof.
  split.
  - induction l.
    + reflexivity.
    + simpl. destruct (in_dec dec a l); [|congruence]. intros. specialize (IHl H). subst. contradiction.
  - intros ->. reflexivity.
Qed.


Fixpoint assigned_vars c :=
  match c with
  | <{ skip }> | <{ _ [_] <- _ }> => []
  | <{ X := _ }> | <{ X <- _ [[_]] }> => [X]
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_vars c1 ++ assigned_vars c2)
  | <{ while _ do c end }> => assigned_vars c
  end.

Fixpoint assigned_arrs c :=
  match c with
  | <{ skip }>
  | <{ _ := _ }>
  | <{ _ <- _ [[_]] }> => []
  | <{ c1; c2 }>
  | <{ if _ then c1 else c2 end }> => str_nodup (assigned_arrs c1 ++ assigned_arrs c2)
  | <{ while _ do c end }> => assigned_arrs c
  | <{ a[_] <- _ }> => [a]
  end.

Definition list_eqb l1 l2 := if list_eq_dec string_dec l1 l2 then true else false.

Fixpoint static_tracking_while (static_tracking : pub_vars -> pub_arrs -> label -> (acom * pub_vars * pub_arrs))
      (P : pub_vars) (PA : pub_arrs) (pc : label) (i : nat) (be : bexp) (vars arrs pvars parrs : list string) :=
  let lbe := label_of_bexp P be in
  let '(ac, P1, PA1) := static_tracking P PA (join pc lbe) in
  let P1 := join_pub_vars P P1 in
  let PA1 := join_pub_vars PA PA1 in
  let pvars1 := filter P1 vars in
  let parrs1 := filter PA1 arrs in
  let stop := (list_eqb pvars pvars1) && (list_eqb parrs parrs1) in
    (* Stopping if a fixpoint was already reached *)
  match i, stop with
  | _, true | 0, _ => (P1, PA1, lbe, ac)
  | S i, false => static_tracking_while static_tracking P1 PA1 pc i be vars arrs pvars1 parrs1
  end.

Fixpoint static_tracking (c:com) (P:pub_vars) (PA:pub_arrs) (pc:label)
  : (acom*pub_vars*pub_arrs) :=
  match c with
  | <{ skip }> => (<[skip]>, P, PA)
  | <{ x := ae }> => (<[x := ae]>, x !-> (join pc (label_of_aexp P ae)); P, PA)
  | <{ c1; c2 }> => let '(ac1, P1, PA1) := static_tracking c1 P PA pc in
                    let '(ac2, P2, PA2) := static_tracking c2 P1 PA1 pc in
                     (<[ ac1;@(P1, PA1) ac2 ]>, P2, PA2)
  | <{ if be then c1 else c2 end }> =>
      let lbe := label_of_bexp P be in
      let '(ac1, P1, PA1) := static_tracking c1 P PA (join pc lbe) in
      let '(ac2, P2, PA2) := static_tracking c2 P PA (join pc lbe) in
      (<[ if be@lbe then ac1 else ac2 end ]>, join_pub_vars P1 P2, join_pub_vars PA1 PA2)
  | <{ while be do c1 end }> =>
      let vars := assigned_vars c1 in
      let arrs := assigned_arrs c1 in
      let pvars := filter P vars in
      let parrs := filter PA arrs in
      let max_iters := length vars + length arrs in
      let '(P', PA', lbe, ac1) := static_tracking_while (static_tracking c1) P PA pc max_iters be vars arrs pvars parrs in
      (<[ while be@lbe do ac1 @(P', PA') end ]>, P', PA')
  | <{ X <- a[[i]] }> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (PA a)) in
      (<[ X@@lx <- a[[i@li]] ]>, X !-> lx; P, PA)
  | <{ a[i] <- e }> =>
      let li := label_of_aexp P i in
      let la := join (PA a) (join pc (join li (label_of_aexp P e))) in
      (<[ a[i@li] <- e ]>, P, a !-> la; PA)
  end.

Lemma static_tracking_while_invariant : forall ac P' PA' pc' f P PA pc i be vars arrs pvars parrs (R : acom -> Prop),
  (forall ac' P PA P1 PA1 pc, f P PA pc = (ac', P1, PA1) -> R ac') ->
  static_tracking_while f P PA pc i be vars arrs pvars parrs = (P', PA', pc', ac) ->
  R ac.
Proof.
  intros until i. revert f P PA pc P' PA' pc'. induction i; simpl; intros.
  + destruct (f P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq1.
    eapply H. rewrite Heq1.
    destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)); now invert H0.
  + destruct (f P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq.
    destruct (list_eqb pvars (filter (join_pub_vars P P1) vars) && list_eqb parrs (filter (join_pub_vars PA PA1) arrs)).
    - invert H0. eapply H, Heq.
    - eapply IHi; eassumption.
Qed.

Fixpoint pc_of_acom pc c :=
  match c with
  | <[ branch pc' _ ]> => pc'
  | <[ c1;@(_,_) c2 ]> => pc_of_acom (pc_of_acom pc c1) c2
  | _ => pc
  end.

Fixpoint branch_free ac :=
  match ac with 
  | <[ skip ]> | <[ _ := _ ]> | <[ _@@_ <-_[[_@_]] ]> | <[_[_@_] <- _]> => True
  | <[ ac1;@(_,_) ac2]> => branch_free ac1 /\ branch_free ac2
  | <[ if _@_ then ac1 else ac2 end ]> => branch_free ac1 /\ branch_free ac2
  | <[ while _@_ do ac1@(_,_) end ]> => branch_free ac1
  | <[ branch _ _ ]> => False
end.

Lemma branch_free_pc_of_acom: 
  forall ac pc, branch_free ac -> pc_of_acom pc ac = pc.
Proof.
  induction ac; simpl; try tauto.
  intros pc [H1 H2]. now rewrite IHac1, IHac2.
Qed.

Fixpoint well_labeled_acom ac P PA pc P' PA' : Prop :=
  match ac with 
  | <[ skip ]> => less_precise P' P /\ less_precise PA' PA
  | <[ x := ae ]> => less_precise P' (x !->(join pc (label_of_aexp P ae)); P) /\ less_precise PA' PA
  | <[ ac1 ;@(Pi, PAi) ac2 ]> => branch_free ac2 /\
                                   well_labeled_acom ac1 P PA pc Pi PAi /\
                                   well_labeled_acom ac2 Pi PAi (pc_of_acom pc ac1) P' PA'
  | <[ if be@lbe then ac1 else ac2 end ]> => can_flow (label_of_bexp P be) lbe = true /\
                                               branch_free ac1 /\ branch_free ac2 /\
                                               well_labeled_acom ac1 P PA (join pc lbe) P' PA' /\
                                               well_labeled_acom ac2 P PA (join pc lbe) P' PA'
  | <[ while be@lbe do ac1 @(Pi, PAi) end ]> => can_flow (label_of_bexp Pi be) lbe = true /\
                                                  branch_free ac1 /\
                                                  less_precise Pi P /\
                                                  less_precise PAi PA /\
                                                  well_labeled_acom ac1 Pi PAi (join pc lbe) Pi PAi /\
                                                  less_precise P' Pi /\
                                                  less_precise PA' PAi
  | <[ X@@lx <-a[[i@li]] ]> => can_flow (label_of_aexp P i) li = true /\
                                 can_flow pc lx = true /\
                                 can_flow li lx = true /\
                                 can_flow (PA a) lx = true /\
                                 less_precise P' (X !-> lx; P) /\
                                 less_precise PA' PA
  | <[ a[i@li] <- e]> => can_flow (label_of_aexp P i) li = true /\
                           less_precise P' P /\
                           less_precise PA' (a !-> (join (PA a) (join pc (join li (label_of_aexp P e)))); PA)
  | <[ branch l ac ]> => well_labeled_acom ac P PA pc P' PA'
  end.

Lemma static_tracking_no_branch : forall c P PA P' PA' pc ac lbl,
  static_tracking c P PA pc = (<[branch lbl ac]>, P', PA') ->
  False.
Proof.
  induction c; simpl; intros; invert H.
  + destruct (static_tracking c1 P PA pc) as ((ac1&P1)&PA1), (static_tracking c2 P1 PA1 pc) as ((ac2&P2)&PA2).
    invert H1.
  + destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1),
    (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2).
    invert H1.
  + destruct (static_tracking_while (static_tracking c) P PA pc
         (length (assigned_vars c) + length (assigned_arrs c)) be
         (assigned_vars c) (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c)))
         as (((P1&PA1)&lbe)&ac1).
    invert H1.
Qed.

Lemma static_tracking_branch_free : forall c P PA P' PA' pc ac,
  static_tracking c P PA pc = (ac, P', PA') -> branch_free ac.
Proof.
  induction c; simpl; intros; invert H; try easy.
  - destruct (static_tracking c1 P PA pc) as ((ac1 & P1) & PA1) eqn: Heq1, (static_tracking c2 P1 PA1 pc)
    as ((ac2 & P2) & PA2) eqn: Heq2. invert H1.
    simpl. split; [eapply IHc1 | eapply IHc2]; eassumption.
  - destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Heq1,
    (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2 & P2) & PA2) eqn: Heq2. invert H1.
    simpl. split; [eapply IHc1 | eapply IHc2]; eassumption.
  - destruct (static_tracking_while (static_tracking c) P PA pc
    (length (assigned_vars c) + length (assigned_arrs c)) be (assigned_vars c) (assigned_arrs c))
    as (((Pi & PAi) & lbe) & ac1) eqn: Heq.
    eapply static_tracking_while_invariant in Heq. 2: { intros. apply (IHc P0 PA0 P1 PA1 pc0 ac' H). }
    invert H1. exact Heq.
Qed.

Lemma exp_label_less_precise P P': 
  less_precise P P' ->
  (forall ae, can_flow (label_of_aexp P' ae) (label_of_aexp P ae) = true) /\
  (forall be, can_flow (label_of_bexp P' be) (label_of_bexp P be) = true).
Proof.
  intro Hlp.
  apply aexp_bexp_mutind; intros; try easy.
  - apply Hlp.
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_bexp P' b), (label_of_bexp P b), (label_of_aexp P' a1), (label_of_aexp P a1),
    (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_aexp P' a1), (label_of_aexp P a1), (label_of_aexp P' a2), (label_of_aexp P a2).
  - cbn. now destruct (label_of_bexp P' b1), (label_of_bexp P b1), (label_of_bexp P' b2), (label_of_bexp P b2).
Qed.

Lemma label_of_aexp_less_precise : 
  forall e P P', less_precise P P' ->
  can_flow (label_of_aexp P' e) (label_of_aexp P e) = true.
Proof.
  intros. now apply exp_label_less_precise.
Qed.

Lemma label_of_bexp_less_precise : 
  forall e P P', less_precise P P' ->
  can_flow (label_of_bexp P' e) (label_of_bexp P e) = true.
Proof.
  intros. now apply exp_label_less_precise.
Qed.

Lemma well_labeled_weaken_post : forall ac P PA pc P' PA' P'' PA'',
  well_labeled_acom ac P PA pc P' PA' ->
  less_precise P'' P' ->
  less_precise PA'' PA' ->
  well_labeled_acom ac P PA pc P'' PA''.
Proof.
  induction ac; intros; simpl in *.
  - destruct H. split; eapply less_precise_trans; eassumption.
  - destruct H. split; eapply less_precise_trans; eassumption.
  - destruct H as (? & ? & ?). repeat split. 1, 2: assumption. eapply IHac2; eassumption.
  - destruct H as (? & ? & ? & ? & ?). repeat split; [assumption.. | eapply IHac1 | eapply IHac2]; eassumption.
  - destruct H as (? & ? & ? & ? & ? & ? & ?). repeat split; try assumption; eapply less_precise_trans; eassumption.
  - destruct H as (? & ? & ? & ? & ? & ?). repeat split; try assumption; eapply less_precise_trans; eassumption.
  - destruct H as (? & ? & ?). repeat split; try assumption; eapply less_precise_trans; eassumption.
  - eapply IHac; eassumption.
Qed.

Lemma well_labeled_strengthen_pre : forall ac P PA pc P' PA' P'' PA'',
  well_labeled_acom ac P PA pc P' PA' ->
  less_precise P P'' ->
  less_precise PA PA'' ->
  well_labeled_acom ac P'' PA'' pc P' PA'.
Proof.
  induction ac; simpl; intros.
  - destruct H. split; eapply less_precise_trans; eassumption.
  - destruct H. split; [|eapply less_precise_trans; eassumption].
    intros y. specialize (H y). unfold t_update in *. destruct (x =? y).
    + apply (label_of_aexp_less_precise e) in H0. now destruct pc, (P' y), (label_of_aexp P e), (label_of_aexp P'' e).
    + specialize (H0 y). eapply can_flow_trans; eassumption.
  - destruct H as (? & ? & ?).
    repeat split; try assumption. eapply IHac1; eassumption.
  - destruct H as (? & ? & ? & ? & ?).
    repeat split; try assumption. 1: eapply can_flow_trans; [now apply label_of_bexp_less_precise | eassumption].
    1: eapply IHac1; eassumption.
    eapply IHac2; eassumption.
  - repeat split; try apply H; eapply less_precise_trans; now try apply H.
  - repeat split; try apply H.
    + apply (label_of_aexp_less_precise i) in H0. eapply can_flow_trans; now try apply H.
    + apply (label_of_aexp_less_precise a) in H1. eapply can_flow_trans; now try apply H.
    + destruct H as (?&?&?&?&?&?). intros y. specialize (H5 y).
      unfold t_update in *. destruct (x =? y).
      * assumption.
      * eapply can_flow_trans; [apply H0 | apply H5].
    + eapply less_precise_trans; now try apply H.
  - repeat split.
    + apply (label_of_aexp_less_precise i) in H0. eapply can_flow_trans; now try apply H.
    + eapply less_precise_trans; now try apply H.
    + destruct H as (?&?&?). intros b. specialize (H3 b). apply (label_of_aexp_less_precise e) in H0 as H0'.
      specialize (H1 a) as H1'.
      unfold t_update in *. destruct (a =? b).
      * destruct (PA a), (PA'' a), pc, li, (label_of_aexp P e), (label_of_aexp P'' e); try easy.
      * eapply can_flow_trans. 2: eassumption. apply H1.
  - eapply IHac; eassumption.
Qed.

Lemma static_tracking_fixpoint:
  forall c P PA pc ac P' PA', 
  static_tracking c P PA pc = (ac, P', PA') ->
  forall P'' PA'',
  filter P'' (assigned_vars c) = [] ->
  filter PA'' (assigned_arrs c) = [] ->
  less_precise P'' P -> less_precise PA'' PA ->
  join_pub_vars P'' P' = P'' /\ join_pub_vars PA'' PA' = PA''.
Proof.
  induction c.
  + simpl. intros ? ? _ ? ? ? [= _ -> ->] ? ? _ _ ? ?. split; now apply join_pub_vars_less_precise.
  + simpl. intros. invert H; subst. split; [|now apply join_pub_vars_less_precise].
    apply functional_extensionality. intro y. unfold join_pub_vars, t_update. destruct (x =? y) eqn: Heq.
    - rewrite String.eqb_eq in Heq. subst. specialize (H2 y). now destruct (P y), (P'' y).
    - specialize (H2 y); now destruct (P y), (P'' y).
  + simpl. intros.
    destruct (static_tracking c1 P PA pc) as ((ac1 & P1) & PA1) eqn: Heq1.
    destruct (static_tracking c2 P1 PA1 pc) as ((ac2 & P2) & PA2) eqn: Heq2.
    apply IHc1 with (P'' := P'') (PA'' := PA'') in Heq1.
    2, 3: unfold str_nodup in H0, H1; rewrite filter_nodup in H0, H1; apply nodup_nil in H0, H1;
    rewrite filter_app in H0, H1; now apply app_eq_nil in H0, H1. 2, 3: assumption.
    apply IHc2 with (P'' := P'') (PA'' := PA'') in Heq2.
    2, 3: unfold str_nodup in H0, H1; rewrite filter_nodup in H0, H1; apply nodup_nil in H0, H1;
    rewrite filter_app in H0, H1; now apply app_eq_nil in H0, H1. 2, 3: now apply join_pub_vars_less_precise.
    invert H.
    split; apply Heq2.
  + simpl. intros.
    destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Heq1.
    destruct (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2 & P2) & PA2) eqn: Heq2.
    apply IHc1 with (P'' := P'') (PA'' := PA'') in Heq1.
    2, 3: unfold str_nodup in H0, H1; rewrite filter_nodup in H0, H1; apply nodup_nil in H0, H1;
    rewrite filter_app in H0, H1; now apply app_eq_nil in H0, H1. 2, 3: assumption.
    apply IHc2 with (P'' := P'') (PA'' := PA'') in Heq2.
    2, 3: unfold str_nodup in H0, H1; rewrite filter_nodup in H0, H1; apply nodup_nil in H0, H1;
    rewrite filter_app in H0, H1; now apply app_eq_nil in H0, H1. 2, 3: assumption.
    invert H. do 2 rewrite <- join_pub_vars_assoc. destruct Heq1 as [-> ->]. exact Heq2.
  + simpl. 
    induction (length (assigned_vars c) + length (assigned_arrs c)) as [|n IHn]; simpl;
    intros P PA pc ac P' PA' H. 
    * destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((ac' & Pi') & PAi') eqn: Heq'.
      rewrite Tauto.if_same in H. invert H. intros ? ? Hnil1 Hnil2 ? ?. eapply IHc in Heq'; [|eassumption..].
      do 2 rewrite <- join_pub_vars_assoc. apply join_pub_vars_less_precise in H as ->, H0 as ->. assumption.
    * destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((ac' & Pi') & PAi') eqn: Heq'.
      destruct (list_eqb (filter P (assigned_vars c)) (filter (join_pub_vars P Pi') (assigned_vars c))
        && list_eqb (filter PA (assigned_arrs c)) (filter (join_pub_vars PA PAi') (assigned_arrs c))) eqn: HeqPPA.
      - invert H. intros ? ? Hnil1 Hnil2 ? ?. eapply IHc in Heq'; [|eassumption..].
        do 2 rewrite <- join_pub_vars_assoc. apply join_pub_vars_less_precise in H as ->, H0 as ->. assumption.
      - intros ? ? Hnil1 Hnil2 ? ?. 
        eapply IHc in Heq'; [|eassumption..].
        eapply IHn with (P'' := join_pub_vars P'' Pi') (PA'' := join_pub_vars PA'' PAi') in H.
        2, 3: destruct Heq' as [Heq1 Heq2]; rewrite 1? Heq1; rewrite 1? Heq2; assumption. 
        2, 3: apply join_pub_vars_less_precise; destruct Heq' as [Heq1 Heq2]; rewrite 1? Heq1; rewrite 1? Heq2; rewrite <- join_pub_vars_assoc.
        2: apply join_pub_vars_less_precise in H0 as ->; assumption.
        2: apply join_pub_vars_less_precise in H1 as ->; assumption.
        destruct Heq' as [<- <-]. exact H.
  + simpl. intros. invert H. split; [|now apply join_pub_vars_less_precise].
    apply functional_extensionality. intros y. unfold join_pub_vars, t_update. destruct (x =? y) eqn: Heq.
      - rewrite String.eqb_eq in Heq. subst. specialize (H2 y). now destruct (P y), (P'' y).
      - specialize (H2 y). now destruct (P y), (P'' y).
  + simpl. intros. invert H. split; [now apply join_pub_vars_less_precise|].
    apply functional_extensionality. intros y. unfold join_pub_vars, t_update. destruct (a =? y) eqn: Heq.
      - rewrite String.eqb_eq in Heq. subst. specialize (H3 y). now destruct (PA y), (PA'' y).
      - specialize (H3 y). now destruct (PA y), (PA'' y).
Qed.

Lemma static_tracking_unassigned: forall c P PA pc ac P' PA',
  static_tracking c P PA pc = (ac, P', PA') ->
  (forall y, ~In y (assigned_vars c) -> P' y = P y) /\
  (forall y, ~In y (assigned_arrs c) -> PA' y = PA y).
Proof.
  induction c; simpl; intros.
  - invert H. tauto.
  - invert H. split; [|tauto]. intros y. unfold t_update. destruct (x =? y) eqn: Heq;
    [apply String.eqb_eq in Heq | apply String.eqb_neq in Heq]; tauto.
  - destruct (static_tracking c1 P PA pc) as ((ac1 & P1) & PA1) eqn: Hc1. apply IHc1 in Hc1.
    destruct (static_tracking c2 P1 PA1 pc) as ((ac2 & P2) & PA2) eqn: Hc2. apply IHc2 in Hc2.
    split.
    + intros y Hnin.
      assert (~ In y (assigned_vars c1) /\ ~ In y (assigned_vars c2)) as [Hnin1 Hnin2]. 
      { split; intros Hin; apply Hnin; apply nodup_In; apply in_or_app; [left | right]; assumption. }
      invert H. destruct Hc1, Hc2. now rewrite H1, H.
    + intros y Hnin.
      assert (~ In y (assigned_arrs c1) /\ ~ In y (assigned_arrs c2)) as [Hnin1 Hnin2]. 
      { split; intros Hin; apply Hnin; apply nodup_In; apply in_or_app; [left | right]; assumption. }
      invert H. destruct Hc1, Hc2. now rewrite H2, H0.
  - destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Hc1. apply IHc1 in Hc1.
    destruct (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2 & P2) & PA2) eqn: Hc2. apply IHc2 in Hc2.
    invert H. split.
    + intros y Hnin.
      assert (~ In y (assigned_vars c1) /\ ~ In y (assigned_vars c2)) as [Hnin1 Hnin2]. 
      { split; intros Hin; apply Hnin; apply nodup_In; apply in_or_app; [left | right]; assumption. }
      unfold join_pub_vars. destruct Hc1, Hc2. rewrite H, H1; [|assumption..]. now destruct (P y).
    + intros y Hnin.
      assert (~ In y (assigned_arrs c1) /\ ~ In y (assigned_arrs c2)) as [Hnin1 Hnin2]. 
      { split; intros Hin; apply Hnin; apply nodup_In; apply in_or_app; [left | right]; assumption. }
      unfold join_pub_vars. destruct Hc1, Hc2. rewrite H0, H2; [|assumption..]. now destruct (PA y).
  - revert P PA pc ac P' PA' H.
    induction (length (assigned_vars c) + length (assigned_arrs c)) as [|n IHn]; intros.
    + cbn in H. destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((aci & Pi) & PAi) eqn: Hi.
      apply IHc in Hi. destruct Hi as [Hi1 Hi2].
      rewrite Tauto.if_same in H. invert H.
      split; intros y Hnin; [specialize (Hi1 y Hnin) | specialize (Hi2 y Hnin)]; unfold join_pub_vars;
          [rewrite Hi1; now destruct (P y) | rewrite Hi2; now destruct (PA y)].
    + simpl in H. destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((aci & Pi) & PAi) eqn: Hi.
      apply IHc in Hi.
      destruct (list_eqb (filter P (assigned_vars c)) (filter (join_pub_vars P Pi) (assigned_vars c))
        && list_eqb (filter PA (assigned_arrs c)) (filter (join_pub_vars PA PAi) (assigned_arrs c))).
      * invert H. destruct Hi as [Hi1 Hi2].
        split; intros y Hnin; [specialize (Hi1 y Hnin) | specialize (Hi2 y Hnin)]; unfold join_pub_vars;
            [rewrite Hi1; now destruct (P y) | rewrite Hi2; now destruct (PA y)].
      * apply IHn in H. destruct Hi as [Hi1 Hi2], H as [H1 H2].
        split; intros y Hnin.
        -- specialize (Hi1 y Hnin). specialize (H1 y Hnin). rewrite H1. unfold join_pub_vars. rewrite Hi1.
           now destruct (P y).
        -- specialize (Hi2 y Hnin). specialize (H2 y Hnin). rewrite H2. unfold join_pub_vars. rewrite Hi2.
           now destruct (PA y).
  - invert H. split; [|tauto].
  intros y. unfold t_update. destruct (x =? y) eqn: Heq;
  [apply String.eqb_eq in Heq | apply String.eqb_neq in Heq]; tauto.
  - invert H. split; [tauto|].
    intros y. unfold t_update. destruct (a =? y) eqn: Heq;
    [apply String.eqb_eq in Heq | apply String.eqb_neq in Heq]; tauto.
Qed.
      
Lemma static_tracking_while_early_fixpoint: 
  forall c P PA pc ac P' PA',
  static_tracking c P PA pc = (ac, P', PA') ->
  list_eqb (filter P (assigned_vars c))
  (filter (join_pub_vars P P') (assigned_vars c)) &&
  list_eqb (filter PA (assigned_arrs c))
  (filter (join_pub_vars PA PA') (assigned_arrs c)) = true ->
  join_pub_vars P P' = P /\ join_pub_vars PA PA' = PA.
Proof.
  intros. apply static_tracking_unassigned in H as [H1 H2].
  apply andb_prop in H0 as [HP HPA].
  unfold list_eqb in HP, HPA.
  destruct (list_eq_dec string_dec (filter P (assigned_vars c)) (filter (join_pub_vars P P') (assigned_vars c)))
  as [HeqP|?]; [|congruence].
  destruct (list_eq_dec string_dec (filter PA (assigned_arrs c)) (filter (join_pub_vars PA PA') (assigned_arrs c)))
  as [HeqPA|?]; [|congruence].
  split; unfold join_pub_vars; apply functional_extensionality; intros y.
  - destruct (in_dec string_dec y (assigned_vars c)) as [Hin | Hnin].
    + eapply ext_in_filter in HeqP. 2: eassumption. rewrite HeqP at 2. reflexivity.
    + rewrite H1; [|assumption]. now destruct (P y).
  - destruct (in_dec string_dec y (assigned_arrs c)) as [Hin | Hnin].
    + eapply ext_in_filter in HeqPA. 2: eassumption. rewrite HeqPA at 2. reflexivity.
    + rewrite H2; [|assumption]. now destruct (PA y).
Qed.

Lemma filter_join P P' l:
  filter (join_pub_vars P P') l = filter P' (filter P l).
Proof.
  induction l.
  - reflexivity.
  - simpl. unfold join_pub_vars. destruct (P a); simpl; destruct  (P' a); simpl; [f_equal|..]; apply IHl.
Qed.

Lemma filter_shorter_or_eq {A} f (l: list A):
  filter f l = l \/ length (filter f l) < length l.
Proof.
  induction l.
  - now left.
  - destruct IHl.
    + simpl. destruct (f a).
      * left. now rewrite H.
      * right. rewrite H. lia.
    + right. simpl. destruct (f a); simpl; lia.
Qed.

Lemma static_tracking_while_decreases:
  forall c P PA P' PA',
  list_eqb (filter P (assigned_vars c))
  (filter (join_pub_vars P P') (assigned_vars c)) &&
  list_eqb (filter PA (assigned_arrs c))
  (filter (join_pub_vars PA PA') (assigned_arrs c)) = false ->
  length (filter (join_pub_vars P P') (assigned_vars c))
    + length (filter (join_pub_vars PA PA') (assigned_arrs c))
  < length (filter P (assigned_vars c))
    + length (filter PA (assigned_arrs c)).
Proof.
  intros. apply andb_false_iff in H. unfold list_eqb in H. destruct H as [HP | HPA].
  - destruct (list_eq_dec string_dec (filter P (assigned_vars c)) (filter (join_pub_vars P P') (assigned_vars c))) as
    [?|HneqP];[congruence|].
    repeat rewrite filter_join in *.
    pose proof (filter_length_le PA' (filter PA (assigned_arrs c))).
    enough (length (filter P' (filter P (assigned_vars c))) < length (filter P (assigned_vars c))) by lia.
    destruct (filter_shorter_or_eq P' (filter P (assigned_vars c))); [congruence | lia].
  - destruct (list_eq_dec string_dec (filter PA (assigned_arrs c)) (filter (join_pub_vars PA PA') (assigned_arrs c)))
    as [?|HneqPA];[congruence|].
    repeat rewrite filter_join in *.
    pose proof (filter_length_le P' (filter P (assigned_vars c))).
    enough (length (filter PA' (filter PA (assigned_arrs c))) < length (filter PA (assigned_arrs c))) by lia.
    destruct (filter_shorter_or_eq PA' (filter PA (assigned_arrs c))); [congruence | lia].
Qed.

Lemma static_tracking_while_well_labeled: forall c n P PA pc be P' PA' lbe ac, 
  (forall P PA pc ac P' PA', static_tracking c P PA pc = (ac, P', PA') -> well_labeled_acom ac P PA pc P' PA') ->
  (n >= length (filter P (assigned_vars c)) + length (filter PA (assigned_arrs c))) ->
  (static_tracking_while (static_tracking c) P PA pc n be 
    (assigned_vars c) (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c))
      = (P', PA', lbe, ac)) ->
  can_flow (label_of_bexp P' be) lbe = true /\
  less_precise P' P /\
  less_precise PA' PA /\
  well_labeled_acom ac P' PA' (join pc lbe) P' PA'.
Proof.
  induction n; intros.
  - cbn in H1.
    destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Hwl.
    apply static_tracking_fixpoint with (P'' := P) (PA'' := PA) in Hwl as Hfix. 4, 5: apply less_precise_refl.
    2, 3: apply length_zero_iff_nil; lia.
    apply H in Hwl. rewrite Tauto.if_same in H1. invert H1; subst.
    pose proof (less_precise_join_r P P1). pose proof (less_precise_join_r PA PA1).
    destruct Hfix as [Hfix1 Hfix2]. rewrite Hfix1, Hfix2 in *.
    repeat split. 2, 3: apply less_precise_refl.
    + apply can_flow_refl.
    + eapply well_labeled_weaken_post; eassumption.
  - cbn in H1.
    destruct (static_tracking c P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Hwl.
    apply H in Hwl as Hwl'.
    destruct (list_eqb (filter P (assigned_vars c)) (filter (join_pub_vars P P1) (assigned_vars c))
      && list_eqb (filter PA (assigned_arrs c)) (filter (join_pub_vars PA PA1) (assigned_arrs c))) eqn: HeqPPA.
    + invert H1; subst.
      pose proof (less_precise_join_r P P1). pose proof (less_precise_join_r PA PA1).
      eapply static_tracking_while_early_fixpoint in HeqPPA. 2: eassumption. destruct HeqPPA as [Heq1 Heq2].
      rewrite Heq1, Heq2 in *. clear Heq1 Heq2.
      repeat split. 2, 3: apply less_precise_refl.
      * apply can_flow_refl.
      * eapply well_labeled_weaken_post; eassumption.
    + apply IHn in H1. 3: { apply static_tracking_while_decreases in HeqPPA. lia. } 2: exact H.
      repeat split; try apply H1; (eapply less_precise_trans; [apply less_precise_join_l | apply H1]).
Qed. 
  

Lemma static_tracking_well_labeled : forall c P PA pc ac P' PA',
  static_tracking c P PA pc = (ac, P', PA') ->
  well_labeled_acom ac P PA pc P' PA'.
Proof.
  induction c; intros.
  - simpl in H. invert H. simpl. split; now apply less_precise_refl.
  - simpl in H. invert H. simpl. split; now apply less_precise_refl.
  - simpl in H. destruct (static_tracking c1 P PA pc) as ((ac1 & P1) & PA1) eqn: Heq1,
    (static_tracking c2 P1 PA1 pc) as ((ac2 & P2) & PA2) eqn: Heq2.
    invert H. simpl.
    assert (pc_of_acom pc ac1 = pc) as ->.
    {
      apply static_tracking_branch_free in Heq1. now apply branch_free_pc_of_acom.
    }
    split. 1: eapply static_tracking_branch_free; eassumption.
    split; [now apply IHc1 | now apply IHc2].
  - simpl in H. destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1 & P1) & PA1) eqn: Heq1,
    (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2 & P2) & PA2) eqn: Heq2.
    invert H. simpl.
    split. 1: apply can_flow_refl.
    split. 1: eapply static_tracking_branch_free; eassumption.
    split. 1: eapply static_tracking_branch_free; eassumption.
    apply IHc1 in Heq1. apply IHc2 in Heq2.
    split; eapply well_labeled_weaken_post; try eassumption. 
    + apply less_precise_join_l.
    + apply less_precise_join_l.
    + apply less_precise_join_r.
    + apply less_precise_join_r.
  - apply static_tracking_branch_free in H as H'. simpl in H.
    destruct (static_tracking_while (static_tracking c) P PA pc
      (length (assigned_vars c) + length (assigned_arrs c)) be (assigned_vars c) (assigned_arrs c)
      (filter P (assigned_vars c)) (filter PA (assigned_arrs c))) as (((Pi & PAi) & lbe) & ac1) eqn: Heq.
    invert H. cbn.
    apply static_tracking_while_well_labeled in Heq. 2: assumption.
    2: { pose proof (filter_length_le P (assigned_vars c)). pose proof (filter_length_le PA (assigned_arrs c)). lia. }
    repeat split. 2: exact H'. 5, 6: apply less_precise_refl.
    all: apply Heq.
  - simpl in H. invert H. simpl. repeat split.
    5,6: apply less_precise_refl.
    + now destruct (label_of_aexp P i).
    + now destruct pc.
    + now destruct pc, (label_of_aexp P i).
    + now destruct pc, (label_of_aexp P i), (PA' a).
  - simpl in H. invert H. simpl. repeat split.
    2, 3: apply less_precise_refl.
    now destruct (label_of_aexp P' i).
Qed.
    
Lemma erase_static_tracking : forall c ac P PA P' PA' pc,
  static_tracking c P PA pc = (ac, P', PA') ->
  erase ac = c.
Proof.
  induction c; simpl; intros; try (now invert H; auto).
  + destruct (static_tracking c1 P PA pc) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking c2 P1 PA1 pc) as ((ac2&P2)&PA2) eqn:Heq2.
    invert H. erewrite <- IHc1; [|eassumption]. erewrite <- IHc2; [tauto|eassumption].
  + destruct (static_tracking c1 P PA (join pc (label_of_bexp P be))) as ((ac1&P1)&PA1) eqn:Heq1.
    destruct (static_tracking c2 P PA (join pc (label_of_bexp P be))) as ((ac2&P2)&PA2) eqn:Heq2.
    invert H. erewrite <- IHc1; [|eassumption]. erewrite <- IHc2; [tauto|eassumption].
  + destruct (static_tracking_while (static_tracking c) P PA pc (length (assigned_vars c) + length (assigned_arrs c))
      be (assigned_vars c) (assigned_arrs c) (filter P (assigned_vars c)) (filter PA (assigned_arrs c)))
      as (((P1&PA1)&pc1)&ac1) eqn:Heq.
    invert H. simpl. eapply static_tracking_while_invariant in Heq; [|apply IHc]. now rewrite Heq.
Qed.

Fixpoint flex_vslh_acom ac :=
  match ac with
  | <[ skip ]> => <{ skip }>
  | <[ X := ae ]> => <{ X := ae }>
  | <[ ac1;@(_,_) ac2 ]> => <{ flex_vslh_acom ac1; flex_vslh_acom ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ if be' then "b" := be' ? "b" : 1; flex_vslh_acom ac1 else
                     "b" := be' ? 1 : "b"; flex_vslh_acom ac2 end }>
  | <[ while be@lbe do ac@(_,_) end ]> =>
      let be' := if lbe then be else <{ "b" = 0 && be }> in
      <{ while be' do "b" := be' ? "b" : 1; flex_vslh_acom ac end; "b" := be' ? 1 : "b" }>
  | <[ X@@lx <- a[[i@li]] ]> =>
      let i' := if li && negb lx then i else <{ ("b" = 1) ? 0 : i }> in
      if lx && li then <{ X <- a[[i]]; X := ("b" = 1) ? 0 : X }> else <{ X <- a[[i']] }>
  | <[ a[i@li] <- e ]> => let i' := if li then i else <{ ("b" = 1) ? 0 : i }> in
      <{ a[i'] <- e }>
  | <[ branch l ac1 ]> => <{ flex_vslh_acom ac1 }> (* unreachable anyway *)
  end.

Definition fs_flex_vslh P PA c :=
  let '(ac, _, _) := static_tracking c P PA public in
  flex_vslh_acom ac.

(** * Ideal small-step evaluation *)

Inductive terminal : acom -> Prop :=
  | Terminal_Skip : terminal <[ skip ]>
  | Terminal_Branch : forall l c, terminal c -> terminal <[ branch l c ]>.

Reserved Notation
  "'<[[' c , st , ast , b , pc , P , PA ']]>' '-->i_' ds '^^' os '<[[' ct , stt , astt , bt , pct , Pt , PAt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs ->
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs -> dirs -> obs -> Prop :=
  | ISM_Asgn : forall X ae n st ast b pc P PA,
      aeval st ae = n ->
      <[[X := ae, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[skip, X !-> n; st, ast, b, pc, X !-> (join pc (label_of_aexp P ae)); P, PA]]>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2 pc P PA pc' P' PA' Pi PAi,
      <[[c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[c1t, stt, astt, bt, pc', P', PA']]>  ->
      <[[(c1;@(Pi,PAi)c2), st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[(c1t;@(Pi,PAi) c2), stt, astt, bt, pc', P', PA']]>
  | ISM_Seq_Skip : forall st ast b c1 c2 pc P PA Pi PAi,
      terminal c1 ->
      <[[(c1;@(Pi,PAi)c2), st, ast, b, pc, P, PA]]>  -->i_[]^^[] <[[c2, st, ast, b, pc_of_acom pc c1, P, PA]]>
  | ISM_If : forall be ct cf st ast b c' b' lbe pc P PA,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      <[[if be@lbe then ct else cf end, st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OBranch b'] <[[branch pc c', st, ast, b, join pc lbe, P, PA]]>
  | ISM_If_F : forall be ct cf st ast b c' b' lbe pc P PA,
      b' = (lbe || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      <[[if be@lbe then ct else cf end, st, ast, b, pc, P, PA]]> -->i_[DForce]^^[OBranch b'] <[[branch pc c', st, ast, true, join pc lbe, P, PA]]>
  | ISM_While : forall be c st ast b lbe c' pc P PA Pi PAi,
      c' = <[ if be@lbe then c;@(Pi, PAi) while be@lbe do c@(Pi,PAi) end else skip end ]> ->
      <[[while be@lbe do c@(Pi,PAi) end, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[c', st, ast, b, pc, P, PA]]>
  | ISM_ARead : forall X a ie st ast (b :bool) i li lX v pc P PA,
      (if (negb li) && b then 0 else (aeval st ie)) = i ->
      (if lX && li && b then 0 else nth i (ast a) 0) = v ->
      i < length (ast a) ->
      <[[X@@lX <- a[[ie@li]], st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OARead a i]
            <[[skip, X !-> v; st, ast, b, pc, X !-> lX; P, PA]]>
  | ISM_ARead_U : forall X a ie st ast i a' i' v (lX:label) pc P PA,
      aeval st ie = i ->
      v = (if lX then 0 else nth i' (ast a') 0) ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      <[[X@@lX <- a[[ie@public]], st, ast, true, pc, P, PA]]> -->i_[DLoad a' i']^^[OARead a i]
            <[[skip, X !-> v; st, ast, true, pc, X !-> lX; P, PA]]>
  | ISM_Write : forall a ie e st ast (b :bool) i n li i' la pc P PA,
      aeval st e = n ->
      aeval st ie = i ->
      (if b && negb li then 0 else i) = i' ->
      la = join (PA a) (join pc (join li (label_of_aexp P e))) ->
      i' < length (ast a) ->
      <[[a[ie@li] <- e, st, ast, b, pc, P, PA]]> -->i_[DStep]^^[OAWrite a i']
            <[[skip, st, a !-> upd i' (ast a) n; ast, b, pc, P, a !-> la; PA]]>
  | ISM_Write_U : forall a ie e st ast i n a' i' la pc P PA,
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      la = join (PA a) (join pc (label_of_aexp P e)) ->
      <[[a[ie@public] <- e, st, ast, true, pc, P, PA]]> -->i_[DStore a' i']^^[OAWrite a i]
            <[[skip, st, a' !-> upd i' (ast a') n; ast, true, pc, P, a !-> la; PA]]>
  | ISM_Branch : forall c1 st ast b ds os c1t stt astt bt pc pc' P PA pct Pt PAt,
      <[[c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[c1t, stt, astt, bt, pct, Pt, PAt]]>  ->
      <[[branch pc' c1, st, ast, b, pc, P, PA]]>  -->i_ds^^os <[[branch pc' c1t, stt, astt, bt, pct, Pt, PAt]]>

    where "<[[ c , st , ast , b , pc , P , PA ]]> -->i_ ds ^^ os  <[[ ct ,  stt , astt , bt , pct , Pt , PAt ]]>" :=
    (ideal_eval_small_step c st ast b pc P PA ct stt astt bt pct Pt PAt ds os).

Reserved Notation
  "'<[[' c , st , ast , b , pc , P , PA ']]>' '-->i*_' ds '^^' os '<[[' ct , stt , astt , bt , pct , Pt , PAt ']]>'"
  (at level 40, c custom acom at level 99, ct custom acom at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:acom) (st:state) (ast:astate) (b:bool) (pc:label) (P:pub_vars) (PA:pub_arrs):
    acom -> state -> astate -> bool -> label -> pub_vars -> pub_arrs -> dirs -> obs -> Prop :=
  | multi_ideal_refl : <[[c, st, ast, b, pc, P, PA]]> -->i*_[]^^[] <[[c, st, ast, b, pc, P, PA]]>
  | multi_ideal_trans (c':acom) (st':state) (ast':astate) (b':bool)
                (c'':acom) (st'':state) (ast'':astate) (b'':bool) (pc' pc'':label) (P' P'':pub_vars) (PA' PA'':pub_arrs)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <[[c, st, ast, b, pc, P, PA]]> -->i_ds1^^os1 <[[c', st', ast', b', pc', P', PA']]> ->
      <[[c', st', ast', b', pc', P', PA']]> -->i*_ds2^^os2 <[[c'', st'', ast'', b'', pc'', P'', PA'']]> ->
      <[[c, st, ast, b, pc, P, PA]]> -->i*_(ds1++ds2)^^(os1++os2) <[[c'', st'', ast'', b'', pc'', P'', PA'']]>

  where "<[[ c , st , ast , b , pc , P , PA ]]> -->i*_ ds ^^ os  <[[ ct ,  stt , astt , bt , pct , Pt , PAt ]]>" :=
    (multi_ideal c st ast b pc P PA ct stt astt bt pct Pt PAt ds os).

Definition ideal_same_obs ac st1 st2 ast1 ast2 P PA :=
  forall ds os1 os2 stt1 stt2 astt1 astt2 ac1 ac2 b1 b2 pc1 pc2 Pt1 PAt1 Pt2 PAt2,
    <[[ac, st1, ast1, false, public, P, PA]]> -->i*_ds^^os1 <[[ac1, stt1, astt1, b1, pc1, Pt1, PAt1]]> ->
    <[[ac, st2, ast2, false, public, P, PA]]> -->i*_ds^^os2 <[[ac2, stt2, astt2, b2, pc2, Pt2, PAt2]]> ->
    os1 = os2.

Lemma multi_ideal_trans_nil_l c st ast b c' st' ast' b' ct stt astt bt ds os pc pc' pct P PA P' PA' Pt PAt:
  <[[c, st, ast, b, pc, P, PA]]> -->i_[]^^[] <[[c', st', ast', b', pc', P', PA']]> ->
  <[[c', st', ast', b', pc', P', PA']]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r c st ast b c' st' ast' b' ct stt astt bt ds os pc pc' pct P PA P' PA' Pt PAt:
  <[[c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[c', st', ast', b', pc', P', PA']]> ->
  <[[c', st', ast', b', pc', P', PA']]> -->i*_[]^^[] <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall c st ast b ds cm stm astm bm os dst ct stt astt bt ost pc P PA pcm Pm PAm pct Pt PAt,
    <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[cm, stm, astm, bm, pcm, Pm, PAm]]> ->
    <[[cm, stm, astm, bm, pcm, Pm, PAm]]> -->i*_dst^^ost <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
    <[[c, st, ast, b, pc, P, PA]]> -->i*_(ds++dst)^^(os++ost) <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. revert ct stt astt bt pct Pt PAt dst ost H0. induction H; simpl; intros; [tauto|].
  rewrite <- 2!app_assoc. eapply multi_ideal_trans.
  + eapply H.
  + now apply IHmulti_ideal.
Qed.

Lemma multi_ideal_add_snd_com : forall c st ast ct stt astt ds os c2 b bt pc P PA pct Pt PAt Pi PAi,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[c;@(Pi,PAi) c2, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct;@(Pi,PAi) c2, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma multi_ideal_seq : forall ac1 ac2 acm st ast b stm astm bm ds os pc P PA pcm Pm PAm Pi PAi,
  <[[ac1;@(Pi, PAi) ac2, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[acm, stm, astm, bm, pcm, Pm, PAm]]> ->
  (exists st' ast' pc' P' PA' act b' ds1 ds2 os1 os2,
  terminal act /\ os = os1 ++ os2 /\ ds = ds1 ++ ds2 /\
  <[[ac1, st, ast, b, pc, P, PA]]> -->i*_ds1^^os1 <[[act, st', ast', b', pc', P', PA']]> /\
  <[[ac2, st', ast', b', pc_of_acom pc' act, P', PA']]> -->i*_ds2^^os2 <[[acm, stm, astm, bm, pcm, Pm, PAm]]>) \/
  (exists ac', acm = <[ ac';@(Pi, PAi) ac2 ]> /\
   <[[ac1, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', stm, astm, bm, pcm, Pm, PAm]]>).
Proof.
  intros. remember <[ ac1;@(Pi, PAi) ac2 ]> as ac. revert ac1 ac2 Heqac.
  induction H; intros; subst.
  { right. repeat eexists. constructor. }
  invert H.
  + edestruct IHmulti_ideal; [reflexivity|..].
    - destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&->&->&?&?).
      left. rewrite !app_assoc.
      repeat eexists; [|econstructor|]; eassumption.
    - do 2 destruct H. subst. clear IHmulti_ideal.
      right. repeat eexists. econstructor; eassumption.
  + left. repeat eexists; [|constructor|]; eassumption.
Qed.

Lemma ideal_eval_small_step_spec_needs_force : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  ds = [DForce].
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  now induction H; intros; subst; try discriminate; try reflexivity; apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_spec_needs_force : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  In DForce ds.
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  induction H; intros; subst; [discriminate|]. apply in_or_app.
  destruct b'.
  + apply ideal_eval_small_step_spec_needs_force in H. subst. left. now left.
  + right. now apply IHmulti_ideal.
Qed.

Lemma ideal_eval_seq_eval : forall c st ast ct stt astt bt n os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i_ repeat DStep n ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> -> 
  <((erase c, st, ast))> -->^os <((erase ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert Heqb Heqds.
  induction H; intros; subst; try discriminate; try now econstructor.
  + constructor. now apply IHideal_eval_small_step.
  + induction H; simpl in *; [constructor|tauto].
  + rewrite orb_true_r. simpl.
    replace (erase (if beval st be then ct else cf)) with (if beval st be then erase ct else erase cf)
      by now destruct (beval st be). constructor.
  + symmetry in Heqds. change ([DForce]) with ([] ++ [DForce]) in Heqds.
    now apply repeat_eq_elt in Heqds.
  + rewrite ?andb_false_r in *. now constructor.
  + now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_branch : forall c st ast b ct stt astt bt ds os l pc P PA pct Pt PAt,
  <[[ c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ branch l c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ branch l ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H; [constructor|].
  repeat econstructor; eassumption.
Qed.

Lemma multi_ideal_multi_seq : forall c st ast ct stt astt bt n os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ repeat DStep n ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  <((erase c, st, ast ))> -->*^os <((erase ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert n Heqb Heqds.
  induction H; intros; subst; [constructor|].
  symmetry in Heqds. apply repeat_eq_app in Heqds. destruct Heqds.
  remember (length ds1) as n1. remember (length ds2) as n2. clear Heqn1 Heqn2 H0. subst.
  destruct b'.
  { 
    apply ideal_eval_small_step_spec_needs_force in H. change ([DForce]) with ([] ++ [DForce]) in H. 
    now apply repeat_eq_elt in H. 
  }
  apply ideal_eval_seq_eval in H. econstructor; [eassumption|].
  now eapply IHmulti_ideal; eauto.
Qed.

Lemma ideal_eval_small_step_obs_length : forall c st ast b ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  length ds = length os.
Proof. intros. induction H; simpl; auto. Qed.

Lemma ideal_terminal_no_step : forall c st ast b ct stt astt bt ds os pc P PA pct Pt PAt,
  terminal c ->
  <[[ c, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[ ct, stt, astt, bt, pct, Pt, PAt]]> ->
  False.
Proof. intros. revert ct H0. induction H; intros; [invert H0|invert H0]. eapply IHterminal, H18. Qed.

Lemma ideal_eval_small_step_same_length :
  forall c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2
    pc1 P1 PA1 pc2 P2 PA2 pct1 Pt1 PAt1 pct2 Pt2 PAt2,
  <[[c, st1, ast1, b1, pc1, P1, PA1]]> -->i_ds1^^os1 <[[ct1, stt1, astt1, bt1, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, b2, pc2, P2, PA2]]> -->i_ds2^^os2 <[[ct2, stt2, astt2, bt2, pct2, Pt2, PAt2]]> ->
  length ds1 = length ds2.
Proof.
  intros. revert st2 ast2 b2 ct2 stt2 astt2 bt2 pc2 P2 PA2 pct2 Pt2 PAt2 H0.
  induction H; simpl; intros.
  + now invert H0.
  + invert H0; [|now apply ideal_terminal_no_step in H].
    eapply IHideal_eval_small_step; eassumption.
  + invert H0; [now apply ideal_terminal_no_step in H20|reflexivity].
  + now invert H1.
  + now invert H1.
  + now invert H0.
  + now invert H2.
  + now invert H3.
  + now invert H4.
  + now invert H4.
  + invert H0. eapply IHideal_eval_small_step, H18.
Qed.

Lemma multi_ideal_obs_length : forall c st ast b ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  length ds = length os.
Proof. intros. induction H; [tauto|].
  do 2 rewrite length_app. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_eval_small_step_spec_bit_monotonic : forall c st ast ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, true, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall c st ast ds ct stt astt bt os pc P PA pct Pt PAt,
  <[[c, st, ast, true, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma ideal_eval_small_step_no_spec : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i_ds^^os <[[ct, stt, astt, false, pct, Pt, PAt]]> ->
  ds = [DStep] \/ ds = [].
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; try discriminate; (try now left); (try now right);
    now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_no_spec : forall c st ast ct stt astt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, false, pct, Pt, PAt]]> ->
  exists n, ds = repeat DStep n.
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; [now exists 0|].
  destruct b'; [now apply multi_ideal_spec_bit_monotonic in H0|].
  apply ideal_eval_small_step_no_spec in H. destruct IHmulti_ideal as (n&->); [reflexivity..|].
  destruct H; subst; [|now exists n].
  exists (1 + n). now rewrite repeat_app.
Qed.

Lemma multi_ideal_spec_bit_deterministic : forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2
  pc1 pc2 P1 P2 PA1 PA2 pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  <[[ c, st1, ast1, b, pc1, P1, PA1 ]]> -->i*_ ds ^^ os1 <[[ c1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, b, pc2, P2, PA2 ]]> -->i*_ ds ^^ os2 <[[ c2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  bt1 = bt2.
Proof.
  intros. destruct b.
  + apply multi_ideal_spec_bit_monotonic in H, H0. congruence.
  + destruct bt1, bt2; try reflexivity.
    1:rename H into H1. 1:rename H0 into H2.
    2:rename H0 into H1. 2:rename H into H2.
    all:apply multi_ideal_no_spec in H2.
    all:apply multi_ideal_spec_needs_force in H1.
    all:destruct H2 as (n&->).
    all:now apply repeat_spec in H1.
Qed.

Lemma ideal_eval_small_step_dirs_obs : forall c st ast b ct stt astt bt ds os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ ds ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  (ds = [] /\ os = []) \/ (exists d o, ds = [d] /\ os = [o]).
Proof. intros. now induction H; eauto. Qed.

Lemma ideal_eval_small_step_force_obs : forall c st1 st2 ast1 ast2 stt1 stt2 astt1 astt2 os1 os2 c1 c2
  pc1 pc2 P1 P2 PA1 PA2 pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[ c, st1, ast1, false, pc1, P1, PA1 ]]> -->i_[DForce] ^^ os1 <[[ c1, stt1, astt1, true, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, false, pc2, P2, PA2 ]]> -->i_[DForce] ^^ os2 <[[ c2, stt2, astt2, true, pct2, Pt2, PAt2 ]]> ->
  os1 = os2.
Proof.
   intros. remember false as b in H0. remember true as bt in H0. remember [DForce] as ds in H0.
   revert st2 ast2 stt2 astt2 os2 c2 c2 P2 PA2 pct2 Pt2 PAt2 Heqb Heqbt Heqds H H1.
   induction H0; intros; subst; try discriminate.
   - invert H1. apply seq_same_obs_com_seq in H.
     eapply IHideal_eval_small_step; [tauto..|eassumption|eassumption].
   - invert H2. now apply seq_same_obs_com_if in H1 as <-.
   - invert H1. eapply IHideal_eval_small_step; [tauto..|eassumption|eassumption] .
Qed.

Lemma ideal_eval_small_step_silent_step : forall c st ast b ct stt astt bt pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i_ [] ^^ [] <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  b = bt /\ ast = astt /\ PA = PAt.
Proof. intros. remember [] as ds in H at 1. revert Heqds. induction H; try now intros; eauto. Qed.

Lemma ideal_eval_small_step_silent_step_same_prog :
  forall c st1 st2 ast1 ast2 b ct1 ct2 stt1 stt2 astt1 astt2 bt pc pct1 pct2 P Pt1 Pt2 PA PAt1 PAt2, 
  <[[c, st1, ast1, b, pc, P, PA]]> -->i_ [] ^^ [] <[[ct1, stt1, astt1, bt, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, b, pc, P, PA]]> -->i_ [] ^^ [] <[[ct2, stt2, astt2, bt, pct2, Pt2, PAt2]]> ->
  ct1 = ct2.
Proof.
  induction c; intros; invert H; invert H0; try tauto.
  - erewrite IHc1 with (ct1 := c1t). 2, 3: eassumption. reflexivity.
  - now eapply ideal_terminal_no_step in H20.
  - now eapply ideal_terminal_no_step in H20.
  - erewrite IHc with (ct1 := c1t). 2, 3: eassumption. reflexivity.
Qed.

Lemma multi_ideal_silent : forall c st ast b ct stt astt bt pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ [] ^^ [] <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  b = bt /\ ast = astt /\ PA = PAt.
Proof.
  intros. remember [] as ds. remember [] as os in H. induction H in Heqos, Heqds |- *.
  - tauto.
  - destruct IHmulti_ideal as (<-&<-&<-). 1: now apply app_eq_nil in Heqds. 1: now apply app_eq_nil in Heqos.
    eapply ideal_eval_small_step_silent_step. apply app_eq_nil in Heqds as (->&->), Heqos as (->&->). eassumption.
Qed.

Lemma ideal_eval_small_step_deterministic_labels:
  forall {c st1 st2 ast1 ast2 b ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 ds os1 os2 pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2},
  seq_same_obs (erase c) st1 st2 ast1 ast2 -> 
  <[[ c, st1, ast1, b, pc, P, PA ]]> -->i_ ds ^^ os1 <[[ ct1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, b, pc, P, PA ]]> -->i_ ds ^^ os2 <[[ ct2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  ct1 = ct2 /\ bt1 = bt2 /\ pct1 = pct2 /\ Pt1 = Pt2 /\ PAt1 = PAt2.
Proof.
  induction c; intros; invert H0; invert H1; try tauto.
  - eapply IHc1 in H20. 2: { cbn in H. eapply seq_same_obs_com_seq. eassumption. } 2: eassumption. now firstorder; subst.
  - eapply ideal_terminal_no_step in H21. 1: easy.
    eassumption.
  - eapply ideal_terminal_no_step in H21. 1: easy.
    eassumption.
  - firstorder.
    cbn in H. now apply seq_same_obs_com_if in H as ->.
  - firstorder.
    now apply seq_same_obs_com_if in H as ->.
  - eapply IHc in H18. 2, 3: eassumption.
    firstorder. now subst.
Qed.

Lemma multi_ideal_factorize : forall c st ast b ct stt astt bt d ds os pc P PA pct Pt PAt,
  <[[c, st, ast, b, pc, P, PA]]> -->i*_ (d :: ds) ^^ os <[[ct, stt, astt, bt, pct, Pt, PAt]]> ->
  exists c' st' pc' ct' stt' astt' bt' o os' P' pct' Pt' PAt',
  os = o :: os' /\
  <[[c, st, ast, b, pc, P, PA]]> -->i*_[]^^[] <[[c', st', ast, b, pc', P', PA]]> /\
  <[[c', st', ast, b, pc', P', PA]]> -->i_[d]^^[o] <[[ct', stt', astt', bt', pct', Pt', PAt']]> /\
  <[[ct', stt', astt', bt', pct', Pt', PAt']]> -->i*_ds^^os' <[[ct, stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. remember (d :: ds) as ds'. revert d ds Heqds'. induction H; intros; try discriminate.
  apply ideal_eval_small_step_dirs_obs in H as Heq.
  destruct Heq.
  + destruct H1. subst. simpl in Heqds'. subst. simpl.
    specialize (IHmulti_ideal d ds Logic.eq_refl).
    destruct IHmulti_ideal as (?&?&?&?&?&?&?&?&?&?&?&?&?&->&?&?&?).
    apply ideal_eval_small_step_silent_step in H as Heq. destruct Heq as (->&->&->).
    eapply multi_ideal_trans in H1; [|apply H]. simpl in H1.
    repeat eexists; eassumption.
  + destruct H1 as (d'&o&->&->). simpl in Heqds'. invert Heqds'. simpl.
    repeat eexists; [|eassumption..]. now constructor.
Qed.

Lemma multi_ideal_preserves_seq_same_obs : forall c st1 st2 ast1 ast2 ct stt1 stt2 astt1 astt2 ds os1 os2
    pc1 pc2 P1 P2 PA1 PA2 pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[c, st1, ast1, false, pc1, P1, PA1]]> -->i*_ds^^os1 <[[ct, stt1, astt1, false, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, false, pc2, P2, PA2]]> -->i*_ds^^os2 <[[ct, stt2, astt2, false, pct2, Pt2, PAt2]]> ->
  seq_same_obs (erase ct) stt1 stt2 astt1 astt2.
Proof.
  unfold seq_same_obs. intros.
  apply multi_ideal_obs_length in H0 as Heq, H1 as Heq'.
  rewrite Heq' in Heq. clear Heq'.
  apply multi_ideal_no_spec in H0 as Heq'.
  destruct Heq' as (n&->).
  apply multi_ideal_multi_seq in H0, H1.
  eapply H in H0 as Hpref; [|eassumption]. apply prefix_eq_length in Heq; [|tauto].
  subst. clear Hpref. eapply multi_seq_combined_executions in H2; [|eassumption].
  eapply multi_seq_combined_executions in H3; [|eassumption].
  eapply H in H2; [|eassumption]. destruct H2; apply prefix_append_front in H2; tauto.
Qed.

Lemma seq_same_obs_multi_ideal_factorize : 
  forall c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 d ds os1 os2 pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 -> 
  <[[ c, st1, ast1, false, pc, P, PA ]]> -->i*_ d::ds ^^ os1 <[[ ct1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, false, pc, P, PA ]]> -->i*_ d::ds ^^ os2 <[[ ct2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  exists o1 o2 os1' os2' c' c'' st1' st2' st1'' st2'' b'' ast1'' ast2'' pc' pc'' P' P'' PA'',
  os1 = o1 :: os1' /\
  os2 = o2 :: os2' /\
  <[[ c, st1, ast1, false, pc, P, PA]]> -->i*_[]^^[] <[[ c', st1', ast1, false, pc', P', PA]]> /\
  <[[ c', st1', ast1, false, pc', P', PA]]> -->i_[d]^^[o1] <[[ c'', st1'', ast1'', b'', pc'', P'', PA'']]> /\
  <[[ c'', st1'', ast1'', b'', pc'', P'', PA'']]> -->i*_ds ^^ os1' <[[ ct1, stt1, astt1, bt1, pct1, Pt1, PAt1]]> /\
  <[[ c, st2, ast2, false, pc, P, PA]]> -->i*_[]^^[] <[[ c', st2', ast2, false, pc', P', PA]]> /\
  <[[ c', st2', ast2, false, pc', P', PA]]> -->i_[d]^^[o2] <[[ c'', st2'', ast2'', b'', pc'', P'', PA'']]> /\
  <[[ c'', st2'', ast2'', b'', pc'', P'', PA'']]> -->i*_ds ^^ os2' <[[ ct2, stt2, astt2, bt2, pct2, Pt2, PAt2]]>.
Proof.
  intros. remember (d :: ds) as ds'. remember false as b in H0, H1.
  revert Heqb d ds Heqds' st2 ast2 ct2 stt2 astt2 bt2 os2 pct2 Pt2 PAt2 H H1.
  induction H0; intros; try discriminate.
  inversion H2. { rewrite <- H11 in Heqds'. discriminate. }
  subst.
  apply ideal_eval_small_step_dirs_obs in H as Heq1, H4 as Heq2. destruct Heq1, Heq2.
  - destruct H5, H6; subst. simpl in *. subst.
    apply ideal_eval_small_step_silent_step in H as Heq. destruct Heq as (<-&->&->).
    specialize (IHmulti_ideal Logic.eq_refl d ds Logic.eq_refl).
    assert (seq_same_obs (erase c') st' st'0 ast' ast'0).
    {
      apply ideal_eval_small_step_silent_step in H4 as Heq. destruct Heq as (<-&->&->).
      eapply ideal_eval_small_step_silent_step_same_prog in H as Heq. 2: exact H4. subst.
      eapply multi_ideal_preserves_seq_same_obs. 1: eassumption.
      - eapply multi_ideal_trans. 2: econstructor. eassumption.
      - eapply multi_ideal_trans. 1: eassumption. econstructor.
    }
    pose proof (ideal_eval_small_step_deterministic_labels H1 H H4) as (<- & <- & <- & <- & <-).
    eapply IHmulti_ideal in H3. 2: eassumption.
    destruct H3 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&->&->&?&?&?&?&?&?).
    (*apply ideal_eval_small_step_silent_step in H as Heq. destruct Heq as (->&->&->).*)
    eapply multi_ideal_trans in H, H4. 2, 3: eassumption.
    eapply multi_ideal_silent in H4 as Heq. destruct Heq as (_&<-&_).
    repeat eexists; try eassumption.
  - destruct H5 as (->&->). destruct H6 as (?&?&->&->). simpl in *. subst.
    exfalso.
    clear - H H4.
    eapply ideal_eval_small_step_same_length in H; [|eassumption..]. simpl in H. congruence.
  - destruct H6 as (->&->). destruct H5 as (?&?&->&->). simpl in *. subst.
    exfalso. clear - H H4.
    eapply ideal_eval_small_step_same_length in H; [|eassumption..]. simpl in H. congruence.
  - destruct H5 as (?&?&->&->), H6 as (?&?&->&->). simpl in Heqds'. invert Heqds'. simpl in *. invert H3.
    pose proof (multi_ideal_refl c st2 ast2 false pc P PA).
    pose proof (multi_ideal_refl c st ast false pc P PA).
    pose proof (ideal_eval_small_step_deterministic_labels H1 H H4) as (<-&<-&<-&<-&<-).
    repeat eexists; try eassumption.
Qed.


Lemma pub_equiv_join : forall {A} P P' (st st' : total_map A),
  pub_equiv P st st' ->
  pub_equiv (join_pub_vars P P') st st'.
Proof. intros. intros x Hx. apply andb_prop in Hx. now apply H. Qed.

Lemma join_pub_vars_sym : forall P P',
  join_pub_vars P P' = join_pub_vars P' P.
Proof. intros. apply FunctionalExtensionality.functional_extensionality. intro x. apply andb_comm. Qed.

Lemma ideal_eval_pc_of_acom:
  forall ac st ast b pc P PA ds os ac' st' ast' b' pc' P' PA' Pt PAt,
  well_labeled_acom ac P PA pc Pt PAt ->
  <[[ ac, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[ ac', st', ast', b', pc', P', PA']]> ->
  pc_of_acom pc ac = pc_of_acom pc' ac'.
Proof.
  induction ac; intros; invert H0; try easy.
  - simpl. f_equal. eapply IHac1. 2: eassumption.
    simpl in H. apply H.
Qed.

Lemma well_labeled_terminal_less_precise : 
  forall ac P PA pc P' PA',
  well_labeled_acom ac P PA pc P' PA' ->
  terminal ac ->
  less_precise P' P /\ less_precise PA' PA.
Proof.
  induction ac; simpl; intros; invert H0; [assumption | eapply IHac; eassumption ].
Qed.

Lemma ideal_eval_preserves_well_labeled : 
  forall ac ds P PA Pt PAt pc' P' PA' pc st ast b act stt astt bt os, 
  well_labeled_acom ac P PA pc Pt PAt ->
  <[[ ac, st , ast, b, pc, P, PA ]]> -->i_ds^^os <[[ act, stt, astt, bt, pc', P', PA' ]]> ->
  well_labeled_acom act P' PA' pc' Pt PAt.
Proof.
  induction ac; intros.
  - inversion H0.
  - invert H0. exact H.
  - invert H0.
    + simpl in H |-*. destruct H. split. 1: assumption. split.
      * eapply IHac1; try eassumption. apply H0.
      * eapply ideal_eval_pc_of_acom in H20 as <-. 1, 2: apply H0.
    + simpl in H. 
      eapply well_labeled_terminal_less_precise in H20; [|apply H].
      eapply well_labeled_strengthen_pre; try apply H; apply H20.
  - invert H0.
    + simpl in H |-*. destruct ((lbe || negb bt) && beval stt be); tauto.
    + simpl in H |-*. destruct ((lbe || negb b) && beval stt be); tauto.
  - invert H0. simpl in H |-*. destruct H as (?&?&?&?&?&?&?). repeat split; try assumption.
    + eapply can_flow_trans;[|eassumption]. now apply label_of_bexp_less_precise. 
    + eapply well_labeled_strengthen_pre; eassumption.
    + apply less_precise_refl.
    + apply less_precise_refl.
    + eapply branch_free_pc_of_acom in H0 as ->. now destruct pc', lbe.
    + eapply less_precise_trans; eassumption.
    + eapply less_precise_trans; eassumption.
  - invert H0; simpl in *; tauto.
  - invert H0; simpl in *; tauto.
  - invert H0. simpl in *. eapply IHac; eassumption.
Qed.

Lemma multi_ideal_preserves_well_labeled : 
  forall ac ds P PA Pt PAt pc' P' PA' pc st ast b act stt astt bt os, 
  well_labeled_acom ac P PA pc Pt PAt ->
  <[[ ac, st , ast, b, pc, P, PA ]]> -->i*_ds^^os <[[ act, stt, astt, bt, pc', P', PA' ]]> ->
  well_labeled_acom act P' PA' pc' Pt PAt.
Proof.
  intros. induction H0.
  - assumption.
  - apply IHmulti_ideal.
    eapply ideal_eval_preserves_well_labeled; eassumption.
Qed.

Lemma ideal_eval_noninterferent :
  forall ac ds P PA P' PA' pc st1 ast1 st2 ast2 b act1 act2 stt1 stt2 astt1 astt2 bt1 bt2 os pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  well_labeled_acom ac P PA pc P' PA' ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA ast1 ast2) ->
  <[[ ac, st1, ast1, b, pc, P, PA ]]> -->i_ds^^os <[[ act1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ ac, st2, ast2, b, pc, P, PA ]]> -->i_ds^^os <[[ act2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  act1 = act2 /\ bt1 = bt2 /\ pct1 = pct2 /\ Pt1 = Pt2 /\ PAt1 = PAt2 /\
  pub_equiv Pt1 stt1 stt2 /\ (bt1 = false -> pub_equiv PAt1 astt1 astt2).
Proof.
  induction ac; intros; invert H2; invert H3; try easy.
  - repeat split; try tauto. 
    unfold pub_equiv, t_update. intros y. destruct (x =? y).
    + destruct pct2; simpl. 2: congruence.
      intros. eapply noninterferent_aexp. 1: eassumption.
      unfold public. rewrite <- H2. apply label_of_aexp_sound.
    + apply H0.
  - eapply IHac1 in H22; try eassumption. 2: apply H.
      firstorder. subst. reflexivity.
  - now apply ideal_terminal_no_step in H23.
  - now apply ideal_terminal_no_step in H22.
  - repeat split; try tauto. 
    unfold pub_equiv, t_update. intros y. destruct (x =? y).
    + intros ->. cbn in *. destruct li, bt2. 1, 3, 4: easy (* contradiction in H for 3 and 4*).
      rewrite H1; try reflexivity.
      destruct PAt2; easy.
    + apply H0.
  - repeat split; try tauto. 
    unfold pub_equiv, t_update. intros y. destruct (x =? y).
    + now intros ->.
    + apply H0.
  - repeat split; try tauto. intros ->. simpl in *. 
    unfold pub_equiv, t_update. intros b. destruct (a =? b).
    + destruct (PA a) eqn: HeqPA, pct2, li, (label_of_aexp Pt2 e) eqn: Heqle; try easy.
      unfold pub_equiv in H1. rewrite H1; try easy. intros _.
      f_equal. eapply noninterferent_aexp. 1: eassumption.
      unfold public. rewrite <- Heqle. apply label_of_aexp_sound.
    + apply H1. reflexivity.
  - eapply IHac in H20; try eassumption. firstorder. now subst.
Qed.

Definition acom_unused X ac := unused X (erase ac).

Lemma ideal_eval_preserves_nonempty_arrs : forall ac st ast b act stt astt bt ds os pc pct P Pt PA PAt,
  nonempty_arrs ast ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  nonempty_arrs astt.
Proof.
  intros.
  induction H0; [tauto..|now apply t_update_nonempty_arrs|now apply t_update_nonempty_arrs|tauto].
Qed.

Lemma multi_ideal_preserves_nonempty_arrs : forall ac st ast b act stt astt bt ds os pc pct P Pt PA PAt,
  nonempty_arrs ast ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  nonempty_arrs astt.
Proof.
  intros. induction H0; [tauto|].
  apply ideal_eval_preserves_nonempty_arrs in H0; tauto.
Qed.

Lemma ideal_unused_overwrite : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]> /\
  acom_unused X act.
Proof.
unfold acom_unused. intros. induction H0; simpl in *.
  + split; [|tauto]. rewrite t_update_permute; [|tauto]. constructor. now rewrite aeval_unused_update.
  + repeat constructor; tauto.
  + now repeat constructor.
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [now rewrite beval_unused_update|tauto].
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [now rewrite beval_unused_update|tauto].
  + repeat constructor; [tauto|subst]. simpl. tauto.
  + split; [|trivial]. rewrite t_update_permute; [|tauto].
    econstructor; [now rewrite aeval_unused_update|eassumption|tauto].
  + split; [|trivial]. rewrite t_update_permute; [|tauto].
    econstructor; [now rewrite aeval_unused_update|eassumption..].
  + split; [|trivial]. econstructor; [| |eassumption..]; now rewrite ?aeval_unused_update.
  + split; [|trivial]. econstructor; try tauto. all: now rewrite aeval_unused_update.
  + destruct IHideal_eval_small_step; [tauto|]. split; [|tauto]. now constructor.
Qed.

Lemma multi_ideal_unused_overwrite : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. induction H0; [constructor|].
  eapply ideal_unused_overwrite in H0; [|eassumption].
  destruct H0. now econstructor; eauto.
Qed.

Lemma multi_ideal_unused_update : forall ac st ast b act stt astt bt ds os X n pc pct P Pt PA PAt,
  acom_unused X ac ->
  <[[ac, X !-> n; st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> n; stt, astt, bt, pct, Pt, PAt]]> ->
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[act, X !-> st X; stt, astt, bt, pct, Pt, PAt]]>.
Proof.
  intros. eapply multi_ideal_unused_overwrite with (n:=st X) in H0; [|eassumption].
  now rewrite !t_update_shadow, t_update_same in H0.
Qed.

Fixpoint acom_size (c :acom) :nat :=
  match c with
  | <[ c1;@(_,_) c2 ]> => 1 + (acom_size c1) + (acom_size c2)
  (* For conditionals the maximum of both branches is tighter, but a
     looser bound based on blindly "counting all constructors"
     (commented here) works just as well, and is easier to explain on
     paper *)
  | <[ if _@_ then ct else cf end ]> => 1 + max (acom_size ct) (acom_size cf)
  (* | <{{ if be then ct else cf end }}> => 1 + (com_size ct) + (com_size cf) *)
  | <[ while _@_ do cw@(_,_) end ]> => 1 + (acom_size cw)
  | <[ branch l c ]> => 1 + acom_size c
  | _  => 1
  end.

Definition prog_size (c :acom) (ds :dirs) :nat := acom_size c + length ds.

(** The induction principle on [prog_size] *)

Lemma prog_size_ind :
  forall P : acom -> dirs -> Prop,
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
  (acom_size c1 < acom_size c2 /\ length ds1 <= length ds2 ) \/
  (acom_size c1 <= acom_size c2 /\ length ds1 < length ds2) ->
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
        [| repeat rewrite length_app]; lia );
  try ( apply prog_size_monotonic; right; split; simpl;
        [| repeat rewrite length_app]; lia);
  try ( apply prog_size_monotonic; left; split; simpl;
        [auto | repeat rewrite length_app; lia] ).

Ltac solve_refl :=
  now (do 5 eexists); split; [|split; [(try discriminate); (try now repeat econstructor)|(try discriminate); tauto] ]; rewrite ?t_update_shadow, t_update_same;
  repeat econstructor; (repeat rewrite_eq); rewrite ?andb_false_r; (try now apply label_of_exp_sound).

Lemma flex_slh_acom_bcc_generalized : forall ac st ast c' st' ast' os ds (b b' : bool) pc P PA,
  nonempty_arrs ast ->
  acom_unused "b" ac ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh_acom ac, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' ac' pc' P' PA',
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', "b" !-> st "b"; st'', ast', b', pc', P', PA']]> /\
  (c' = <{{ skip }}> -> terminal ac' /\ st' "b" = (if b' then 1 else 0) /\ st' = st'').
Proof.
  intros until ds. revert st ast c' st' ast' os. eapply prog_size_ind with (c:=ac) (ds:=ds).
clear. intros until PA. intros Harrs Hunused st_b Hexec. destruct c; simpl in *.
  + invert Hexec; [|inversion H0]. eexists. exists <[ skip ]>, pc, P, PA. split; [|split; [constructor|tauto] ]. rewrite t_update_same. constructor.
  + invert Hexec; [solve_refl|]. invert H0. invert H1; [|inversion H0]. eexists. exists <[skip]>. do 3 eexists. rewrite t_update_neq; [|now invert Hunused]. split; [|split; [constructor|tauto] ].
    rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. now repeat econstructor.
  + apply multi_spec_seq in Hexec. destruct Hexec.
    - destruct H0 as (?&?&?&?&?&?&?&->&->&?&?). apply spec_eval_preserves_nonempty_arrs in H0 as ?; [|tauto].
      invert Hunused. eapply H in H0; [|prog_size_auto|tauto..]. destruct H0 as (?&?&?&?&?&?&(?&?&->)); [tauto|].
      eapply H in H1; [|prog_size_auto|tauto..]. destruct H1 as (?&?&?&?&?&?&?). do 5 eexists. split; [|apply H7].
      eapply multi_ideal_unused_overwrite in H1; [|apply H4]. rewrite t_update_shadow in H1.
      eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H0|].
      rewrite <- app_nil_l with (l:=x3). rewrite <- app_nil_l with (l:=x5). econstructor; [|apply H1]. now constructor.
    - destruct H0 as (?&->&?). invert Hunused. eapply H in H0; [|prog_size_auto|tauto..]. destruct H0 as (?&?&?&?&?&?&?).
      do 5 eexists. split; [|discriminate]. apply multi_ideal_add_snd_com. apply H0.
  + invert Hexec; [solve_refl|]. invert H0.
    - destruct ((lbe || negb b'0) && beval st'0 be) eqn:Heq.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'0, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1.
        invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0, t_update_same in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. exists x, <[ branch pc x0 ]>. do 3 eexists. split; [|intro H'; apply H2 in H'; destruct H'; split; [now constructor|tauto] ].
        rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq; [reflexivity|]. apply multi_ideal_branch, H1.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'0, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0, t_update_same in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. exists x, <[branch pc x0]>. do 3 eexists. split; [|intro H'; apply H2 in H'; destruct H'; split; [now constructor|tauto] ].
        rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq; [tauto|apply multi_ideal_branch, H1].
    - destruct ((lbe || negb b) && beval st'0 be) eqn:Heq.
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0 in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused].
        exists x, <[branch pc x0]>. do 3 eexists. split; [|split; (destruct H2; [tauto|]); [now constructor|tauto] ]. rewrite !app_nil_l, H0.
        repeat econstructor; rewrite ?Heq; [tauto|apply multi_ideal_branch, H1].
      * assert (beval st'0 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b, (beval st'0 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H1. invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H2. invert H14. invert H3. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; rewrite H0, ?Heq, ?t_update_same; constructor. }
        invert H1; [inversion H14|]. simpl in H2. rewrite H0 in H2.
        eapply H in H2; [|prog_size_auto|tauto|now invert Hunused|tauto].
        destruct H2, H1, H1, H1, H1, H1. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused].
        exists x, <[branch pc x0]>. do 3 eexists. split; [|split; (destruct H2; [tauto|]); [now constructor|tauto] ]. rewrite !app_nil_l, H0.
        repeat econstructor; rewrite ?Heq; [tauto|apply multi_ideal_branch, H1].
  + invert Hexec; [solve_refl|]. invert H0. invert H13. invert H1; [solve_refl|]. invert H0. invert H13.
    - destruct ((lbe || negb b'1) && beval st'1 be) eqn:Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'1, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1. invert H14. invert H13. invert H14. apply multi_spec_seq_assoc in H3. destruct H3, H1.
        invert H1. { do 5 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate].
        do 2 econstructor; [reflexivity|constructor; [now rewrite H0, Heq|reflexivity] |simpl; rewrite t_update_same; constructor]. }
        invert H3. invert H15; [inversion H14|]. apply multi_spec_seq in H4. destruct H4.
        ++ do 8 destruct H1. destruct H3, H4. remember (if lbe then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh_acom c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh_acom <[ while be@lbe do c@(P0,PA0) end ]>) in H5
             by now simpl; rewrite Heqbe'.
           subst. simpl in H4. rewrite H0, t_update_same in H4. eapply H in H4; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H4, H1, H1, H1, H1, H1, H3; [tauto|]. destruct H4. subst. eapply multi_ideal_preserves_nonempty_arrs in H1 as Harrs'; [|tauto].
           eapply H in H5; [|prog_size_auto|tauto|now invert Hunused|tauto]. destruct H5,H5, H5, H5, H5, H5. eapply multi_ideal_unused_overwrite in H5; [|eassumption].
           rewrite t_update_shadow in H5. exists x0, <[branch pc x12]>. do 3 eexists. split; [|intro Hc'; split; [constructor|]; tauto].
           do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           simpl. apply multi_ideal_branch. eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H1|]. change x4 with ([] ++ x4). change x6 with ([] ++ x6).
           now econstructor; [apply ISM_Seq_Skip|eassumption].
        ++ do 2 destruct H1. subst. simpl in H3. rewrite H0, t_update_same in H3. eapply H in H3; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H3, H1, H1, H1, H1, H1. do 5 eexists. split; [|intro Habs; apply H2 in Habs; discriminate]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           apply multi_ideal_branch. apply multi_ideal_add_snd_com, H1.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'1, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1; [invert H14|]. invert H3; [solve_refl|]. invert H1. invert H2; [|inversion H1].
        do 5 eexists. split; [|split; [apply Terminal_Branch, Terminal_Skip|]; simpl; rewrite H0, t_update_eq, t_update_same; tauto]. rewrite t_update_same.
        do 2 econstructor; [constructor..|simpl; constructor]; now rewrite H0, ?Heq.
    - destruct ((lbe || negb b'0) && beval st'1 be) eqn:Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct b'0, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1; [invert H14|]. invert H3; [solve_refl|]. invert H1. invert H2; [|inversion H1].
        do 5 eexists. split; [|split; [apply Terminal_Branch, Terminal_Skip|]; simpl; rewrite H0, t_update_eq; tauto]. rewrite t_update_shadow, t_update_same.
        do 2 econstructor; [constructor..|simpl; constructor]; now rewrite H0, ?Heq.
      * assert (beval st'1 (if lbe then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct b'0, (beval st'1 be) eqn:Hbe, lbe; simpl; rewrite ?st_b, ?Hbe; try discriminate.
        rewrite H0 in H2. invert H2; [solve_refl|]. invert H1. invert H14. invert H13. invert H14. apply multi_spec_seq_assoc in H3. destruct H3, H1.
        invert H1. { do 5 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate].
        do 2 econstructor; [reflexivity|constructor; [now rewrite H0, Heq|reflexivity] |simpl; rewrite t_update_same; constructor]. }
        invert H3. invert H15; [inversion H14|]. apply multi_spec_seq in H4. destruct H4.
        ++ do 8 destruct H1. destruct H3, H4. remember (if lbe then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh_acom c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh_acom <[ while be@lbe do c @(P0,PA0) end ]>) in H5
             by now simpl; rewrite Heqbe'.
           subst. simpl in H4. rewrite H0 in H4. eapply H in H4; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H4, H1, H1, H1, H1, H1, H3; [tauto|]. destruct H4. subst. eapply multi_ideal_preserves_nonempty_arrs in H1 as Harrs'; [|tauto].
           eapply H in H5; [|prog_size_auto|tauto|now invert Hunused|tauto]. destruct H5, H5, H5, H5, H5, H5. eapply multi_ideal_unused_overwrite in H5; [|eassumption].
           rewrite t_update_shadow in H5. exists x0, <[branch pc x12]>. do 3 eexists. split; [|intro Hc'; split; [constructor|]; tauto ]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           simpl. rewrite t_update_eq in H1. eapply multi_ideal_unused_update in H1; [|now invert Hunused]. apply multi_ideal_branch.
           eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H1|]. change x4 with ([] ++ x4). change x6 with ([] ++ x6).
           econstructor; [apply ISM_Seq_Skip|]; eassumption.
        ++ do 2 destruct H1. subst. simpl in H3. rewrite H0 in H3. eapply H in H3; [|prog_size_auto|tauto|now invert Hunused|tauto].
           destruct H3, H1, H1, H1, H1, H1. do 5 eexists. split; [|intro Habs; apply H2 in Habs; discriminate]. do 2 econstructor; [reflexivity|constructor; rewrite H0, ?Heq; reflexivity|].
           rewrite t_update_eq in H1. apply multi_ideal_unused_update in H1; [|now invert Hunused]. apply multi_ideal_branch, multi_ideal_add_snd_com, H1.
  + destruct (lx&&li) eqn:Heq.
    - apply andb_prop in Heq. destruct Heq. subst.
      invert Hexec; [solve_refl|]. invert H0. invert H13.
      * invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0; [inversion H13|]. invert H2. { do 5 eexists. split; [|discriminate]. rewrite app_nil_l. repeat econstructor; [tauto|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite !app_nil_l. repeat econstructor; [tauto|]. simpl. rewrite t_update_neq; [|now invert Hunused].
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same, t_update_eq, st_b. now destruct b'; constructor.
      * invert H1. { do 5 eexists. split; [|discriminate]. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [|now invert Hunused]. constructor. }
        invert H0; [inversion H13|]. invert H2. { do 5 eexists. split; [|discriminate]. rewrite !app_nil_l. repeat econstructor; [tauto..|].
        rewrite <- t_update_same with (m:=st) (x:="b") at 1. rewrite t_update_permute; [constructor|now invert Hunused]. }
        invert H0. invert H1; [|inversion H0]. rewrite t_update_shadow. rewrite t_update_neq; [|now invert Hunused].
        do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite !app_nil_l. repeat econstructor; [tauto..|]. rewrite t_update_permute; [|now invert Hunused].
        rewrite t_update_same. simpl. rewrite t_update_neq; [|now invert Hunused]. rewrite st_b. constructor.
    - invert Hexec; [solve_refl|]. invert H0.
      * invert H1; [|inversion H0]. rewrite t_update_neq; [|now invert Hunused]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ].
        repeat econstructor; [|tauto|]. { destruct lx, li, b'; simpl in *; rewrite ?st_b; try reflexivity; discriminate. }
        rewrite t_update_permute; [|now invert Hunused]. rewrite t_update_same. destruct li, lx, b'; simpl; rewrite ?st_b; try constructor; discriminate.
      * invert H1; [|inversion H0]. do 5 eexists. rewrite t_update_neq; [|now invert Hunused]. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_permute; [|now invert Hunused].
        rewrite t_update_same. repeat econstructor. destruct li; [repeat constructor; rewrite andb_true_r in Heq; subst; tauto|].
        simpl in H15. rewrite st_b in H15. simpl in H15. specialize (Harrs a). lia.
  + invert Hexec; [solve_refl|]. invert H0.
    - invert H1; [|inversion H0]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_same. repeat econstructor; [|tauto].
      now destruct b', li; simpl; rewrite ?st_b.
    - invert H1; [|inversion H0]. do 5 eexists. split; [|split; [apply Terminal_Skip|tauto] ]. rewrite t_update_same. destruct li; [now repeat econstructor|].
      simpl in H16. rewrite st_b in H16. simpl in H16. specialize (Harrs a). lia.
  + eapply H in Hexec; [|prog_size_auto|tauto..]. destruct Hexec as (st''&ac'&?&?&?&?&?). exists st'', <[branch lbl ac']>. do 3 eexists. split; [|split; [constructor|]; tauto].
    apply multi_ideal_branch. eassumption.
Qed.

Lemma flex_slh_acom_bcc : forall ac st ast c' st' ast' os ds (b b' : bool) pc P PA,
  nonempty_arrs ast ->
  acom_unused "b" ac ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh_acom ac, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' ac' pc' P' PA',
  <[[ac, st, ast, b, pc, P, PA]]> -->i*_ds^^os <[[ac', "b" !-> st "b"; st'', ast', b', pc', P', PA']]>.
Proof.
  intros. eapply flex_slh_acom_bcc_generalized in H2; [|tauto..].
  destruct H2 as (st''&ac'&?&?&?&?&?). now eauto 20.
Qed.

Lemma ideal_misspeculated_unwinding_one_step :
  forall ac P PA P' PA' pc st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds
    pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  well_labeled_acom ac P PA pc P' PA' ->
  pub_equiv P st1 st2 ->
  <[[ac, st1, ast1, true, pc, P, PA]]> -->i_ds^^os1 <[[ct1, stt1, astt1, true, pct1, Pt1, PAt1]]> ->
  <[[ac, st2, ast2, true, pc, P, PA]]> -->i_ds^^os2 <[[ct2, stt2, astt2, true, pct2, Pt2, PAt2]]> ->
  os1 = os2 /\ ct1 = ct2.
Proof.
  induction ac; intros; invert H1; invert H2; try easy.
  - eapply IHac1 in H21; try eassumption. 2: apply H. destruct H21 as (->&->). split; reflexivity.
  - now apply ideal_terminal_no_step in H22.
  - now apply ideal_terminal_no_step in H22.
  - cbn in H|-*. destruct (label_of_bexp Pt2 be) eqn: Heq, lbe; cbn in *. 2-4: easy.
    eapply noninterferent_bexp in H0 as ->. 1: easy.
    unfold public. rewrite <- Heq. apply label_of_bexp_sound.
  - cbn in H|-*. destruct (label_of_bexp Pt2 be) eqn: Heq, lbe; cbn in *. 2-4: easy.
    eapply noninterferent_bexp in H0 as ->. 1: easy.
    unfold public. rewrite <- Heq. apply label_of_bexp_sound.
  - cbn in H|-*. destruct li; cbn in *.
    + destruct (label_of_aexp P i) eqn: Heq; cbn in H. 2: easy. (* contradiction in H *)
      split. 2: reflexivity. do 2 f_equal. 
      eapply noninterferent_aexp. 1: eassumption.
      unfold public. rewrite <- Heq. apply label_of_aexp_sound.
    + easy.
  - cbn in H. destruct (label_of_aexp P i) eqn: Heq; cbn in H. 2: easy.
    split. 2: reflexivity. do 2 f_equal.
    eapply noninterferent_aexp. 1: eassumption.
    unfold public. rewrite <- Heq. apply label_of_aexp_sound.
  - cbn in H|-*. destruct li; cbn in *.
    + destruct (label_of_aexp Pt2 i) eqn: Heq; cbn in H. 2: easy.
  split. 2: reflexivity. do 2 f_equal.
      eapply noninterferent_aexp. 1: eassumption.
      unfold public. rewrite <- Heq. apply label_of_aexp_sound.
    + easy.
  - cbn in H. destruct (label_of_aexp Pt2 i) eqn: Heq; cbn in H. 2: easy.
    split. 2: reflexivity. do 2 f_equal.
    eapply noninterferent_aexp. 1: eassumption.
    unfold public. rewrite <- Heq. apply label_of_aexp_sound.
  - eapply IHac in H19; [|eassumption..]. destruct H19 as (->&->). split; reflexivity.
Qed.

Lemma ideal_misspeculated_unwinding :
  forall ac P PA P' PA' pc st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds
    pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  well_labeled_acom ac P PA pc P' PA' ->
  pub_equiv P st1 st2 ->
  <[[ac, st1, ast1, true, pc, P, PA]]> -->i*_ds^^os1 <[[ct1, stt1, astt1, true, pct1, Pt1, PAt1]]> ->
  <[[ac, st2, ast2, true, pc, P, PA]]> -->i*_ds^^os2 <[[ct2, stt2, astt2, true, pct2, Pt2, PAt2]]> ->
  os1 = os2.
Proof.
  intros. revert H2. remember true as b in H1 at 1. remember true as bt in H1.
  revert st2 ast2 ct2 stt2 astt2 os2 Heqb Heqbt H H0.
  induction H1; intros; subst.
  - apply multi_ideal_obs_length in H2. now destruct os2.
  - pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H). subst. invert H3.
    + apply multi_ideal_obs_length in H1. apply ideal_eval_small_step_obs_length in H.
      symmetry in H7. apply app_eq_nil in H7 as (->&->). symmetry in H, H1.
      apply length_zero_iff_nil in H, H1. now subst.
    + assert (ds0 = ds1).
      { 
        apply app_eq_prefix in H4. apply prefix_eq_length; [|tauto].
        eapply ideal_eval_small_step_same_length; eassumption. 
      }
      subst. apply app_inv_head in H4. subst.
      pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5). subst.
      eapply ideal_misspeculated_unwinding_one_step in H5 as H5'; [|eassumption..]. destruct H5'. subst.
      eapply ideal_eval_noninterferent in H5 as H5'; [|now eauto..].
      destruct H5' as (_ & _ & -> & -> & -> & Hequiv' & Hequiv'').
      eapply ideal_eval_preserves_well_labeled in H0; [|now eauto]. f_equal.
      now eapply IHmulti_ideal; eauto.
Qed.

Lemma multi_ideal_no_spec_deterministic : forall c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 ds os1 os2
    pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 ->
  <[[c, st1, ast1, false, pc, P, PA]]> -->i*_ds^^os1 <[[ct1, stt1, astt1, false, pct1, Pt1, PAt1]]> ->
  <[[c, st2, ast2, false, pc, P, PA]]> -->i*_ds^^os2 <[[ct2, stt2, astt2, false, pct2, Pt2, PAt2]]> ->
  os1 = os2.
Proof.
  intros. apply multi_ideal_no_spec in H0 as Heq.
  destruct Heq as (n&->). apply multi_ideal_obs_length in H0 as Heq, H1 as Heq'.
  rewrite Heq' in Heq. clear Heq'. apply multi_ideal_multi_seq in H1, H0.
  apply prefix_eq_length; [now symmetry|]. eapply H; eassumption.
Qed.

Lemma multi_ideal_stuck_noninterference :
  forall ac P PA P' PA' st1 st2 ast1 ast2 b pc act1 act2 stt1 stt2 astt1 astt2 bt1 bt2 pct1 pct2 Pt1 Pt2 PAt1 PAt2
    act1' act2' stt1' stt2' astt1' astt2' bt1' bt2' pct1' pct2' Pt1' Pt2' PAt1' PAt2' ds os d1 d2 o1 o2,
  well_labeled_acom ac P PA pc P' PA' ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA ast1 ast2) -> 
  <[[ ac, st1, ast1, b, pc, P, PA ]]> -->i*_ds^^os <[[ act1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> ->
  <[[ act1, stt1, astt1, bt1, pct1, Pt1, PAt1 ]]> -->i_[d1]^^[o1] <[[ act1', stt1', astt1', bt1', pct1', Pt1', PAt1' ]]> ->
  <[[ ac, st2, ast2, b, pc, P, PA ]]> -->i*_ds^^os <[[ act2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> ->
  <[[ act2, stt2, astt2, bt2, pct2, Pt2, PAt2 ]]> -->i_[d2]^^[o2] <[[ act2', stt2', astt2', bt2', pct2', Pt2', PAt2' ]]> ->
  act1 = act2 /\ bt1 = bt2 /\ Pt1 = Pt2 /\ PAt1 = PAt2 /\
  pub_equiv Pt1 stt1 stt2 /\ (bt2 = false -> pub_equiv PAt1 astt1 astt2).
Proof.
  intros.
  revert st2 ast2 act2 stt2 astt2 bt2 pct2 Pt2 PAt2 act2' stt2' astt2' bt2' pct2' Pt2' PAt2' d2 o2 H4 H5 H H0 H1.
  induction H2; intros.
  - invert H4; [tauto|].
    eapply ideal_eval_small_step_same_length in H3 as Heq; [|apply H14].
    apply app_eq_nil in H2. now destruct H2; subst.
  - specialize (IHmulti_ideal H3). invert H4.
    { symmetry in H15. apply app_eq_nil in H15. destruct H15; subst.
      now eapply ideal_eval_small_step_same_length in H; [|apply H5]. }
    eapply ideal_eval_small_step_same_length in H as Heq; [|apply H16].
    apply prefix_eq_length in Heq; [subst|eapply app_eq_prefix, H7].
    apply ideal_eval_small_step_obs_length in H as Heq, H16 as Heq'.
    rewrite Heq' in Heq. apply prefix_eq_length in Heq; [subst|eapply app_eq_prefix, H8].
    apply app_inv_head in H7, H8. clear Heq'. subst.
    eapply ideal_eval_noninterferent in H16 as Heq; [|eassumption..].
    destruct Heq as (<-&<-&<-&<-&<-&?&?).
    eapply IHmulti_ideal; try eassumption.
    eapply ideal_eval_preserves_well_labeled; eassumption.
Qed.
  
  

Lemma multi_ideal_misspeculate_split : forall ds c st ast ct stt astt os pc pct P Pt PA PAt,
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ds^^os <[[ct, stt, astt, true, pct, Pt, PAt]]> ->
  exists n ds2 os1 o os2 c1 c2 st1 st2 ast1 ast2 pc1 pc2 P1 P2 PA1 PA2,
  ds = repeat DStep n ++ DForce :: ds2 /\
  os = os1 ++ o :: os2 /\
  <[[c, st, ast, false, pc, P, PA]]> -->i*_ repeat DStep n ^^os1 <[[c1, st1, ast1, false, pc1, P1, PA1]]> /\
  <[[c1, st1, ast1, false, pc1, P1, PA1]]> -->i_[DForce]^^[o] <[[c2, st2, ast2, true, pc2, P2, PA2]]> /\
  <[[c2, st2, ast2, true, pc2, P2, PA2]]> -->i*_ds2^^os2 <[[ct, stt, astt, true, pct, Pt, PAt]]>.
Proof.
  induction ds; intros; [now apply multi_ideal_spec_needs_force in H|].
  apply multi_ideal_factorize in H. do 14 destruct H. destruct H0, H1. subst.
  destruct x5.
  + apply ideal_eval_small_step_spec_needs_force in H1 as Heq. invert Heq.
    change (DForce :: ds) with ([]++[DForce]++ds). change (x6::x7) with ([]++ x6 :: x7).
    exists 0, ds. now eauto 20.
  + apply IHds in H2. destruct H2. do 17 destruct H. destruct H2, H3. subst.
    apply ideal_eval_small_step_no_spec in H1 as Heq. destruct Heq; [|discriminate]. invert H.
    eapply multi_ideal_trans in H1; [|eassumption]. eapply multi_ideal_combined_executions in H1; [|eassumption].
    rewrite !app_comm_cons. exists (1+x5), x12. now eauto 20.
Qed.

Lemma seq_same_obs_multi_ideal_misspeculate_split :
  forall ds c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 os1 os2 pc P PA pct1 pct2 Pt1 Pt2 PAt1 PAt2,
  seq_same_obs (erase c) st1 st2 ast1 ast2 -> 
  <[[ c, st1, ast1, false, pc, P, PA ]]> -->i*_ ds ^^ os1 <[[ ct1, stt1, astt1, true, pct1, Pt1, PAt1 ]]> ->
  <[[ c, st2, ast2, false, pc, P, PA ]]> -->i*_ ds ^^ os2 <[[ ct2, stt2, astt2, true, pct2, Pt2, PAt2 ]]> ->
  exists n ds' os o os1' os2' c' c'' st1' st2' st1'' st2'' ast1' ast2' ast1'' ast2'' pc' pc'' P' P'' PA' PA'',
  ds = repeat DStep n ++ DForce :: ds' /\
  os1 = os ++ o :: os1' /\
  os2 = os ++ o :: os2' /\
  <[[ c, st1, ast1, false, pc, P, PA]]> -->i*_ repeat DStep n ^^os <[[ c', st1', ast1', false, pc', P', PA']]> /\
  <[[ c', st1', ast1', false, pc', P', PA']]> -->i_[DForce]^^[o] <[[ c'', st1'', ast1'', true, pc'', P'', PA'']]> /\
  <[[ c'', st1'', ast1'', true, pc'', P'', PA'']]> -->i*_ds' ^^ os1' <[[ ct1, stt1, astt1, true, pct1, Pt1, PAt1]]> /\
  <[[ c, st2, ast2, false, pc, P, PA]]> -->i*_ repeat DStep n ^^os <[[ c', st2', ast2', false, pc', P', PA']]> /\
  <[[ c', st2', ast2', false, pc', P', PA']]> -->i_[DForce]^^[o] <[[ c'', st2'', ast2'', true, pc'', P'', PA'']]> /\
  <[[ c'', st2'', ast2'', true, pc'', P'', PA'']]> -->i*_ds' ^^ os2' <[[ ct2, stt2, astt2, true, pct2, Pt2, PAt2]]>.
Proof.
  induction ds; intros; [now apply multi_ideal_spec_needs_force in H0|].
  remember H as H'. clear HeqH'.
  eapply seq_same_obs_multi_ideal_factorize in H as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?).
  2, 3: eassumption. subst.
  destruct x9.
  - apply ideal_eval_small_step_spec_needs_force in H4 as Heq. invert Heq.
    change (DForce :: ds) with ([]++[DForce]++ds). change (x::x1) with ([]++x::x1). change (x0::x2) with ([]++x0::x2).
    exists 0, ds.
    eapply ideal_eval_small_step_force_obs in H7 as Heq. 3: exact H4.
    2: eapply multi_ideal_preserves_seq_same_obs; eassumption.
    invert Heq.
    exists [], x0, x1, x2. repeat eexists; try eassumption.
  - eapply IHds in H8 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). 3: exact H5.
    2: {
      eapply multi_ideal_preserves_seq_same_obs.
      - eassumption.
      - eapply multi_ideal_combined_executions. 1: eassumption.
        eapply multi_ideal_trans; [eassumption|constructor].
      - eapply multi_ideal_combined_executions. 1: eassumption.
        eapply multi_ideal_trans; [eassumption|constructor].
    }
    apply ideal_eval_small_step_no_spec in H4 as Heq1. destruct Heq1; [|discriminate]. invert H15.
    eapply multi_ideal_trans in H4, H7. 2, 3: eassumption.
    eapply multi_ideal_combined_executions in H4, H7; [|eassumption..].
    assert (x = x0) as <-.
    {
      eapply multi_ideal_no_spec_deterministic in H7. 2,3: eassumption. cbn in H7. now invert H7.
    }
    rewrite !app_comm_cons. exists  (1 + x9).
    repeat eexists; try eassumption.
Qed.

Theorem ideal_eval_relative_secure : forall ac c st st' ast ast' P PA P' PA',
  static_tracking c P PA public = (ac, P', PA') ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs c st st' ast ast' ->
  ideal_same_obs ac st st' ast ast' P PA.
Proof.
  unfold ideal_same_obs. intros. eapply multi_ideal_spec_bit_deterministic in H5 as Heq; [|eassumption]. subst.
  apply erase_static_tracking in H as H'. subst.
  apply static_tracking_well_labeled in H.
  destruct b1; [|eapply multi_ideal_no_spec_deterministic; eassumption].
  eapply seq_same_obs_multi_ideal_misspeculate_split in H6; [|eassumption..]. clear H5.
  destruct H6 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&->&->&->&?&?&?&?&?&?).
  do 2 f_equal.
  eapply multi_ideal_stuck_noninterference in H9 as Heq; try eassumption. 2: now intros.
  eapply multi_ideal_preserves_well_labeled in H5 as Hwl. 2: eassumption.
  eapply ideal_misspeculated_unwinding in H10; try eassumption.
  - eapply ideal_eval_preserves_well_labeled; eassumption.
  - destruct Heq as (_&_&_&_&Hequiv1%pub_equiv_sym&Hequiv2%pub_equiv_sym). 2: reflexivity.
    eapply ideal_eval_noninterferent in H6; try eassumption.
    + apply pub_equiv_sym, H6.
    + intros _. apply Hequiv2.
Qed.

Theorem fs_flex_vslh_relative_secure : forall P PA c st ast st' ast',
  unused "b" c ->
  st "b" = 0 ->
  st' "b" = 0 ->
  pub_equiv P st st' ->
  pub_equiv PA ast ast' ->
  nonempty_arrs ast ->
  nonempty_arrs ast' ->
  seq_same_obs c st st' ast ast' ->
  spec_same_obs (fs_flex_vslh P PA c) st st' ast ast'.
Proof.
  unfold spec_same_obs, fs_flex_vslh. intros.
  destruct (static_tracking c P PA public) as ((ac&P')&PA') eqn:Heq.
  eapply flex_slh_acom_bcc in H7; try tauto; [|unfold acom_unused; erewrite erase_static_tracking; eassumption].
  eapply flex_slh_acom_bcc in H8; try tauto; [|unfold acom_unused; erewrite erase_static_tracking; eassumption].
  destruct H7 as (st1''&ac1'&?&?&?&?), H8 as (st2''&ac2'&?&?&?&?).
  eapply ideal_eval_relative_secure; eassumption.
Qed.

