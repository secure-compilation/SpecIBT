(** * UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import SpecCT.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** * Relative security *)

(** We would like to also enforce security for arbitrary programs that do
    not follow the cryptographic constant time programming discipline
    (i.e. which do not satisfy [ct_well_typed]). The goal is to achieve a
    relative notion of security which intuitively ensures that the protected
    program does not leak more information speculatively than the original
    program leaks sequentially via the CT observations. One way to achieve this
    protection is by transforming the program using Ultimate Speculative Load
    Hardening (USLH), instead of the selective variant from the previous chapter. *)

(** We formalize this as a relative security property that doesn't label data at
    all as public or secret. *)

(** We need to define [seq_same_obs] below wrt a small-step semantics, so that
    this hypothesis also gives us something for sequentially infinite
    executions, and also for executions that sequentially get stuck because of
    out of bound accesses. *)

(** Sequential small-step semantics *)

Reserved Notation
  "'<((' c , st , ast '))>' '-->^' os '<((' ct , stt , astt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive seq_eval_small_step :
    com -> state -> astate ->
    com -> state -> astate -> obs -> Prop :=
  | SSM_Asgn  : forall st ast e n x,
      aeval st e = n ->
      <((x := e, st, ast))> -->^[] <((skip, x !-> n; st, ast))>
  | SSM_Seq : forall c1 st ast os c1t stt astt c2,
      <((c1, st, ast))>  -->^os <((c1t, stt, astt))>  ->
      <(((c1;c2), st, ast))>  -->^os <(((c1t;c2), stt, astt))>
  | SSM_Seq_Skip : forall st ast c2,
      <(((skip;c2), st, ast))>  -->^[] <((c2, st, ast))>
  | SSM_If : forall be ct cf st ast,
      <((if be then ct else cf end, st, ast))> -->^[OBranch (beval st be)]
      <((match beval st be with
        | true => ct
        | false => cf end, st, ast))>
  | SSM_While : forall be c st ast,
      <((while be do c end, st, ast))> -->^[]
      <((if be then c; while be do c end else skip end, st, ast))>
  | SSM_ARead : forall x a ie st ast i,
      aeval st ie = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast))> -->^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast))>
  | SSM_Write : forall a ie e st ast i n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast))> -->^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast))>

  where "<(( c , st , ast ))> -->^ os  <(( ct ,  stt , astt ))>" :=
    (seq_eval_small_step c st ast ct stt astt os).

Reserved Notation
   "'<((' c , st , ast '))>' '-->*^' os '<((' ct , stt , astt '))>'"
   (at level 40, c custom com at level 99, ct custom com at level 99,
    st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_seq (c:com) (st:state) (ast:astate) :
    com -> state -> astate -> obs -> Prop :=
  | multi_seq_refl : <((c, st, ast))> -->*^[] <((c, st, ast))>
  | multi_seq_trans (c':com) (st':state) (ast':astate)
                (c'':com) (st'':state) (ast'':astate)
                (os1 os2 : obs) :
      <((c, st, ast))> -->^os1 <((c', st', ast'))> ->
      <((c', st', ast'))> -->*^os2 <((c'', st'', ast''))> ->
      <((c, st, ast))> -->*^(os1++os2) <((c'', st'', ast''))>

  where "<(( c , st , ast ))> -->*^ os <(( ct ,  stt , astt ))>" :=
    (multi_seq c st ast ct stt astt os).

Lemma multi_seq_combined_executions : forall c st ast cm stm astm osm ct stt astt ost,
  <((c, st, ast))> -->*^osm <((cm, stm, astm))> ->
  <((cm, stm, astm))> -->*^ost <((ct, stt, astt))> ->
  <((c, st, ast))> -->*^(osm++ost) <((ct, stt, astt))>.
Proof.
  intros c st ast cm stm astm osm ct stt astt ost Hev1 Hev2.
  induction Hev1.
  - rewrite app_nil_l. apply Hev2.
  - rewrite <- app_assoc. eapply multi_seq_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma seq_small_step_obs_type : forall c st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2,
  <((c, st1, ast1))> -->^os1 <((ct1, stt1, astt1))> ->
  <((c, st2, ast2))> -->^os2 <((ct2, stt2, astt2))> ->
  match os2 with
  | [] => os1 = []
  | OBranch _ :: os => exists b, os1 = OBranch b :: os
  | OARead _ _ :: os => exists a i, os1 = OARead a i :: os
  | OAWrite _ _ :: os => exists a i, os1 = OAWrite a i :: os
  end.
Proof.
  induction c; intros st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2 H1 H2;
  inversion H1; inversion H2; subst; try eauto.
  + eapply IHc1; eauto.
  + inversion H9.
  + inversion H17.
Qed.

Corollary seq_small_step_obs_length : forall c st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2,
  <((c, st1, ast1))> -->^os1 <((ct1, stt1, astt1))> ->
  <((c, st2, ast2))> -->^os2 <((ct2, stt2, astt2))> ->
  length os1 = length os2.
Proof.
  intros. eapply seq_small_step_obs_type in H; [|now apply H0].
  destruct os1; subst; [now auto|].
  destruct o.
  2, 3 : now (do 2 destruct H); subst.
  now destruct H; subst.
Qed.

Lemma seq_big_to_small_step : forall c st ast stt astt os,
  <(st, ast)> =[ c ]=> <(stt, astt, os)> ->
  <((c, st, ast))> -->*^os <((skip, stt, astt))>.
Proof.
  intros c st ast stt astt os Hev. induction Hev;
  try (now rewrite <- app_nil_r; econstructor; econstructor; eauto).
  - remember Skip as c'. clear Hev1. clear Hev2.
    induction IHHev1; subst.
    + eapply multi_seq_trans; eauto.
      econstructor.
    + rewrite <- app_assoc.
      eapply multi_seq_trans.
      * econstructor. now apply H.
      * apply IHIHHev1; eauto.
  - (* If_True *)
    econstructor.
    + rewrite <- H. eapply SSM_If.
    + rewrite H; eauto.
  - (* If_False *)
    econstructor.
    + rewrite <- H. eapply SSM_If.
    + rewrite H; eauto.
  - (* While *)
    rewrite <- app_nil_l. econstructor; [econstructor |]; eauto.
Qed.

(* HIDE: CH: Why are we going to cteval? Is that used at all in this file? *)
Lemma seq_eval_one_step : forall c st ast stt astt os c1 os1 st1 ast1,
  <((c, st, ast))> -->^os1 <((c1, st1, ast1))> ->
  <(st1, ast1)> =[ c1 ]=> <(stt, astt, os)> ->
  <(st, ast)> =[ c ]=> <(stt, astt, os1++os)>.
Proof.
  intros c st ast stt astt os c1 os1 st1 ast1 H1 H.
  generalize dependent os. generalize dependent astt.
  generalize dependent stt.
  induction H1; intros.
  - inversion H0. subst. constructor. reflexivity.
  - inversion H. subst. rewrite app_assoc. econstructor; eauto.
  - econstructor. { constructor. } { assumption. }
  - destruct (beval st be) eqn:Heq; now constructor.
  - now constructor.
  - inversion H1; subst. now constructor.
  - inversion H2; subst. now constructor.
Qed.

Lemma seq_small_to_big_step : forall c st ast stt astt os,
  <((c, st, ast))> -->*^os <((skip, stt, astt))> ->
  <(st, ast)> =[ c ]=> <(stt, astt, os)>.
Proof.
  intros c st ast stt astt os H. remember Skip as c1.
  induction H; subst.
  - constructor.
  - eapply seq_eval_one_step; eauto.
Qed.

(** * Definition of Relative Secure *)

Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2 c1 c2,
    <((c, st1, ast1))> -->*^os1 <((c1, stt1, astt1))> ->
    <((c, st2, ast2))> -->*^os2 <((c2, stt2, astt2))> ->
    (prefix os1 os2) \/ (prefix os2 os1).

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure (trans : com -> com)
    (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

(** * Ultimate Speculative Load Hardening *)

Fixpoint ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> => <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

(** The masking USLH does for indices requires that our arrays are nonempty. *)

Definition nonempty_arrs (ast : astate) :Prop :=
  forall a, 0 < length (ast a).

(** * Ideal big-step evaluation *)

(** As in SpecCT, we define an ideal big-step evaluation relation, which
    abstractly captures the masking done by USLH. *)

Reserved Notation
  "'|-i' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
  (at level 40, c custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      |-i <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      |-i <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      |-i <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      |-i <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      |-i <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, b, ds)> =[ match negb b && beval st be  with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (negb b && beval st be)]++os1)>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      |-i <(st, ast, true, ds)> =[ match negb b && beval st be  with
                                 | true => c2 (* <-- branches swapped *)
                                 | false => c1 end ]=> <(st', ast', b', os1)> ->
      |-i <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', [OBranch (negb b && beval st be)]++os1)>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      |-i <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      |-i <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast (b :bool) x a ie i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_Write : forall st ast (b :bool) a ie i e n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      |-i <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (ast a) n; ast, b, [OAWrite a i])>

  where "|-i <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval c st ast b ds stt astt bb os).

Definition ideal_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

(** * Ideal small-step evaluation *)

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall st ast b c2,
      <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))>
      -->i_[DStep]^^[OBranch (negb b && beval st be)]
      <((match negb b && beval st be with
        | true => ct
        | false => cf end, st, ast, b))>
  | ISM_If_F : forall be ct cf st ast b,
      <((if be then ct else cf end, st, ast, b))>
      -->i_[DForce]^^[OBranch (negb b && beval st be)]
      <((match negb b && beval st be with
        | true => cf
        | false => ct end, st, ast, true))>
  | ISM_While : forall be c st ast b,
      <((while be do c end, st, ast, b))> -->i_[]^^[]
      <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall x a ie st ast (b :bool) i,
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
      <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | ISM_Write : forall a ie e st ast (b :bool) i n,
      aeval st e = n ->
      (if b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
      <((skip, st, a !-> upd i (ast a) n; ast, b))>

  where "<(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step c st ast b ct stt astt bt ds os).

Reserved Notation
  "'<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      <((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      <((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      <((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

  where "<(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal c st ast b ct stt astt bt ds os).

Lemma multi_ideal_combined_executions :
  forall c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    <((c, st, ast, b))> -->i*_ds^^osm <((cm, stm, astm, bm))> ->
    <((cm, stm, astm, bm))> -->i*_dsm^^ost <((ct, stt, astt, bt))> ->
    <((c, st, ast, b))> -->i*_(ds++dsm)^^(osm++ost) <((ct, stt, astt, bt))>.
Proof.
  intros c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

(* Should be similar to seq_big_to_small_step *)
Lemma ideal_big_to_small_step : forall c st ast b stt astt bt ds os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  <((c, st, ast, b))> -->i*_ds^^os <((skip, stt, astt, bt))>.
Proof.
  intros c st ast b stt astt bt ds os Hbig. induction Hbig.
  - (* Skip *) apply multi_ideal_refl.
  - (* Asgn*)
    replace ([] :dirs) with ([]++[] :dirs) by (apply app_nil_r).
    replace ([] :obs) with ([]++[] :obs) by (apply app_nil_r).
    eapply multi_ideal_trans.
    + eapply ISM_Asgn. eapply H.
    + apply multi_ideal_refl.
  - (* Seq *)
    remember Skip as c'. clear Hbig1. clear Hbig2.
    induction IHHbig1; subst.
    + eapply multi_ideal_trans; eauto.
      econstructor.
    + rewrite <- !app_assoc.
      eapply multi_ideal_trans.
      * econstructor. now apply H.
      * apply IHIHHbig1; eauto.
  - (* IF *)
    replace (DStep:: ds) with ([DStep] ++ ds) by reflexivity.
    eapply multi_ideal_trans.
    + apply ISM_If.
    + apply IHHbig.
  - (* IF_F *)
    replace (DForce:: ds) with ([DForce] ++ ds) by reflexivity.
    eapply multi_ideal_trans.
    + apply ISM_If_F.
    + apply IHHbig.
  - (* While *)
    replace (ds) with ([]++ds) by reflexivity.
    replace (os) with ([]++os) by reflexivity.
    eapply multi_ideal_trans.
    + eapply ISM_While.
    + apply IHHbig.
  - (* ARead *)
    replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
    replace ([OARead a i]) with ([OARead a i]++[]) by (apply app_nil_r).
    eapply multi_ideal_trans.
    + eapply ISM_ARead; auto.
    + apply multi_ideal_refl.
  - (* AWrite *)
    replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
    replace ([OAWrite a i]) with ([OAWrite a i]++[]) by (apply app_nil_r).
    eapply multi_ideal_trans.
    + eapply ISM_Write; auto.
    + rewrite H. apply multi_ideal_refl.
Qed.


Lemma ideal_eval_one_step : forall c1 c2 st stm stt ast astm astt b bm bt ds1 ds2 os1 os2,
  <((c1, st, ast, b))> -->i_ds1^^os1 <((c2, stm, astm, bm))> ->
  |-i <(stm, astm, bm, ds2)> =[ c2 ]=> <(stt, astt, bt, os2)> ->
  |-i <(st, ast, b, ds1++ds2)> =[ c1 ]=> <(stt, astt, bt, os1++os2)>.
Proof.
  intros c1 c2 st stm stt ast astm astt b bm bt ds1 ds2 os1 os2 Hsmall.
  generalize dependent os2; generalize dependent ds2;
  generalize dependent bt; generalize dependent astt;
  generalize dependent stt.
  induction Hsmall; intros stt' astt' bt' ds2 os2 Hbig.
  - (* ISM_Asgn *)
    inversion Hbig; subst; simpl in *. apply Ideal_Asgn; auto.
  - (* ISM_Seq *)
    inversion Hbig; subst; simpl in *. apply IHHsmall in H1.
    replace (ds ++ ds1 ++ ds0) with ((ds ++ ds1) ++ ds0) by (rewrite app_assoc; auto).
    replace (os ++ os1 ++ os0) with ((os ++ os1) ++ os0) by (rewrite app_assoc; auto).
    eapply Ideal_Seq; eauto.
  - (* ISM_Seq_Skip *)
    eapply Ideal_Seq; eauto. apply Ideal_Skip.
  - (* ISM_If *)
    apply Ideal_If; auto.
  - (* ISM_If_F *)
    apply Ideal_If_F; auto.
  - (* ISM_While *)
    do 2 rewrite app_nil_l. apply Ideal_While. apply Hbig.
  - (* ISM_ARead *)
    inversion Hbig; subst; simpl in *. apply Ideal_ARead; auto.
  - (* ISM_Write *)
  inversion Hbig; subst; simpl in *. apply Ideal_Write; auto.
Qed.

Lemma ideal_eval_multi_steps : forall c1 c2 st stm stt ast astm astt b bm bt ds1 ds2 os1 os2,
  <((c1, st, ast, b))> -->i*_ds1^^os1 <((c2, stm, astm, bm))> ->
  |-i <(stm, astm, bm, ds2)> =[ c2 ]=> <(stt, astt, bt, os2)> ->
  |-i <(st, ast, b, ds1++ds2)> =[ c1 ]=> <(stt, astt, bt, os1++os2)>.
Proof.
  intros. generalize dependent os2. generalize dependent ds2. induction H.
  + intros. apply H0.
  + intros. rewrite <- !app_assoc.
    eapply ideal_eval_one_step; eauto.
Qed.

Lemma ideal_small_to_big_step : forall c st ast b stt astt bt ds os,
  <((c, st, ast, b))> -->i*_ds^^os <((skip, stt, astt, bt))> ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)>.
Proof.
  intros c st ast b stt astt bt ds os Hsmall.
  remember <{{skip}}> as ct eqn:Eqct. induction Hsmall; subst.
  - apply Ideal_Skip.
  - assert (L: <{{ skip }}> = <{{ skip }}>) by reflexivity.
    apply IHHsmall in L. eapply ideal_eval_one_step; eauto.
Qed.

(** * Relative Security of Ultimate Speculative Load Hardening *)

(* HIDE *)
(* Some intuition about Lemma 1 from the USLH paper (unwinding for ideal misspeculated executions),
   but now we plan to prove it directly, like determinism (see below) *)

Fixpoint observations (c:com) (ds:dirs) : option (obs * dirs) :=
  match c with
  | <{{skip}}> => Some ([],ds)
  | <{{x := e}}> => Some ([],ds)
  | <{{c1; c2}}> =>
      match observations c1 ds with
      | Some (os',ds') =>
          match observations c2 ds' with
          | Some (os'',ds'') => Some (os''++os', ds'')
          | None => None
          end
      | None => None
      end
  | <{{if be then c1 else c2 end}}> =>
      match ds with
      | DStep :: ds' =>
          match observations c2 ds' with
          | Some (os,ds'') => Some (os++[OBranch false],ds'')
          | None => None
          end
      | DForce :: ds' =>
          match observations c1 ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{while be do c end}}> =>
      match ds with
      | DStep :: ds' => Some ([OBranch false],ds')
      | DForce :: ds' =>
          (* `c` below should actually be `while be do c end`,
              but then termination no longer obvious  *)
          match observations c ds' with
          | Some (os,ds'') => Some (os++[OBranch true],ds'')
          | None => None
          end
      | _ => None
      end
  | <{{x <- a[[i]]}}> => Some ([OARead a 0],ds)
  | <{{a[i] <- e}}> => Some ([OAWrite a 0],ds)
  end.

Lemma observations_fixed : forall c st ast ds stt astt os,
  unused "b" c ->
  st "b" = 1 ->
  |-i <(st, ast, true, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  Some (os,[]) = observations c ds.
Proof.
Admitted.

Lemma ideal_misspeculated_unwinding_follows : forall c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2,
  unused "b" c ->
  st1 "b" = 1 ->
  st2 "b" = 1 ->
  |-i <(st1, ast1, true, ds)> =[ c ]=> <(stt1, astt1, true, os1)> ->
  |-i <(st2, ast2, true, ds)> =[ c ]=> <(stt2, astt2, true, os2)> ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 ds stt1 stt2 astt1 astt2 os1 os2 Hunused Hb1 Hb2 H1 H2.
  apply observations_fixed in H1; try auto.
  apply observations_fixed in H2; try auto. congruence.
Qed.
(* /HIDE *)

(** As in SpecCT and Spectre Declassified, an important step in the proof is
    relating the speculative semantics of the hardened program with the ideal
    semantics, by means of a backwards compiler correctness (BCC) result. *)

Lemma ideal_unused_overwrite : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
  intros. induction H0.
  + constructor.
  + subst. destruct H as [H H'].
    rewrite t_update_permute; [|assumption].
    constructor. now rewrite aeval_unused_update.
  + destruct H. now econstructor; eauto.
  + destruct H as [Hb [Hc1 Hc2] ].
    erewrite <- beval_unused_update; [|eassumption]. constructor.
    rewrite beval_unused_update; [|assumption].
    apply IHideal_eval. now destruct (negb b && beval st be).
  + destruct H as [Hb [Hc1 Hc2] ].
    erewrite <- beval_unused_update; [|eassumption]. constructor.
    rewrite beval_unused_update; [|assumption].
    apply IHideal_eval. now destruct (negb b && beval st be).
  + constructor. apply IHideal_eval. destruct H. now repeat constructor.
  + subst. destruct H.
    rewrite t_update_permute; [|assumption].
    now constructor; [rewrite aeval_unused_update|assumption].
  + subst. destruct H. now constructor; try rewrite aeval_unused_update.
Qed.

Lemma ideal_unused_update : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)> ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X !-> st X; st', ast', b', os)>.
Proof.
  intros. rewrite <- (t_update_same _ st X) at 1.
  eapply ideal_unused_overwrite with (X:=X) (n:=(st X)) in H0; [|assumption].
  now rewrite !t_update_shadow in H0.
Qed.

Lemma ideal_unused_update_rev : forall st ast b ds c st' ast' b' os X n,
  unused X c ->
  |-i <(st, ast, b, ds)> =[ c ]=> <(X!-> st X; st', ast', b', os)> ->
  |-i <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
  intros.
  eapply ideal_unused_overwrite with (n:=n) in H0; [|eassumption].
  now rewrite t_update_shadow in H0.
Qed.

Lemma upd_length : forall l i a,
  length (upd i l a) = length l.
Proof.
  induction l; destruct i; auto.
  intros. simpl. now f_equal.
Qed.

Lemma spec_eval_preserves_nonempty_arrs : forall c st ast b ds st' ast' b' os,
  nonempty_arrs ast ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  nonempty_arrs ast'.
Proof.
  unfold nonempty_arrs.
  intros. generalize dependent a. induction H0; eauto; subst.
  2:clear H2 a. 1:rename a into a'.
  all: intros; destruct (String.eqb a a') eqn:Heq.
  2, 4: now apply String.eqb_neq in Heq; rewrite t_update_neq.
  all: now apply String.eqb_eq in Heq; subst; rewrite t_update_eq, upd_length.
Qed.

Lemma flag_zero_check_spec_bit : forall (st :state) (X :string) (b b' :bool),
  st X = (if b then 1 else 0) ->
  (st X =? 0)%nat = b' ->
  b = negb b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.

Lemma flag_one_check_spec_bit : forall (st :state) (X :string) (b b' :bool),
  st X = (if b then 1 else 0) ->
  (st X =? 1)%nat = b' ->
  b = b'.
Proof.
 intros st X b b' Hflag Heqb. destruct b; destruct b'; try reflexivity;
 rewrite Hflag in Heqb; simpl in Heqb; discriminate.
Qed.

Definition ultimate_slh_flag_prop (c :com) (ds :dirs) :Prop :=
  forall st ast (b:bool) st' ast' (b':bool) os,
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
  st' "b" = (if b' then 1 else 0).

Lemma ultimate_slh_flag : forall c ds,
  ultimate_slh_flag_prop c ds.
Proof.
  apply prog_size_ind. unfold ultimate_slh_flag_prop.
  destruct c; simpl; intros.
  + now inversion H2; subst.
  + inversion H2; subst. now rewrite t_update_neq.
  + inversion H2; subst. eapply H; [..|apply H14].
    { prog_size_auto. } { now destruct H0. }
    eapply H; [..|apply H1|apply H5].
    { prog_size_auto. } now destruct H0.
  + inversion H2; subst.
    - simpl in H14. destruct b.
      * rewrite H1 in H14. simpl in H14.
        inversion H14; subst.
        eapply H; [..|apply H15].
        { prog_size_auto. } { now destruct H0. }
        inversion H5; subst. rewrite t_update_eq.
        simpl. now rewrite H1.
      * rewrite H1 in H14. simpl in H14.
        destruct (beval st be) eqn:Heq; inversion H14; subst; (eapply H; [..|apply H15]; [prog_size_auto|now destruct H0|]).
        all: inversion H5; subst. all:rewrite t_update_eq; simpl.
        all:now rewrite H1, Heq.
    - simpl in H14. destruct b.
      * rewrite H1 in H14. simpl in H14.
        inversion H14; subst.
        eapply H; [..|apply H15].
        { prog_size_auto. } { now destruct H0. }
        inversion H5; subst. rewrite t_update_eq.
        simpl. now rewrite H1.
      * rewrite H1 in H14. simpl in H14.
        destruct (beval st be) eqn:Heq; inversion H14; subst; (eapply H; [..|apply H15]; [prog_size_auto|now destruct H0|]).
        all: inversion H5; subst. all:rewrite t_update_eq; simpl.
        all:now rewrite H1, Heq.
  + inversion H2; subst; clear H2.
    inversion H5; subst; clear H5.
    inversion H13; subst; clear H13.
    - destruct b.
      * simpl in H15. rewrite H1 in H15.
        simpl in H15. inversion H15; subst; clear H15.
        inversion H14; subst; clear H14.
        rewrite t_update_eq. simpl. now rewrite H1.
      * simpl in H15. rewrite H1 in H15. destruct (beval st be) eqn:Heq.
        ++ simpl in H15. inversion H15; subst; clear H15.
           inversion H4; subst; clear H4.
           inversion H5; subst; clear H5.
           assert (Hwhile : <( st'1, ast'1, b'1, ds0++ds2 )> =[ ultimate_slh <{{ while be do c end }}> ]=> <( st', ast', b', os3++os2 )>).
           { simpl. inversion H14; subst; clear H14. inversion H13; subst; clear H13. econstructor.
             + econstructor. apply H12.
             + now constructor. }
           eapply H; [..|apply Hwhile]. { prog_size_auto. } { now destruct H0. }
           eapply H; [..|apply H16]. { prog_size_auto. } { now destruct H0. }
           rewrite t_update_eq. simpl. now rewrite H1, Heq.
        ++ simpl in H15. inversion H15; subst; clear H15.
           inversion H14; subst; clear H14. rewrite t_update_eq. simpl. now rewrite H1, Heq.
    - assert (b'0 = true) by (eapply speculation_bit_monotonic; eauto); subst.
      assert (b' = true) by (eapply speculation_bit_monotonic; eauto); subst.
      simpl in H15. destruct b.
      * rewrite H1 in H15. simpl in H15. inversion H15; subst; clear H15.
        inversion H4; subst; clear H4.
        inversion H5; subst; clear H5.
        assert (b' = true) by (eapply speculation_bit_monotonic; eauto); subst.
        assert (Hwhile : <( st'1, ast'1, true, ds0++ds2 )> =[ ultimate_slh <{{ while be do c end }}> ]=> <( st', ast', true, os3++os2 )>).
        { simpl. inversion H14; subst; clear H14. inversion H13; subst; clear H13. econstructor.
          + econstructor. apply H12.
          + now constructor. }
        erewrite H; [..|apply Hwhile]. { reflexivity. } { prog_size_auto. } { now destruct H0. }
        eapply H; [..|apply H16]. { prog_size_auto. } { now destruct H0. }
        rewrite t_update_eq. simpl. now rewrite H1.
      * simpl in H15. rewrite H1 in H15. destruct (beval st be) eqn:Heq.
        ++ simpl in H15. inversion H15; subst; clear H15.
           inversion H14; subst; clear H14. rewrite t_update_eq. simpl. now rewrite H1, Heq.
        ++ simpl in H15. inversion H15; subst; clear H15.
           inversion H4; subst; clear H4.
           inversion H5; subst; clear H5.
           assert (b' = true) by (eapply speculation_bit_monotonic; eauto); subst.
           assert (Hwhile : <( st'1, ast'1, true, ds0++ds2 )> =[ ultimate_slh <{{ while be do c end }}> ]=> <( st', ast', true, os3++os2 )>).
           { simpl. inversion H14; subst; clear H14. inversion H13; subst; clear H13. econstructor.
             + econstructor. apply H12.
             + now constructor. }
           erewrite H; [..|apply Hwhile]. { reflexivity. } { prog_size_auto. } { now destruct H0. }
           eapply H; [..|apply H16]. { prog_size_auto. } { now destruct H0. }
           rewrite t_update_eq. simpl. now rewrite H1, Heq.
  + inversion H2; subst; now rewrite t_update_neq.
  + now inversion H2; subst.
Qed.

Definition ultimate_slh_bcc_prop (c: com) (ds :dirs) :Prop :=
  forall st ast (b: bool) st' ast' b' os,
    nonempty_arrs ast ->
    unused "b" c ->
    st "b" = (if b then 1 else 0) ->
    <(st, ast, b, ds)> =[ ultimate_slh c ]=> <(st', ast', b', os)> ->
    |-i <(st, ast, b, ds)> =[ c ]=> <("b" !-> st "b"; st', ast', b', os)>.

Lemma ultimate_slh_bcc : forall c ds,
  ultimate_slh_bcc_prop c ds.
Proof.
  apply prog_size_ind. unfold ultimate_slh_bcc_prop.
  intros c ds IH st ast b st' ast' b' os Hast Hunused Hstb Heval.
  destruct c; simpl in *; inversion Heval; subst; clear Heval.
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
    + apply ultimate_slh_flag in H1 as Hstb'0; try tauto.
      apply IH in H10; try tauto.
      * eapply ideal_unused_update_rev; try tauto.
      * prog_size_auto.
      * eapply spec_eval_preserves_nonempty_arrs in H1; auto.
  (* IF *)
  - (* non-speculative *)
    simpl in *. destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
    + (* true *)
      destruct (beval st be) eqn:Eqbe; simpl in H10;
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *;
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
      * replace (OBranch true) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe; rewrite Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
        apply Ideal_If. rewrite <- app_nil_l. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto. prog_size_auto.
      * replace (OBranch false) with (OBranch (negb b'0 && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
        apply Ideal_If. rewrite <- app_nil_l. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto. prog_size_auto.
    + (* false *)
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *.
      rewrite Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
      replace (OBranch false) with (OBranch (negb b'0 && beval st be))
        by (rewrite Hbit; reflexivity).
      apply Ideal_If. rewrite <- app_nil_l. subst; simpl.
      apply IH in H11; try tauto. prog_size_auto.
  - (* speculative *)
    simpl in *. destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
    + (* true *)
      destruct (beval st be) eqn:Eqbe; simpl in H10;
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *;
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
      * replace (OBranch true) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11.
        apply Ideal_If_F. rewrite <- app_nil_l. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto.
        { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
        { prog_size_auto. }
      * replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Eqbe, Hbit; reflexivity).
        rewrite Eqbe, Eqstb in H11; simpl in H11.
        apply Ideal_If_F. rewrite <- app_nil_l. rewrite Eqbe; subst; simpl.
        apply IH in H11; try tauto.
        { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
        { prog_size_auto. }
    + (* false *)
      inversion H10; inversion H1; subst; clear H10; clear H1; simpl in *.
      rewrite Eqstb in H11; simpl in H11.
      eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
      replace (OBranch false) with (OBranch (negb b && beval st be))
        by (rewrite Hbit; reflexivity).
      apply Ideal_If_F. rewrite <- app_nil_l. subst; simpl.
      apply IH in H11; try tauto.
      { rewrite t_update_eq in H11. apply ideal_unused_update in H11; try tauto. }
      { prog_size_auto. }
  - (* While *)
    eapply Ideal_While.
    inversion H1; subst; clear H1.
    inversion H11; subst; clear H11; simpl in *.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl. do 2 rewrite app_nil_r.
      destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
      * destruct (beval st be) eqn:Eqbe;
        inversion H12; subst; clear H12.
        { assert(Hwhile: <(st'1, ast'1, b'1, ds2)>
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (rewrite app_nil_r; reflexivity).
            replace os2 with (os2 ++ [])%list by (apply app_nil_r).
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch true) with (OBranch (negb b && beval st be))
            by (rewrite Eqbe, Hbit; reflexivity).
          apply Ideal_If. rewrite Eqbe; subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite <- app_nil_r. rewrite Eqbe, Eqstb in H11; simpl in H11.
            rewrite t_update_same in H11. apply IH in H11; try tauto.
            + rewrite app_nil_r. auto.
            + prog_size_auto.
          - apply IH in Hwhile; try tauto.
            + eapply ideal_unused_update_rev; eauto.
            + prog_size_auto.
            + eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            + auto.
            + inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqbe, Eqstb in H11; simpl in H11. rewrite t_update_same in H11.
              apply ultimate_slh_flag in H11; try tauto. }
        { eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b'0 && beval st'0 be))
            by (rewrite Hbit, Eqbe; reflexivity).
          apply Ideal_If. rewrite Eqbe; subst; simpl.
          inversion H10; subst; clear H10; simpl in *. rewrite Eqbe, Eqstb; simpl.
          rewrite t_update_shadow. rewrite t_update_same. apply Ideal_Skip. }
      * eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
        replace (OBranch false) with (OBranch (negb b && beval st be))
          by (rewrite Hbit; reflexivity).
        apply Ideal_If. subst; simpl.
        inversion H12; subst; clear H12.
        inversion H10; subst; clear H10; simpl in *.
        rewrite Eqstb; simpl. rewrite t_update_shadow. rewrite t_update_same.
        apply Ideal_Skip.
    + (* non-speculative *)
      assert(Lnil: os2 = [] /\ ds2 = []).
      { inversion H10; subst; eauto. }
      destruct Lnil; subst; simpl. do 2 rewrite app_nil_r.
      destruct (st "b" =? 0)%nat eqn:Eqstb; simpl in *.
      * destruct (beval st be) eqn:Eqbe;
        inversion H12; subst; clear H12.
        { eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch true) with (OBranch (negb b && beval st'0 be))
            by (rewrite Hbit, Eqbe; reflexivity).
          apply Ideal_If_F. rewrite Eqbe; subst; simpl.
          inversion H10; subst; clear H10; simpl in *.
          rewrite Eqstb; simpl. rewrite t_update_shadow. rewrite t_update_same.
          apply Ideal_Skip. }
        { assert(Hwhile: <(st'1, ast'1, b'1, ds2)>
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (apply app_nil_r).
            replace os2 with (os2++[])%list by (apply app_nil_r).
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b && beval st be))
            by (rewrite Eqbe, Hbit; reflexivity).
          apply Ideal_If_F. rewrite Eqbe; subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite Eqbe, Eqstb in H11; simpl in H11.
            apply IH in H11; try tauto.
            + eapply ideal_unused_update in H11; try tauto.
            + prog_size_auto.
          - apply IH in Hwhile; try tauto.
            + eapply ideal_unused_update_rev; eauto.
            + prog_size_auto.
            + eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            + auto.
            + inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqbe, Eqstb in H11; simpl in H11.
              apply ultimate_slh_flag in H11; try tauto. }
      * inversion H12; subst; clear H12.
        assert(Hwhile: <(st'1, ast'1, b'1, ds2)>
              =[ ultimate_slh <{{while be do c end}}> ]=> <(st', ast', b', os2)> ).
          { simpl. replace ds2 with (ds2 ++ [])%list by (apply app_nil_r).
            replace os2 with (os2++[])%list by (apply app_nil_r).
            eapply Spec_Seq; eassumption. }
          clear H11; clear H10.
          eapply flag_zero_check_spec_bit in Hstb as Hbit; eauto; simpl in Hbit.
          replace (OBranch false) with (OBranch (negb b && beval st be))
            by (rewrite Hbit; reflexivity).
          apply Ideal_If_F. subst; simpl.
          apply (Ideal_Seq _ _ _ _ _ ("b" !-> st "b"; st'1) ast'1 b'1 _ _ _ os1).
          { inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
            rewrite Eqstb in H11; simpl in H11.
            apply IH in H11; try tauto.
            - rewrite t_update_eq in H11.
              eapply ideal_unused_update in H11; try tauto.
            -  prog_size_auto. }
          { apply IH in Hwhile; try tauto.
            - eapply ideal_unused_update_rev; eauto.
            - prog_size_auto.
            - eapply spec_eval_preserves_nonempty_arrs in H1; auto.
            - auto.
            - inversion H1; subst; clear H1; inversion H2; subst; clear H2; simpl in *.
              rewrite Eqstb in H11; simpl in H11.
              apply ultimate_slh_flag in H11; try tauto. }
  - (* ARead *)
    simpl in H11. destruct (st "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
    + rewrite t_update_permute; [| tauto]. rewrite t_update_same.
      apply Ideal_ARead; auto. rewrite Hbit. reflexivity.
  - (* ARead; contradiction *) simpl in H11. rewrite Hstb in H11; simpl in H11.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H11.
    exfalso; auto.
  - (* AWrite *)
    simpl in H12. destruct (st' "b" =? 1)%nat eqn:Eqstb;
    eapply flag_one_check_spec_bit in Hstb as Hbit; eauto; simpl in *;
    rewrite Eqstb in *.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
    + rewrite t_update_same. apply Ideal_Write; auto.
      rewrite Hbit. reflexivity.
  - (* AWrite; contradiction *) simpl in H12. rewrite Hstb in H12; simpl in H12.
    specialize (Hast a). apply lt_neq in Hast. apply le_0_r in H12.
    exfalso; auto.
Qed.

(** * More prefix lemmas *)

Lemma prefix_eq_length : forall {X:Type} (ds1 ds2 : list X),
  length ds1 = length ds2 ->
  prefix ds1 ds2 \/ prefix ds2 ds1 ->
  ds1 = ds2.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 Hlen Hpre; simpl in *.
  - symmetry in Hlen. apply length_zero_iff_nil in Hlen. auto.
  - destruct ds2 as [| d2 ds2'] eqn:Eqds2; simpl in *.
    + discriminate Hlen.
    + destruct Hpre as [Hpre | Hpre]; apply prefix_heads_and_tails in Hpre as [Heq Hpre];
      subst; inversion Hlen; apply IH in H0; auto; subst; reflexivity.
Qed.

Lemma prefix_app_front_eq_length : forall {X:Type} {ds1 ds2 ds3 ds4 : list X},
  length ds1 = length ds3 ->
  prefix (ds1 ++ ds2) (ds3 ++ ds4) ->
  prefix ds2 ds4.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 ds4 Hlen Hpre; simpl in *.
  - symmetry in Hlen. apply length_zero_iff_nil in Hlen. subst; auto.
  - destruct ds3 as [| d3 ds3'] eqn:Eqds3; simpl in *.
    + discriminate Hlen.
    + apply prefix_heads_and_tails in Hpre as [Heq Hpre]; subst.
      inversion Hlen. eapply IH in H0; eauto.
Qed.

Lemma app_eq_head_tail : forall {X :Type} (l1 l2 l3: list X) (x :X),
  x::l1 = l2 ++ l3 ->
  l2 = []  \/ (exists l2', l2 = x::l2').
Proof.
  intros X. induction l1 as [| x1 l1' IH]; intros l2 l3 x Heq.
  - symmetry in Heq. apply app_eq_unit in Heq.
    destruct Heq as [ [Hl2 Hl3] | [Hl2 Hl3] ].
    + left; auto.
    + right; eexists; eauto.
  - destruct l2 as [| x2 l2'] eqn:Eql2.
    + left. reflexivity.
    + simpl in Heq. inversion Heq.
      apply IH in H1; subst. destruct H1 as [H | H].
      * right. eexists; eauto.
      * destruct H as [l Hl].
        right. eexists; eauto.
Qed.

(** * Lemmas for the proof of [ideal_eval_relative_secure] *)

Lemma ideal_eval_dirs : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  (forall d, In d ds -> d = DStep \/ d = DForce).
Proof.
  intros c sst ast b ds stt astt bt os Hev.
  induction Hev; intros d Hin; simpl in Hin; try (now destruct Hin; auto).
  - apply in_app_or in Hin as [Hds1 | Hds2]; auto.
  - apply IHHev; auto.
Qed.

Lemma ideal_eval_spec_needs_force : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  In DForce ds.
Proof.
  intros c st ast ds stt astt os Heval.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Lemma ideal_eval_spec_bit_monotonic : forall c st ast ds stt astt bt os,
  |-i <(st, ast, true, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  bt = true.
Proof.
  intros c st ast ds stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto.
Qed.

Lemma ideal_eval_spec_eval_no_spec : forall c st ast ds stt astt os,
  |-i <( st, ast, false, ds )> =[ c ]=> <( stt, astt, false, os )> ->
    <( st, ast, false, ds )> =[ c ]=> <( stt, astt, false, os )>.
Proof.
  intros. remember false as b in H at 1. rewrite <- Heqb at 1. remember false as b' in H.
  rewrite <- Heqb'.
  induction H; try (now subst; econstructor; eauto).
  + destruct b'; [apply ideal_eval_spec_bit_monotonic in H0|now econstructor;eauto].
    now subst.
  + apply ideal_eval_spec_bit_monotonic in H. now subst.
Qed.

Lemma ideal_eval_final_spec_bit_false : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, false, os)> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros c st ast ds stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; intros d Hin; subst; simpl in *; try (now destruct Hin; auto); auto.
  - (* Seq *)
    destruct b' eqn:Eqb'.
    + apply ideal_eval_spec_bit_monotonic in Hev2. discriminate Hev2.
    + apply in_app_or in Hin as [Hds1 | Hds2].
      * apply IHHev1; auto.
      * apply IHHev2; auto.
  - apply ideal_eval_spec_bit_monotonic in Hev. discriminate Hev.
Qed.

Lemma ideal_eval_spec_bit_deterministic :
  forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    |-i <(st1, ast1, b, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    |-i <(st2, ast2, b, ds)> =[ c ]=> <(stt2, astt2, bt2, os2 )> ->
    bt1 = bt2.
Proof.
  intros c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  destruct b eqn:Eqb.
  - apply ideal_eval_spec_bit_monotonic in Hev1, Hev2. subst; auto.
  - destruct bt1 eqn:Eqbt1; destruct bt2 eqn:Eqbt2; auto.
    + apply ideal_eval_spec_needs_force in Hev1.
      eapply ideal_eval_final_spec_bit_false in Hev1; eauto. inversion Hev1.
    + apply ideal_eval_spec_needs_force in Hev2.
      eapply ideal_eval_final_spec_bit_false in Hev2; eauto. inversion Hev2.
Qed.

Lemma ideal_eval_obs_length : forall c st ast b ds stt astt bt os,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  length ds = length os.
Proof.
  intros c st ast b ds stt astt bt os Hev. induction Hev; simpl; auto.
  do 2 rewrite app_length. auto.
Qed.

Lemma ideal_eval_small_step_obs_length : forall c st ast b ds ct stt astt bt os,
  <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof.
  intros c st ast b ds ct stt astt bt os Hev. induction Hev; simpl; auto.
Qed.

Lemma multi_ideal_obs_length : forall c st ast b ds ct stt astt bt os,
  <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof.
  intros c st ast b ds ct stt astt bt os Hev. induction Hev; simpl; auto.
  do 2 rewrite app_length. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_dirs_split : forall c st ast ds stt astt os,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  exists ds1 ds2, (forall d, In d ds1 -> d = DStep) /\ ds = ds1 ++ [DForce] ++ ds2 .
Proof.
  intros c st ast ds stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl; eauto; try discriminate.
  - destruct b' eqn:Eqb'.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev1 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists ds3; exists (ds4 ++ ds2). split; auto.
      rewrite app_comm_cons. rewrite app_assoc. simpl in Heq. rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev2 in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (ds1 ++ ds3); exists ds4. split.
      * intros d H. apply in_app_or in H as [Hds1 | Hds3]; auto.
        eapply ideal_eval_final_spec_bit_false in Hev1; [| eapply Hds1]. auto.
      * rewrite <- app_assoc. simpl in Heq. rewrite Heq. reflexivity.
  - (* IF non-speculative *)
    simpl in Hev. destruct (beval st be) eqn:Eqbe.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * simpl in Heq. rewrite Heq. reflexivity.
    + assert (L1: false = false) by reflexivity; assert (L2: true = true) by reflexivity.
      apply IHHev in L2; auto. destruct L2 as [ds3 [ds4 [Hin Heq] ] ].
      exists (DStep::ds3); exists ds4. split; simpl.
      * intros d H; destruct H; auto.
      * simpl in Heq. rewrite Heq. reflexivity.
  - (* IF speculative *)
    exists []; exists ds. split; simpl.
    + intros d H; destruct H.
    + reflexivity.
Qed.

Lemma ideal_eval_no_spec : forall c st ast ds stt astt bt os,
  (forall d, In d ds -> d = DStep) ->
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  <((c, st, ast ))> -->*^os <((skip, stt, astt))>.
Proof.
  intros c st ast ds stt astt bt os Hds Heval.
  apply seq_big_to_small_step. apply cteval_equiv_seq_spec_eval.
  unfold seq_spec_eval. exists ds. split; [assumption|].
  assert(bt = false). { destruct bt; [|reflexivity].
    apply ideal_eval_spec_needs_force in Heval. apply Hds in Heval. discriminate. }
  subst. now apply ideal_eval_spec_eval_no_spec.
Qed.

Lemma multi_ideal_add_snd_com : forall c st ast ct stt astt ds os c2 b bt,
  <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  <((c;c2, st, ast, b))> -->i*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma ideal_exec_split_by_dirs : forall c st ast b ds stt astt bt os ds1 ds2,
  |-i <(st, ast, b, ds)> =[ c ]=> <(stt, astt, bt, os)> ->
  ds = ds1 ++ ds2 ->
  exists cm stm astm bm os1 os2,
    <((c, st, ast, b))> -->i*_ds1^^os1 <((cm, stm, astm, bm))> /\
    |-i <(stm, astm, bm, ds2)> =[ cm ]=> <(stt, astt, bt, os2)> /\
    os = os1++os2.
Proof.
  intros c st ast b ds stt astt bt os ds1 ds2 Hev.
  generalize dependent ds2; generalize dependent ds1.
  induction Hev; intros ds3 ds4 Hds.
  - (* Skip *)
    symmetry in Hds. apply app_eq_nil in Hds. destruct Hds; subst.
    eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
    + eapply multi_ideal_refl.
    + eapply Ideal_Skip.
    + reflexivity.
  - (* Asgn *)
    symmetry in Hds. apply app_eq_nil in Hds. destruct Hds; subst.
    eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
    + eapply multi_ideal_refl.
    + eapply Ideal_Asgn. reflexivity.
    + reflexivity.
  - (* Seq *)
    destruct (app_eq_prefix Hds) as [ [ds H] | [ds H] ]; subst.
    + rewrite <- app_assoc in Hds. apply app_inv_head in Hds. subst.
      destruct (IHHev2 ds ds4) as [ cm [ stm [ astm [ bm [ os3 [ os4 [ H [ H' ? ] ] ] ] ] ] ] ]; [reflexivity|subst].
      exists cm, stm, astm, bm, (os1 ++ os3), os4.
      split.
      { apply ideal_big_to_small_step in Hev1.
        eapply multi_ideal_combined_executions.
        { eapply multi_ideal_add_snd_com. eassumption. }
        change ds with ([] ++ ds). change os3 with ([] ++ os3).
        econstructor; [constructor|assumption]. }
      split; [assumption|now rewrite app_assoc].
    + rewrite <- app_assoc in Hds. apply app_inv_head in Hds. subst.
      destruct (IHHev1 ds3 ds) as [ cm [ stm [ astm [ bm [ os3 [ os4 [ H [ H' ? ] ] ] ] ] ] ] ]; [reflexivity|subst].
      exists (Seq cm c2), stm, astm, bm, os3, (os4 ++ os2).
      split. { now apply multi_ideal_add_snd_com. }
      split; [|now rewrite app_assoc].
      econstructor; eassumption.
  - (* IF *)
    apply app_eq_head_tail in Hds as L.
    destruct L as [Hds3 | [dsm Hdsm] ].
    + eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
      * subst. apply multi_ideal_refl.
      * subst; simpl in Hds; subst.
        econstructor; eauto.
      * auto.
    + subst. simpl in Hds. inversion Hds.
      apply IHHev in H0.
      destruct H0 as [cm [stm [astm [bm [os3 [os4 [Hsmall [Hideal Hos] ] ] ] ] ] ] ].
      eexists; eexists; eexists; eexists; eexists; eexists; split; [| split]; eauto.
      * replace (DStep::dsm) with ([DStep]++dsm) by auto.
        eapply multi_ideal_trans; [econstructor | eauto].
      * subst; eauto.
  - (* IF_F *)
    apply app_eq_head_tail in Hds as L.
    destruct L as [Hds3 | [dsm Hdsm] ].
    + eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
      * subst. apply multi_ideal_refl.
      * subst; simpl in Hds; subst.
        econstructor; eauto.
      * auto.
    + subst. simpl in Hds. inversion Hds.
      apply IHHev in H0.
      destruct H0 as [cm [stm [astm [bm [os3 [os4 [Hsmall [Hideal Hos] ] ] ] ] ] ] ].
      eexists; eexists; eexists; eexists; eexists; eexists; split; [| split]; eauto.
      * replace (DForce::dsm) with ([DForce]++dsm) by auto.
        eapply multi_ideal_trans; [econstructor | eauto].
      * subst; eauto.
  - (* While *)
    apply IHHev in Hds.
    destruct Hds as [cm [stm [astm [bm [os3 [os4 [Hsmall [Hideal Hos] ] ] ] ] ] ] ].
    eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
    + replace (ds3) with ([]++ds3) by (apply app_nil_l).
      eapply multi_ideal_trans.
      * econstructor.
      * eapply Hsmall.
    + eauto.
    + eauto.
  - (* Aread *)
    apply app_eq_head_tail in Hds as L.
    destruct L as [Hds3 | [dsm Hdsm] ].
    + eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
      * subst. apply multi_ideal_refl.
      * subst; simpl in Hds; subst.
        econstructor; eauto.
      * subst; eauto.
    + subst. simpl in Hds. inversion Hds.
      symmetry in H1. apply app_eq_nil in H1. destruct H1; subst.
      eexists; eexists; eexists; eexists; eexists; eexists; split; [| split]; eauto.
      * replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
        eapply multi_ideal_trans; [econstructor |]; eauto.
        econstructor.
      * econstructor.
      * eauto.
  - (* Write *)
    apply app_eq_head_tail in Hds as L.
    destruct L as [Hds3 | [dsm Hdsm] ].
    + eexists; eexists; eexists; eexists; eexists; eexists; split; [| split].
      * subst. apply multi_ideal_refl.
      * subst; simpl in Hds; subst.
        econstructor; eauto.
      * subst; eauto.
    + subst. simpl in Hds. inversion Hds.
      symmetry in H0. apply app_eq_nil in H0. destruct H0; subst.
      eexists; eexists; eexists; eexists; eexists; eexists; split; [| split]; eauto.
      * replace ([DStep]) with ([DStep]++[]) by (apply app_nil_r).
        eapply multi_ideal_trans; [econstructor |]; eauto.
        econstructor.
      * econstructor.
      * eauto.
Qed.

Lemma ideal_eval_small_step_spec_needs_force : forall c st ast ds ct stt astt os,
  <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, true))> ->
  In DForce ds.
Proof.
  intros c st ast ds ct stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl in *; try discriminate; auto.
Qed.

Lemma multi_ideal_spec_needs_force : forall c st ast ds ct stt astt os,
  <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, true))> ->
  In DForce ds.
Proof.
  intros c st ast ds ct stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl in *; try discriminate.
  apply in_or_app. destruct b' eqn:Eqb'.
  - apply ideal_eval_small_step_spec_needs_force in H; auto.
  - right. apply IHHev; auto.
Qed.

Lemma ideal_eval_small_step_spec_bit_monotonic : forall c st ast ds ct stt astt bt os,
  <((c, st, ast, true))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros c st ast ds ct stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall c st ast ds ct stt astt bt os,
  <((c, st, ast, true))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros c st ast ds ct stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma ideal_eval_small_step_final_spec_bit_false : forall c st ast ds ct stt astt os,
  <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros c st ast ds ct stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; subst; intros d Hin; simpl in *; try destruct Hin;
  try discriminate; try contradiction; auto.
Qed.

Lemma multi_ideal_final_spec_bit_false : forall c st ast ds ct stt astt os,
  <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros c st ast ds ct stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; intros d Hin; simpl in *; subst; try contradiction.
  destruct b' eqn:Eqb'.
  - apply multi_ideal_spec_bit_monotonic in Hev. discriminate.
  - apply in_app_or in Hin as [Hin | Hin].
    + destruct b eqn:Eqb.
      * apply ideal_eval_small_step_spec_bit_monotonic in H. discriminate.
      * eapply ideal_eval_small_step_final_spec_bit_false in Hin; eauto.
    + apply IHHev; auto.
Qed.

Lemma ideal_eval_small_step_no_spec : forall c st ast ds ct stt astt bt os,
    <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, bt))> ->
    (forall d, In d ds -> d = DStep) ->
    <((c, st, ast ))> -->^os <((ct, stt, astt))>.
Proof.
  intros c st ast ds ct stt astt bt os Hev.
  remember false as b eqn:Eqb. induction Hev; intros Hds;
  try (now subst; econstructor; eauto).
  - assert (L: In DForce [DForce]) by (simpl; auto).
    apply Hds in L. inversion L.
Qed.

Lemma multi_ideal_no_spec : forall c st ast ds ct stt astt bt os,
    <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
    (forall d, In d ds -> d = DStep) ->
    <((c, st, ast ))> -->*^os <((ct, stt, astt))>.
Proof.
  intros c st ast ds ct stt astt bt os Hev.
  remember false as b eqn:Eqb. induction Hev; intros Hds; subst.
  - apply multi_seq_refl.
  - assert (L1: forall d, In d ds1 -> d = DStep).
    { intros d Hd. apply Hds. apply in_or_app. auto. }
    assert (L2: forall d, In d ds2 -> d = DStep).
    { intros d Hd. apply Hds. apply in_or_app. auto. }
    destruct b' eqn:Eqb'.
    + apply ideal_eval_small_step_spec_needs_force in H.
      apply L1 in H. inversion H.
    + apply ideal_eval_small_step_no_spec in H; auto.
      eapply multi_seq_trans.
      * eapply H.
      * apply IHHev; auto.
Qed.

Lemma seq_to_ideal : forall c st ast ct stt astt os,
  <((c, st, ast ))> -->^os <((ct, stt, astt))> ->
  <((c, st, ast, false))> -->i_(repeat DStep (length os))^^os <((ct, stt, astt, false))>.
Proof.
  intros.
  now induction H; constructor.
Qed.

Lemma multi_seq_to_ideal : forall c st ast ct stt astt os,
  <((c, st, ast ))> -->*^os <((ct, stt, astt))> ->
  <((c, st, ast, false))> -->i*_(repeat DStep (length os))^^os <((ct, stt, astt, false))>.
Proof.
  intros. induction H.
  - apply multi_ideal_refl.
  - apply seq_to_ideal in H.
    rewrite app_length, repeat_app.
    eapply multi_ideal_trans; eauto.
Qed.

Lemma seq_small_step_if_total : forall c be ct cf st ast,
  c = <{{if be then ct else cf end}}> ->
  exists c' stt astt os,
  <((c, st, ast))> -->^os <((c', stt, astt))> /\ os <> [].
Proof.
  intros c be ct cf st ast Heq. subst.
  repeat econstructor. intros Contra. inversion Contra.
Qed.

Lemma seq_small_step_to_multi_seq : forall c st ast ct stt astt os,
  <((c, st, ast))> -->^os <((ct, stt, astt))> ->
  <((c, st, ast))> -->*^os <((ct, stt, astt))>.
Proof.
  intros c st ast ct stt astt os Hev.
  rewrite <- app_nil_r. eapply multi_seq_trans; eauto.
  apply multi_seq_refl.
Qed.

Lemma seq_same_obs_com_if : forall be ct cf st1 st2 ast1 ast2,
  seq_same_obs <{{ if be then ct else cf end }}> st1 st2 ast1 ast2 ->
  beval st1 be = beval st2 be.
Proof.
  intros be ct cf st1 st2 ast1 ast2 Hsec.
  remember <{{if be then ct else cf end}}> as c eqn:Eqc.
  assert (L1: exists c' stt astt os, <((c, st1, ast1))> -->^os <((c', stt, astt))> /\ os <> []).
  { eapply seq_small_step_if_total; eauto. }
  assert (L2: exists c' stt astt os, <((c, st2, ast2))> -->^os <((c', stt, astt))> /\ os <> []).
  { eapply seq_small_step_if_total; eauto. }
  destruct L1 as [c1 [stt1 [astt1 [os1 [Hev1 Hneq1] ] ] ] ].
  destruct L2 as [c2 [stt2 [astt2 [os2 [Hev2 Hneq2] ] ] ] ].
  apply seq_small_step_to_multi_seq in Hev1, Hev2.
  eapply Hsec in Hev2 as Hpre; [| eapply Hev1].
  inversion Hev1; subst; clear Hev1.
  - destruct Hneq1; auto.
  - inversion Hev2; subst; clear Hev2.
    + destruct Hneq2; auto.
    + inversion H1; subst; clear H1. inversion H; subst; clear H.
      destruct Hpre as [Hpre | Hpre]; simpl in Hpre.
      * apply prefix_heads in Hpre. inversion Hpre; auto.
      * apply prefix_heads in Hpre. inversion Hpre; auto.
Qed.

Lemma multi_seq_add_snd_com : forall c st ast ct stt astt os c2,
  <((c, st, ast))> -->*^os <((ct, stt, astt))> ->
  <((c;c2, st, ast))> -->*^os <((ct;c2, stt, astt))>.
Proof.
  intros c st ast ct stt astt os c2 Hev.
  induction Hev.
  - apply multi_seq_refl.
  - eapply multi_seq_trans.
    + econstructor. eauto.
    + apply IHHev.
Qed.

Lemma seq_same_obs_com_seq : forall c1 c2 st1 st2 ast1 ast2,
  seq_same_obs <{{ c1; c2 }}> st1 st2 ast1 ast2 ->
  seq_same_obs c1 st1 st2 ast1 ast2.
Proof.
  intros c1 c2 st1 st2 ast1 ast2 Hsec. unfold seq_same_obs.
  intros stt1 stt2 astt1 astt2 os1 os2 ct1 ct2 Hev1 Hev2.
  eapply multi_seq_add_snd_com in Hev1, Hev2. eapply Hsec in Hev2; eauto.
Qed.

Lemma ideal_one_step_obs : forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  <((c, st1, ast1, false))> -->i_[DForce]^^os1 <((ct, stt1, astt1, true))> ->
  <((c, st2, ast2, false))> -->i_[DForce]^^os2 <((ct, stt2, astt2, true))> ->
  os1 = os2.
Proof.
  intros c ct st ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 Hobs Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ast2;
  generalize dependent st2.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev1; intros st2 ast2 Hobs stt2 astt2 os2 Hev2; try(inversion Hev2; subst; auto);
  try discriminate.
  - eapply IHHev1; eauto. eapply seq_same_obs_com_seq; eauto.
  - apply seq_same_obs_com_if in Hobs. rewrite Hobs. reflexivity.
Qed.

(* HIDE *)
(* Currently unused, but maybe helpful in the future. *)
Lemma seq_eval_small_step_preserves_seq_same_obs :
  forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2,
    <((c, st1, ast1))>  -->^os1 <((ct, stt1, astt1))> ->
    <((c, st2, ast2))>  -->^os2 <((ct, stt2, astt2))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    seq_same_obs ct stt1 stt2 astt1 astt2.
Proof.
  intros c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 Hev1 Hev2 Hsec .
  unfold seq_same_obs. intros stt1' stt2' astt1' astt2' os1' os2' ct1 ct2 Hmul1 Hmul2.
  assert (L1: <((c, st1, ast1))> -->*^ (os1++os1') <((ct1, stt1', astt1'))> ).
  { eapply multi_seq_trans; eauto. }
  assert (L2: <((c, st2, ast2))> -->*^ (os2++os2') <((ct2, stt2', astt2'))> ).
  { eapply multi_seq_trans; eauto. }
  eapply Hsec in L2; eauto. destruct L2 as [Hpre | Hpre].
  - apply prefix_app_front_eq_length in Hpre; auto.
    eapply seq_small_step_obs_length in Hev2; eauto.
  - apply prefix_app_front_eq_length in Hpre; auto.
    eapply seq_small_step_obs_length in Hev2; eauto.
Qed.
(* /HIDE *)

(* SOONER: It could hold that the [seq_same_obs]
   is even preserved for different final coms. *)
(* CH: Maybe better is to just drop the length assumption instead though *)
Lemma multi_seq_preserves_seq_same_obs :
  forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2,
    <((c, st1, ast1))>  -->*^os1 <((ct, stt1, astt1))> ->
    <((c, st2, ast2))>  -->*^os2 <((ct, stt2, astt2))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    length os1 = length os2 ->
    seq_same_obs ct stt1 stt2 astt1 astt2.
Proof.
  intros c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 Hev1 Hev2 Hsec Hlen.
  unfold seq_same_obs. intros stt1' stt2' astt1' astt2' os1' os2' ct1 ct2 Hmul1 Hmul2.
  assert (L1: <((c, st1, ast1))> -->*^ (os1++os1') <((ct1, stt1', astt1'))> ).
  { eapply multi_seq_combined_executions; eauto.  }
  assert (L2: <((c, st2, ast2))> -->*^ (os2++os2') <((ct2, stt2', astt2'))> ).
  { eapply multi_seq_combined_executions; eauto. }
  eapply Hsec in L2; eauto. destruct L2 as [Hpre | Hpre].
  - apply prefix_app_front_eq_length in Hpre; auto.
  - apply prefix_app_front_eq_length in Hpre; auto.
Qed.

(* HIDE *)
(* Currently unused but maybe helpful in the future. *)
Lemma seq_eval_small_step_com_deterministic :
    forall c st1 ast1 ct1 stt1 astt1 os1 st2 ast2 ct2 stt2 astt2 os2,
    <((c, st1, ast1))>  -->^os1 <((ct1, stt1, astt1))> ->
    <((c, st2, ast2))>  -->^os2 <((ct2, stt2, astt2))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    ct1 = ct2.
Proof.
  intros c st1 ast1 ct1 stt1 astt1 os1 st2 ast2 ct2 stt2 astt2 os2 Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ct2;
  generalize dependent ast2 ; generalize dependent st2.
  induction Hev1; intros st2 ast2 ct2 stt2 astt2 ost2 Hev2 Hsec;
  try (now inversion Hev2; subst; auto).
  - inversion Hev2; subst; auto.
    + apply seq_same_obs_com_seq in Hsec as Hc1.
      apply IHHev1 in H7; subst; auto.
    + inversion Hev1.
  - apply seq_same_obs_com_if in Hsec.
    inversion Hev2; subst. rewrite Hsec. reflexivity.
Qed.

Lemma ideal_eval_small_step_com_deterministic :
    forall c st1 ast1 b ds ct1 stt1 astt1 bt os1 st2 ast2 ct2 stt2 astt2 os2,
    <((c, st1, ast1, b))>  -->i_ds^^os1 <((ct1, stt1, astt1, bt))> ->
    <((c, st2, ast2, b))>  -->i_ds^^os2 <((ct2, stt2, astt2, bt))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    ct1 = ct2.
Proof.
  intros c st1 ast1 b ds ct1 stt1 astt1 bt os1 st2 ast2 ct2 stt2 astt2 os2 Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ct2;
  generalize dependent ast2 ; generalize dependent st2.
  induction Hev1; intros st2 ast2 ct2 stt2 astt2 ost2 Hev2 Hsec;
  try (now inversion Hev2; subst; auto).
  - inversion Hev2; subst; auto.
    + apply seq_same_obs_com_seq in Hsec as Hc1.
      apply IHHev1 in H10; subst; auto.
    + inversion Hev1.
  - apply seq_same_obs_com_if in Hsec.
    inversion Hev2; subst. rewrite Hsec. reflexivity.
  - apply seq_same_obs_com_if in Hsec.
    inversion Hev2; subst. rewrite Hsec. reflexivity.
Qed.
(* /HIDE *)

Lemma ideal_small_step_com_deterministic :
  forall c b ds st1 ast1 ct1 stt1 astt1 bt1 os1 st2 ast2 ct2 stt2 astt2 bt2 os2,
    <((c, st1, ast1, b))>  -->i_ds^^os1 <((ct1, stt1, astt1, bt1))> ->
    <((c, st2, ast2, b))>  -->i_ds^^os2 <((ct2, stt2, astt2, bt2))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    ct1 = ct2.
Proof.
    intros c b ds st1 ast1 ct1 stt1 astt1 bt1 os1 st2 ast2 ct2 stt2 astt2 bt2 os2 Hev1.
    generalize dependent os2; generalize dependent bt2;
    generalize dependent astt2; generalize dependent stt2;
    generalize dependent ct2; generalize dependent ast2;
    generalize dependent st2.
    induction Hev1; intros st2 ast2 ct2 stt2 astt2 bt2 ost2 Hev2 Hsec;
    try (now inversion Hev2; subst; auto).
    - inversion Hev2; subst; auto.
      + apply seq_same_obs_com_seq in Hsec as Hc1.
        apply IHHev1 in H10; subst; auto.
      + inversion Hev1.
    - apply seq_same_obs_com_if in Hsec.
      inversion Hev2; subst. rewrite Hsec. reflexivity.
    - apply seq_same_obs_com_if in Hsec.
      inversion Hev2; subst. rewrite Hsec. reflexivity.
Qed.

Lemma ideal_small_step_obs_type : forall c b1 st1 ast1 stt1 astt1 ct1 ds1 os1 b2 ct2 st2 ast2 stt2 astt2 ds2 os2 bt1 bt2,
  <((c, st1, ast1, b1))> -->i_ds1^^os1 <((ct1, stt1, astt1, bt1))> ->
  <((c, st2, ast2, b2))> -->i_ds2^^os2 <((ct2, stt2, astt2, bt2))> ->
  match os2 with
  | [] => os1 = []
  | OBranch _ :: os => exists b, os1 = OBranch b :: os
  | OARead _ _ :: os => exists a i, os1 = OARead a i :: os
  | OAWrite _ _ :: os => exists a i, os1 = OAWrite a i :: os
  end.
Proof.
  induction c; intros;
  inversion H; inversion H0; subst; eauto.
  + eapply IHc1; eauto.
  + inversion H12.
  + inversion H23.
Qed.

Corollary ideal_small_step_obs_length : forall c b1 st1 ast1 stt1 astt1 ct1 ds1 os1 b2 ct2 st2 ast2 stt2 astt2 ds2 os2 bt1 bt2,
  <((c, st1, ast1, b1))> -->i_ds1^^os1 <((ct1, stt1, astt1, bt1))> ->
  <((c, st2, ast2, b2))> -->i_ds2^^os2 <((ct2, stt2, astt2, bt2))> ->
  length os1 = length os2.
Proof.
  intros. eapply ideal_small_step_obs_type in H; [|now apply H0].
  destruct os1; subst; [now auto|].
  destruct o.
  2, 3 : now (do 2 destruct H); subst.
  now destruct H; subst.
Qed.

(** * Unwinding Lemma for Ideal Misspeculated Executions *)

Lemma ideal_prefix_dirs :
  forall c st1 st2 ast1 ast2 b ds1 ds2 stt1 stt2 astt1 astt2 bt os1 os2,
  |-i <(st1, ast1, b, ds1)> =[ c ]=> <(stt1, astt1, bt, os1)> ->
  |-i <(st2, ast2, b, ds2)> =[ c ]=> <(stt2, astt2, bt, os2)> ->
  (prefix ds1 ds2 \/ prefix ds2 ds1) ->
  b = true ->
  bt = true ->
  ds1 = ds2.
Proof.
  intros c st1 st2 ast1 ast2 b ds1 ds2 stt1 stt2 astt1 astt2 bt os1 os2 Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ds2;
  generalize dependent ast2; generalize dependent st2.
  induction Hev1; intros st2 ast2 ds2' stt2 astt2 ost2 Hev2 Hpre Hb Hbt;
  try (now inversion Hev2; subst; auto).
  - inversion Hev2; subst; clear Hev2.
    apply ideal_eval_spec_bit_monotonic in H1 as Hb'0; subst.
    apply ideal_eval_spec_bit_monotonic in Hev1_1 as Hb'; subst.
    destruct Hpre as [Hpre | Hpre]; apply prefix_app in Hpre as L.
    + apply IHHev1_1 in H1; auto. subst.
      apply prefix_append_front in Hpre.
      apply IHHev1_2 in H10; auto. subst. reflexivity.
    + apply IHHev1_1 in H1; try tauto. subst.
      apply prefix_append_front in Hpre.
      apply IHHev1_2 in H10; auto. subst. reflexivity.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    + destruct Hpre as [Hpre | Hpre];
      apply prefix_heads_and_tails in Hpre as [_ Hpre];
      apply IHHev1 in H10; auto; rewrite H10; reflexivity.
    + destruct Hpre as [Hpre | Hpre];
      apply prefix_heads_and_tails in Hpre as [Contra _];
      discriminate.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    + destruct Hpre as [Hpre | Hpre];
      apply prefix_heads_and_tails in Hpre as [Contra _];
      discriminate.
    + destruct Hpre as [Hpre | Hpre];
      apply prefix_heads_and_tails in Hpre as [_ Hpre];
      apply IHHev1 in H10; auto; rewrite H10; reflexivity.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    apply IHHev1 in H9; auto.
Qed.

Lemma ideal_misspeculated_unwinding : forall c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt os1 os2,
  |-i <(st1, ast1, b, ds)> =[ c ]=> <(stt1, astt1, bt, os1)> ->
  |-i <(st2, ast2, b, ds)> =[ c ]=> <(stt2, astt2, bt, os2)> ->
  b = true ->
  bt = true ->
  os1 = os2.
Proof.
  intros c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt os1 os2 Hev1.
  generalize dependent os2;  generalize dependent astt2;
  generalize dependent stt2;  generalize dependent ast2;
  generalize dependent st2.
  induction Hev1; intros st2 ast2 stt2 astt2 ost2 Hev2 Hb Hbt;
  try (now inversion Hev2; subst; auto).
  - inversion Hev2; subst; clear Hev2.
    apply ideal_eval_spec_bit_monotonic in H5 as Hb'0; subst.
    apply ideal_eval_spec_bit_monotonic in Hev1_1 as Hb'; subst.
    assert (L: ds0 = ds1).
    { apply app_eq_prefix in H1 as Hpre.
      eapply ideal_prefix_dirs in Hpre; eauto. } subst.
    apply app_inv_head_iff in H1. subst.
    apply IHHev1_1 in H5; auto. apply IHHev1_2 in H10; auto.
    subst. reflexivity.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    apply IHHev1 in H10; auto. subst. reflexivity.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    apply IHHev1 in H10; auto. subst. reflexivity.
  - inversion Hev2; subst; clear Hev2; simpl in *.
    apply IHHev1 in H9; auto.
Qed.

(** * Conjectures for the proof of ideal_eval_relative_secure *)

(* HIDE *)

(* This conjecture does not hold, look at c = skip; skip; skip :
      <((c, st1, ast1))>  -->*^[] <((skip; skip, st1, ast1))> /\
      <((c, st2, ast2))>  -->*^[] <((skip, st2, ast2))> /\
      seq  seq_same_obs c st1 st2 ast1 ast2 /\
      length [] = length []
    But: skip; skip <> skip
*)
Lemma multi_seq_com_deterministic :
    forall c st1 ast1 ct1 stt1 astt1 os1 st2 ast2 ct2 stt2 astt2 os2,
    <((c, st1, ast1))>  -->*^os1 <((ct1, stt1, astt1))> ->
    <((c, st2, ast2))>  -->*^os2 <((ct2, stt2, astt2))> ->
    seq_same_obs c st1 st2 ast1 ast2 ->
    length os1 = length os2 ->
    ct1 = ct2.
Proof.
Abort.

(* Same problem as in [multi_seq_com_deterministic]. Steps without observations
   and directions do not destroy the seq_same_obs property. but lead to
   different ct1 adn ct2. Needs a measure that exactly same amount of single
  steps are taken. *)
Lemma multi_ideal_com_deterministic :
    forall c ds b st1 ast1 ct1 stt1 astt1 bt1 os1 st2 ast2 ct2 stt2 astt2 bt2 os2,
      <((c, st1, ast1, b))>  -->i*_ds^^os1 <((ct1, stt1, astt1, bt1))> ->
      <((c, st2, ast2, b))>  -->i*_ds^^os2 <((ct2, stt2, astt2, bt2))> ->
      seq_same_obs c st1 st2 ast1 ast2 ->
      ct1 = ct2.
Proof.
Abort.
(* /HIDE *)

Lemma multi_ideal_single_force_direction :
  forall c st ast ct astt stt os,
    <(( c, st, ast, false ))> -->i*_ [DForce]^^ os <((ct, stt, astt, true))> ->
    exists cm1 stm1 astm1 os1 cm2 stm2 astm2 os2 os3,
    <((c, st, ast, false))> -->i*_[]^^os1 <((cm1, stm1, astm1, false))> /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os2 <((cm2, stm2, astm2, true))> /\
    <((cm2, stm2, astm2, true))>  -->i*_[]^^os3 <((ct, stt, astt, true))> /\
    os = os1 ++ os2 ++ os3.
Proof.
  intros c st ast ct astt stt os Hev. remember [DForce] as ds eqn:Eqds.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; try discriminate; subst.
  assert (L: ds1 = [] \/ ds2 = []).
  { destruct ds1; auto; destruct ds2; auto. inversion Eqds.
    apply app_eq_nil in H2 as [_ Contra]. inversion Contra. }
  destruct L as [L | L]; subst; simpl in *.
  - assert (Hb': b' = false).
    { destruct b' eqn:Eqb'; auto. apply ideal_eval_small_step_spec_needs_force in H. simpl in H. destruct H. }
    apply IHHev in Eqds; auto; subst.
    destruct Eqds as [cm1 [stm1 [astm1 [osm1 [cm2 [stm2 [astm2 [os3 [os4 [H1 [H2 [H3 H4] ] ] ] ] ] ] ] ] ] ] ].
    exists cm1; exists stm1; exists astm1; exists (os1++osm1); exists cm2; exists stm2; exists astm2; exists os3; exists os4.
    split; [| split; [| split] ]; auto.
    + replace ([] :dirs) with ([]++[] :dirs) by (apply app_nil_l).
      eapply multi_ideal_trans; eauto.
    + rewrite <- app_assoc. rewrite H4. reflexivity.
  - rewrite app_nil_r in Eqds. subst.
    assert (Hb': b' = true).
    { destruct b' eqn:Eqb'; auto. apply ideal_eval_small_step_final_spec_bit_false with (d:=DForce) in H; simpl; auto.
      inversion H. } subst.
    exists c; exists st; exists ast; exists []; exists c'; exists st'; exists ast'; exists os1; exists os2.
    split; [| split; [| split] ]; auto.
    apply multi_ideal_refl.
Qed.

(* HIDE *)
(* If this conjecture holds it could also be used to proof [ideal_eval_relative_secure]. *)
   Conjecture multi_ideal_and_single_step_com_deterministic :
    forall c st1 ast1 ds os cm1 stm1 astm1 ct1 stt1 astt1
            st2 ast2 cm2 stm2 astm2 ct2 stt2 astt2,
      <((c, st1, ast1, false))> -->i*_ds^^os <((cm1, stm1, astm1, false))> ->
      <((cm1, stm1, astm1, false))> -->i_[DForce]^^os <((ct1, stt1, astt1, true))> ->
      <((c, st2, ast2, false))> -->i*_ds^^os <(( cm2, stm2, astm2, false))> ->
      <(( cm2, stm2, astm2, false))>  -->i_[DForce]^^os <((ct2, stt2, astt2, true))> ->
      seq_same_obs c st1 st2 ast1 ast2 ->
      cm1 = cm2 /\ ct1 = ct2.
  (* /HIDE *)

(* HIDE *)
(* This lemma was replaced by [ideal_exec_split_v2] and is here only as an
   initial idea on how to prove the new version. *)
Lemma ideal_exec_split : forall c st ast ds stt astt os ds1 ds2,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  (forall d, In d ds1 -> d = DStep) ->
  ds = ds1 ++ [DForce] ++ ds2 ->
  exists cm1 stm1 astm1 os1 cm2 stm2 astm2 os2 os3,
    <((c, st, ast, false))> -->i*_ds1^^os1 <((cm1, stm1, astm1, false))>  /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os2 <((cm2, stm2, astm2, true))> /\
    |-i <(stm2, astm2, true, ds2)> =[ cm2 ]=> <(stt, astt, true, os3)> /\
    os = os1 ++ os2 ++ os3.
Proof.
  intros c st ast ds stt astt os ds1 ds2 Hev Hds1 Hds. subst.
  apply ideal_exec_split_by_dirs with (ds1:=ds1) (ds2:=[DForce]++ds2) in Hev; auto.
  destruct Hev as [cm1 [stm1 [astm1 [bm1 [os1 [os' [Hsmall1 [Hbig Hos1] ] ] ] ] ] ] ].
  assert(L: bm1 = false).
  { destruct bm1 eqn:Eqbm1; auto.
    apply multi_ideal_spec_needs_force in Hsmall1.
    apply Hds1 in Hsmall1. discriminate. } subst.
  apply ideal_exec_split_by_dirs with (ds1:=[DForce]) (ds2:=ds2) in Hbig; auto.
  destruct Hbig as [cm4 [stm4 [astm4 [bm4 [os'' [os5 [Hsmall2 [Hbig Hos'] ] ] ] ] ] ] ].
  assert (L: bm4 = true).
  { destruct bm4 eqn:Eqb4; auto.
    apply multi_ideal_final_spec_bit_false with (d:=DForce) in Hsmall2; simpl; auto.
    discriminate. } subst.
  apply multi_ideal_single_force_direction in Hsmall2.
  destruct Hsmall2 as [cm2 [stm2 [astm2 [os2 [cm3 [stm3 [astm3 [os3 [os4 [Hsmall2 [Hsmall3 [Hsamll4 Hos''] ] ] ] ] ] ] ] ] ] ] ].
  exists cm2; exists stm2; exists astm2; exists (os1++os2).
  exists cm3; exists stm3; exists astm3; exists (os3). exists (os4++os5).
  split; [| split; [| split] ].
  - replace(ds1) with (ds1++[]) by (apply app_nil_r).
    eapply multi_ideal_combined_executions; eauto.
  - apply Hsmall3.
  - replace(ds2) with ([]++ds2) by (apply app_nil_l).
    eapply ideal_eval_multi_steps; eauto.
  - subst. rewrite app_assoc. do 4 rewrite <- app_assoc.
    reflexivity.
Qed.
(* /HIDE *)

(* HIDE: CH: If we wanted to stick to the original [ideal_exec_split] above,
   can't we even obtain the new conjunct 2 from conjunct 3 and some notion of
   determinism? I don't think that v2 version below is harder to prove than the
   original version though.
         Léon: The additionnal conclusion is actually implied by the other.
   This lemma is equivalent to the previous one. *)

Lemma ideal_exec_split_v2 : forall c st ast ds stt astt os ds1 ds2,
  |-i <(st, ast, false, ds)> =[ c ]=> <(stt, astt, true, os)> ->
  (forall d, In d ds1 -> d = DStep) ->
  ds = ds1 ++ [DForce] ++ ds2 ->
  exists cm1 stm1 astm1 os1 cm2 stm2 astm2 os2 os3,
    <((c, st, ast, false))> -->i*_ds1^^os1 <((cm1, stm1, astm1, false))>  /\
    ~( exists cm1' stm1' astm1',
          <((cm1, stm1, astm1, false))> -->i_[]^^[] <((cm1', stm1', astm1', false))> ) /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os2 <((cm2, stm2, astm2, true))> /\
    |-i <(stm2, astm2, true, ds2)> =[ cm2 ]=> <(stt, astt, true, os3)> /\
    os = os1 ++ os2 ++ os3.
Proof.
  intros.
  specialize (ideal_exec_split c st ast ds stt astt os ds1 ds2 H H0 H1).
  intros [cm1 [ stm1 [ astm1 [ os1 [ cm2 [ stm2 [ astm2 [ os2 [ os3 H' ] ] ] ] ] ] ] ] ].
  destruct H' as [Hc [Hcm1 [ Hcm2 Hos ] ] ].
  repeat eexists; eauto.
  inversion Hcm1; subst.
  + intros [? [? [? Hfalse] ] ].
    inversion Hfalse; subst.
    - eapply ideal_small_step_obs_length in H13; [|apply H2].
      now erewrite <- ideal_eval_small_step_obs_length in H13; [|apply H2].
    - inversion H2.
  + intros [? [? [? Hfalse] ] ].
    inversion Hfalse.
Qed.

(* This looks quite similar to (and maybe simpler than)
           ideal_small_step_com_deterministic *)

Lemma small_step_cmd_determinate : forall c st1 ast1 os ct1 stt1 astt1 st2 ast2 ct2 stt2 astt2,
  <(( c, st1, ast1 ))> -->^ os <(( ct1, stt1, astt1 ))> ->
  <(( c, st2, ast2 ))> -->^ os <(( ct2, stt2, astt2 ))> ->
  ct1 = ct2.
Proof.
  intros c os st1 ast1 ct1 stt1 astt1 st2 ast2 ct2 stt2 astt2 H.
  generalize dependent astt2;
  generalize dependent stt2; generalize dependent ct2;
  generalize dependent ast2 ; generalize dependent st2.
  induction H; intros st2 ast2 ct2 stt2 astt2 H2;
    try (now inversion H2; subst; auto).
  inversion H2; subst.
  - now apply IHseq_eval_small_step in H9; subst.
  - inversion H.
Qed.

(* It's crucial that os=[] here, since otherwise:
   - in the case in which c gets stuck on OOB access for st2
   - if branches evaluate differently in st2 *)
Lemma stuckness_not_data_dependent : forall c st1 ast1 ct1 stt1 astt1 st2 ast2,
  <(( c, st1, ast1 ))> -->^ [] <(( ct1, stt1, astt1 ))> ->
  exists ct2 stt2 astt2,
    <(( c, st2, ast2 ))> -->^ [] <(( ct2, stt2, astt2 ))>.
Proof.
  intros c st1 ast1 ct1 stt1 astt1 st2 ast2 H.
  remember [] as os. revert Heqos.
  induction H; subst;
    try (now inversion 1); try (now repeat econstructor).
  intro; subst. destruct IHseq_eval_small_step; auto.
  do 2 destruct H0. repeat econstructor. apply H0.
Qed.

Lemma multi_ideal_lock_step : forall os c st1 ast1 ct1 stt1 astt1 st2 ast2 ct2 stt2 astt2,
  <(( c, st1, ast1 ))> -->*^os <(( ct1, stt1, astt1 ))> ->
  ~ (exists (cm1 : com) (stm1 : state) (astm1 : astate),
      <(( ct1, stt1, astt1 ))> -->^ [] <(( cm1, stm1, astm1 ))>) ->
  <(( c, st2, ast2 ))> -->*^ os <(( ct2, stt2, astt2 ))> ->
  ~ (exists (cm1 : com) (stm1 : state) (astm1 : astate),
      <((ct2, stt2, astt2 ))> -->^ [] <(( cm1, stm1, astm1 ))>) ->
  ct1 = ct2.
Proof.
  intros c st1 ast1 os ct1 stt1 astt1 st2 ast2 ct2 stt2 astt2 H1mult.
  generalize dependent astt2. generalize dependent stt2. generalize dependent ct2.
  generalize dependent ast2. generalize dependent st2.
  induction H1mult; intros st2 ast2 ct2 stt2 astt2 H1stuck H2mult H2stuck.
  - inversion H2mult; subst; clear H2mult.
    + reflexivity. (* both executions stuck *)
    + (* only one execution stuck -> contradiction *)
      apply app_eq_nil in H. destruct H; subst.
      eapply stuckness_not_data_dependent in H0. exfalso. eauto.
  - inversion H2mult; subst; clear H2mult.
    + (* only one execution stuck -> contradiction *) symmetry in H4.
      apply app_eq_nil in H4. destruct H4; subst.
      eapply stuckness_not_data_dependent in H. exfalso. eauto.
    + (* both executions step at least once *)
      assert (length os0 = length os1) by (eapply seq_small_step_obs_length; eauto).
      assert (os1 = os0).
      { eapply prefix_eq_length; eauto.
        eapply app_eq_prefix; eauto. } subst.
      apply app_inv_head in H0; subst.
      eapply small_step_cmd_determinate in H1; [| now apply H]; subst.
      now eapply IHH1mult; eauto.
Qed.

(** * Ultimate SLH Relative Secure *)

Lemma ideal_eval_relative_secure : forall c st1 st2 ast1 ast2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  ideal_same_obs c st1 st2 ast1 ast2.
Proof.
  unfold ideal_same_obs. intros c st1 st2 ast1 ast2 Hsec
  ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  eapply ideal_eval_spec_bit_deterministic in Hev1 as SameB; try eassumption. subst.
  destruct bt1 eqn:Eqbt1.
  - (* with mis-speculation *)
    eapply ideal_dirs_split in Hev1 as L.
    destruct L as [ds1 [ds2 [Hds1 Heq] ] ]. subst.
    eapply ideal_exec_split_v2 in Hev1; eauto.
    destruct Hev1 as [cm1 [stm1 [astm1 [os1_1 [cm2 [stm2 [astm2 [os1_2 [os1_3 [Hsmall1 [Hmax1 [Hone1 [Hbig1 Hos1] ] ] ] ] ] ] ] ] ] ] ] ].
    eapply ideal_exec_split_v2 in Hev2; eauto.
    destruct Hev2 as [cm1' [stm1' [astm1' [os2_1 [cm2' [stm2' [astm2' [os2_2 [os2_3 [Hsmall2 [Hmax2 [Hone2 [Hbig2 Hos2] ] ] ] ] ] ] ] ] ] ] ] ].
    assert (Hlen2: length os1_1 = length os2_1).
    { apply multi_ideal_obs_length in Hsmall1, Hsmall2. congruence. }
    assert (L: os1_1 = os2_1).
    { apply multi_ideal_no_spec in Hsmall1, Hsmall2; auto.
      eapply Hsec in Hsmall1. eapply Hsmall1 in Hsmall2 as Hpre.
      apply prefix_eq_length in Hpre; auto. } subst.
    assert (L : cm1' = cm1).
    { eapply multi_ideal_no_spec in Hsmall1, Hsmall2; eauto.
      eapply multi_ideal_lock_step; eauto.
      all: intro; (do 3 destruct H). 1:apply Hmax2. 2:apply Hmax1.
      all: eapply seq_to_ideal in H. all: (simpl in H); eauto. } subst.
    assert (Hsec2: seq_same_obs cm1 stm1 stm1' astm1 astm1').
    { apply multi_ideal_no_spec in Hsmall1, Hsmall2; auto.
      eapply multi_seq_preserves_seq_same_obs; eauto. }
    assert (L: cm2 = cm2').
    { eapply ideal_small_step_com_deterministic in Hone2; eauto. } subst.
    eapply ideal_one_step_obs in Hone2; eauto.
    eapply ideal_misspeculated_unwinding in Hbig1; eauto. congruence.
  - (* without mis-speculation *)
    (* LATER: this case is similar to the start of the more interesting case
              above; we can likely share more (e.g. use the same obs_length lemma) *)
    assert (Hds: forall d, In d ds -> d = DStep).
    { intros; eapply ideal_eval_final_spec_bit_false in Hev1; eauto. }
    apply ideal_eval_obs_length in Hev1 as Hos1.
    apply ideal_eval_obs_length in Hev2 as Hos2.
    rewrite Hos1 in Hos2. clear Hos1. unfold seq_same_obs in Hsec.
    eapply ideal_eval_no_spec in Hev1; try assumption.
    eapply ideal_eval_no_spec in Hev2; try assumption.
    assert(H:prefix os1 os2 \/ prefix os2 os1). { eapply Hsec; eassumption. }
    apply prefix_eq_length; assumption.
Qed.

(* LATER: Strengthen the conclusion so that our theorem is termination sensitive
   (and also error sensitive) by looking at prefixes there too. *)

Theorem ultimate_slh_relative_secure :
  forall c st1 st2 ast1 ast2,
    (* some extra assumptions needed by slh_bcc *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure ultimate_slh c st1 st2 ast1 ast2.
Proof. (* from bcc + ideal_eval_relative_secure *)
  unfold relative_secure.
  intros c st1 st2 ast1 ast2 Hunused Hst1b Hst2b Hast1 Hast2 Hseq ds stt1 stt2
    astt1 astt2 bt1 bt2 os1 os2 Hev1 Hev2.
  apply ultimate_slh_bcc in Hev1; try assumption.
  apply ultimate_slh_bcc in Hev2; try assumption.
  eapply (ideal_eval_relative_secure c st1 st2); eassumption.
Qed.

(* HIDE *)
(* CH: Some playing with BCC generalization *)

Definition ct_preservation trans : Prop := forall c,
  (forall st1 st2 ast1 ast2, ideal_same_obs c st1 st2 ast1 ast2) ->
  (forall st1 st2 ast1 ast2, spec_same_obs (trans c) st1 st2 ast1 ast2).

Definition secure_compilation_bw trans :=
  forall c, exists Td To, forall ds st ast ost st' ast' b,
      <(st, ast, false, ds)> =[trans c]=> <(st', ast', b, ost)> ->
     exists oss,
      |-i <(st, ast, false, Td ds)> =[c]=> <(st', ast', b, oss)> /\
      ost = To oss.

(* Theorem 2 of Santiago's POPL submission *)
Theorem ct_preservation_bw : forall trans,
  secure_compilation_bw trans ->
  ct_preservation trans.
Proof.
  unfold secure_compilation_bw, ct_preservation, ideal_same_obs, spec_same_obs.
  intros trans H c Hsrc st1 st2 ast1 ast2
         ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 H1 H2.
  specialize (H c). destruct H as [Td [To H] ].
  apply H in H1. destruct H1 as [oss1 [H1 H1'] ].
  apply H in H2. destruct H2 as [oss2 [H2 H2'] ].
  subst. f_equal. eapply Hsrc; eassumption.
Qed.

(* The same proof also applies in our setting to prove relative security from
   speculative source semantics (our ideal semantics) to speculative target
   semantics for the transformed program. In fact this is very similar to
   our use of BCC, just that in our setting both Td and To are identity. *)
Theorem relative_secure_bw : forall trans,
  secure_compilation_bw trans ->
  forall c st1 st2 ast1 ast2,
    ideal_same_obs c st1 st2 ast1 ast2 ->
    spec_same_obs (trans c) st1 st2 ast1 ast2.
Proof.
  unfold secure_compilation_bw, relative_secure, ideal_same_obs, spec_same_obs.
  intros trans H c st1 st2 ast1 ast2 Hsrc
         ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 H1 H2.
  specialize (H c). destruct H as [Td [To H] ].
  apply H in H1. destruct H1 as [oss1 [H1 H1'] ].
  apply H in H2. destruct H2 as [oss2 [H2 H2'] ].
  subst. f_equal. eapply Hsrc; eassumption.
Qed.
(* /HIDE *)
