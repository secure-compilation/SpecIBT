(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import ImpArrCall.
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

Ltac invert H := inversion H; subst; clear H.

Reserved Notation
  "p '|-' '<((' c , st , ast '))>' '-->^' os '<((' ct , stt , astt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

(* YH: To avoid complex errors from fixing the notation,
       I changed program to a tuple with its starting point. *)
Inductive seq_eval_small_step (p:prog * nat) :
    com -> state -> astate ->
    com -> state -> astate -> obs -> Prop :=
  | SSM_Asgn  : forall st ast e n x,
aeval st e = n ->
      p |- <((x := e, st, ast))> -->^[] <((skip, x !-> n; st, ast))>
  | SSM_Seq : forall c1 st ast os c1t stt astt c2,
  p|- <((c1, st, ast))>  -->^os <((c1t, stt, astt))>  ->
      p |- <(((c1;c2), st, ast))>  -->^os <(((c1t;c2), stt, astt))>
  | SSM_Seq_Skip : forall st ast c2,
      p |- <(((skip;c2), st, ast))>  -->^[] <((c2, st, ast))>
  | SSM_If : forall be ct cf st ast,
   p |- <((if be then ct else cf end, st, ast))> -->^[OBranch (beval st be)]
           <((match beval st be with
             | true => ct
         | false => cf end, st, ast))>
  | SSM_While : forall be c st ast,
  p |- <((while be do c end, st, ast))> -->^[]
<((if be then c; while be do c end else skip end, st, ast))>
  | SSM_ARead : forall x a ie st ast i,
   aeval st ie = i ->
      i < length (ast a) ->
      p |- <((x <- a[[ie]], st, ast))> -->^[OARead a i]
          <((skip, x !-> nth i (ast a) 0; st, ast))>
  | SSM_Write : forall a ie e st ast i n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      p |- <((a[ie] <- e, st, ast))> -->^[OAWrite a i]
           <((skip, st, a !-> upd i (ast a) n; ast))>
  | SSM_Call : forall e i c st ast,
      aeval st e = i + (snd p) ->
      nth_error (fst p) i = Some c ->
      p |- <((call e, st, ast))> -->^[OCall (i + snd p)] <((c, st, ast))>

  where "p |- <(( c , st , ast ))> -->^ os  <(( ct ,  stt , astt ))>" :=
    (seq_eval_small_step p c st ast ct stt astt os).

Reserved Notation
   "p '|-' '<((' c , st , ast '))>' '-->*^' os '<((' ct , stt , astt '))>'"
   (at level 40, c custom com at level 99, ct custom com at level 99,
    st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_seq (p:prog * nat) (c:com) (st:state) (ast:astate) :
    com -> state -> astate -> obs -> Prop :=
  | multi_seq_refl : p |- <((c, st, ast))> -->*^[] <((c, st, ast))>
  | multi_seq_trans (c':com) (st':state) (ast':astate)
                (c'':com) (st'':state) (ast'':astate)
                (os1 os2 : obs) :
      p |- <((c, st, ast))> -->^os1 <((c', st', ast'))> ->
      p |- <((c', st', ast'))> -->*^os2 <((c'', st'', ast''))> ->
      p |- <((c, st, ast))> -->*^(os1++os2) <((c'', st'', ast''))>

  where "p |- <(( c , st , ast ))> -->*^ os <(( ct ,  stt , astt ))>" :=
    (multi_seq p c st ast ct stt astt os).

Lemma multi_seq_combined_executions : forall p c st ast cm stm astm osm ct stt astt ost,
  p |- <((c, st, ast))> -->*^osm <((cm, stm, astm))> ->
  p |- <((cm, stm, astm))> -->*^ost <((ct, stt, astt))> ->
  p |- <((c, st, ast))> -->*^(osm++ost) <((ct, stt, astt))>.
Proof.
  intros p c st ast cm stm astm osm ct stt astt ost Hev1 Hev2.
  induction Hev1.
  - rewrite app_nil_l. apply Hev2.
  - rewrite <- app_assoc. eapply multi_seq_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma seq_small_step_obs_type : forall p c st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2,
  p |- <((c, st1, ast1))> -->^os1 <((ct1, stt1, astt1))> ->
  p |- <((c, st2, ast2))> -->^os2 <((ct2, stt2, astt2))> ->
  match os2 with
  | [] => os1 = []
  | OBranch _ :: os => exists b, os1 = OBranch b :: os
  | OARead _ _ :: os => exists a i, os1 = OARead a i :: os
  | OAWrite _ _ :: os => exists a i, os1 = OAWrite a i :: os
  | OCall _ :: os => exists i, os1 = OCall i :: os
  | OForceCall :: os => os1 = OForceCall :: os
  end.
Proof.
  intros p; induction c; intros st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2 H1 H2;
  inversion H1; inversion H2; subst; try eauto.
  + eapply IHc1; eauto.
  + inversion H9.
  + inversion H17.
Qed.

Corollary seq_small_step_obs_length : forall p c st1 ast1 stt1 astt1 ct1 os1 ct2 st2 ast2 stt2 astt2 os2,
  p |- <((c, st1, ast1))> -->^os1 <((ct1, stt1, astt1))> ->
p |- <((c, st2, ast2))> -->^os2 <((ct2, stt2, astt2))> ->
  length os1 = length os2.
Proof.
  intros. eapply seq_small_step_obs_type in H; [|now apply H0].
  destruct os1; subst; [now auto|].
  destruct o.
  2, 3 : now (do 2 destruct H); subst.
  all : now destruct H; subst.
Qed.

(** Small-step speculative semantics *)

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

(* YH: To avoid complex errors from fixing the notation,
       I changed program to a tuple with its starting point. *)
Inductive spec_eval_small_step (p:prog * nat) :
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | SpecSM_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      p |- <((x := e, st, ast, b))> -->_[]^^[] <((skip, x !-> n; st, ast, b))>
  | SpecSM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      p |- <((c1, st, ast, b))>  -->_ds^^os <((c1t, stt, astt, bt))>  ->
      p |- <(((c1;c2), st, ast, b))>  -->_ds^^os <(((c1t;c2), stt, astt, bt))>
  | SpecSM_Seq_Skip : forall st ast b c2,
      p |- <(((skip;c2), st, ast, b))>  -->_[]^^[] <((c2, st, ast, b))>
  | SpecSM_If : forall be ct cf st ast b c' b',
      b' = beval st be ->
      c' = (if b' then ct else cf) ->
      p |- <((if be then ct else cf end, st, ast, b))> -->_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | SpecSM_If_F : forall be ct cf st ast b c' b',
      b' = beval st be ->
      c' = (if b' then cf else ct) ->
      p |- <((if be then ct else cf end, st, ast, b))> -->_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | SpecSM_While : forall be c st ast b,
      p |- <((while be do c end, st, ast, b))> -->_[]^^[]
           <((if be then c; while be do c end else skip end, st, ast, b))>
  | SpecSM_ARead : forall x a ie st ast b i,
      aeval st ie = i ->
      i < length (ast a) ->
      p |- <((x <- a[[ie]], st, ast, b))> -->_[DStep]^^[OARead a i]
           <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | SpecSM_ARead_U : forall x a ie st ast i a' i',
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      p |- <((x <- a[[ie]], st, ast, true))> -->_[DLoad a' i']^^[OARead a i]
           <((skip, x !-> nth i' (ast a') 0; st, ast, true))>
  | SpecSM_Write : forall a ie e st ast b i n,
      aeval st e = n ->
      aeval st ie = i ->
      i < length (ast a) ->
      p |- <((a[ie] <- e, st, ast, b))> -->_[DStep]^^[OAWrite a i]
           <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | SpecSM_Write_U : forall a ie e st ast i n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      p |- <((a[ie] <- e, st, ast, true))> -->_[DStore a' i']^^[OAWrite a i]
           <((skip, st, a' !-> upd i' (ast a') n; ast, true))>
  | SpecSM_Call : forall e i c st ast b,
      aeval st e = i + (snd p) ->
      nth_error (fst p) i = Some c ->
      p |- <((call e, st, ast, b))> -->_[DStep]^^[OCall (i + snd p)] <((c, st, ast, b))>
  | SpecSM_Call_F : forall e i j c st ast b,
      aeval st e = i + (snd p) ->
      i <> j ->
      nth_error (fst p) j = Some c ->
      p |- <((call e, st, ast, b))> -->_[DForceCall (j + snd p)]^^[OForceCall] <((c, st, ast, true))>

  where "p |- <(( c , st , ast , b ))> -->_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (spec_eval_small_step p c st ast b ct stt astt bt ds os).

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_spec (p:prog * nat) (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_spec_refl : p |- <((c, st, ast, b))> -->*_[]^^[] <((c, st, ast, b))>
  | multi_spec_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      p |- <((c, st, ast, b))> -->_ds1^^os1 <((c', st', ast', b'))> ->
      p |- <((c', st', ast', b'))> -->*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      p |- <((c, st, ast, b))> -->*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

    where "p |- <(( c , st , ast , b ))> -->*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_spec p c st ast b ct stt astt bt ds os).

Lemma multi_spec_trans_nil_l p c st ast b c' st' ast' b' ct stt astt bt ds os :
  p |- <((c, st, ast, b))> -->_[]^^[] <((c', st', ast', b'))> ->
  p |- <((c', st', ast', b'))> -->*_ds^^os <((ct, stt, astt, bt))> ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_spec_trans; eassumption.
Qed.

Lemma multi_spec_trans_nil_r p c st ast b c' st' ast' b' ct stt astt bt ds os :
  p |- <((c, st, ast, b))> -->_ds^^os <((c', st', ast', b'))> ->
  p |- <((c', st', ast', b'))> -->*_[]^^[] <((ct, stt, astt, bt))> ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_spec_trans; eassumption.
Qed.

Lemma multi_spec_combined_executions : forall p c st ast cm stm astm osm ct stt astt ost ds ds' b b' b'',
  p |- <((c, st, ast, b))> -->*_ds^^osm <((cm, stm, astm, b'))> ->
  p |- <((cm, stm, astm, b'))> -->*_ds'^^ost <((ct, stt, astt, b''))> ->
  p |- <((c, st, ast, b))> -->*_(ds++ds')^^(osm++ost) <((ct, stt, astt, b''))>.
Proof.
  intros.
  induction H.
  - rewrite app_nil_l. apply H0.
  - rewrite <- !app_assoc. eapply multi_spec_trans.
    + eapply H.
    + apply IHmulti_spec. apply H0.
Qed.

Lemma multi_spec_add_snd_com : forall p c st ast ct stt astt ds os c2 b bt,
  p |- <((c, st, ast, b))> -->*_ds^^os <((ct, stt, astt, bt))> ->
  p |- <((c;c2, st, ast, b))> -->*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma multi_spec_seq : forall p c1 c2 cm st ast b stm astm bm ds os,
  p |- <((c1; c2, st, ast, b))> -->*_ds^^os <((cm, stm, astm, bm))> ->
  (exists st' ast' b' ds1 ds2 os1 os2,
  os = os1 ++ os2 /\ ds = ds1 ++ ds2 /\
  p |- <((c1, st, ast, b))> -->*_ds1^^os1 <((skip, st', ast', b'))> /\
  p |- <((c2, st', ast', b'))> -->*_ds2^^os2 <((cm, stm, astm, bm))>) \/
  (exists c', cm = <{{ c'; c2 }}> /\
   p |- <((c1, st, ast, b))> -->*_ds^^os <((c', stm, astm, bm))>).
Proof.
  intros. remember <{{ c1; c2 }}> as c. revert c1 c2 Heqc.
  induction H; intros; subst.
  { right. repeat eexists. constructor. }
  invert H.
  + edestruct IHmulti_spec; [reflexivity|..].
    - do 8 destruct H. destruct H1, H2. subst. clear IHmulti_spec.
      left. rewrite !app_assoc. repeat eexists; [econstructor|]; eassumption.
    - do 2 destruct H. subst. clear IHmulti_spec.
      right. repeat eexists. econstructor; eassumption.
  + left. repeat eexists; [constructor|eassumption].
Qed.

Lemma multi_seq_seq : forall p c1 c2 cm st ast stm astm os,
  p |- <((c1; c2, st, ast))> -->*^os <((cm, stm, astm))> ->
  (exists st' ast' os1 os2,
  os = os1 ++ os2 /\
  p |- <((c1, st, ast))> -->*^os1 <((skip, st', ast'))> /\
  p |- <((c2, st', ast'))> -->*^os2 <((cm, stm, astm))>) \/
  (exists c', cm = <{{ c'; c2 }}> /\
  p |- <((c1, st, ast))> -->*^os <((c', stm, astm))>).
Proof.
  intros. remember <{{ c1; c2 }}> as c. revert c1 c2 Heqc.
  induction H; intros; subst.
  { right. repeat eexists. constructor. }
  invert H.
  + edestruct IHmulti_seq; [reflexivity|..].
    - do 5 destruct H. destruct H1. subst. clear IHmulti_seq.
      left. rewrite !app_assoc. repeat eexists; [econstructor|]; eassumption.
    - do 2 destruct H. subst. clear IHmulti_seq.
      right. repeat eexists. econstructor; eassumption.
  + left. repeat eexists; [constructor|eassumption].
Qed.

Lemma multi_spec_seq_assoc p c1 c2 c3 st ast b c' st' ast' b' ds os :
  p |- <(((c1; c2); c3, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists c'', 
  p |- <((c1; c2; c3, st, ast, b))> -->*_ds^^os <((c'', st', ast', b'))> /\ (c' = <{{ skip }}> -> c'' = <{{ skip }}>).
Proof.
  intros. apply multi_spec_seq in H. destruct H.
  + do 8 destruct H. destruct H0, H1. subst. apply multi_spec_seq in H1. destruct H1.
    - do 8 destruct H. destruct H0, H1. subst. exists c'. split; [|tauto].
      rewrite <- !app_assoc. eapply multi_spec_combined_executions; [apply multi_spec_add_snd_com, H1|].
      eapply multi_spec_trans_nil_l; [apply SpecSM_Seq_Skip|]. eapply multi_spec_combined_executions; [apply multi_spec_add_snd_com, H3|].
      eapply multi_spec_trans_nil_l; [apply SpecSM_Seq_Skip|apply H2].
    - destruct H as (c''&abs&_). discriminate abs.
  + destruct H as (c''&->&H). apply multi_spec_seq in H. destruct H.
    - do 8 destruct H. destruct H0, H1. subst. exists <{{ c''; c3 }}>.
      split; [|discriminate]. eapply multi_spec_combined_executions; [apply multi_spec_add_snd_com, H1|].
      eapply multi_spec_trans_nil_l; [apply SpecSM_Seq_Skip|]. apply multi_spec_add_snd_com, H2.
    - destruct H as (c'&->&H). exists <{{ c'; c2; c3 }}>. split; [|discriminate].
      apply multi_spec_add_snd_com, H.
Qed.

(** * Definition of Relative Secure *)

Definition seq_same_obs p c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2 c1 c2,
    p |- <((c, st1, ast1))> -->*^os1 <((c1, stt1, astt1))> ->
    p |- <((c, st2, ast2))> -->*^os2 <((c2, stt2, astt2))> ->
    (prefix os1 os2) \/ (prefix os2 os1). 

Definition spec_same_obs p c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    p |- <((c, st1, ast1, false))> -->*_ds^^os1 <((c1, stt1, astt1, bt1))> ->
    p |- <((c, st2, ast2, false))> -->*_ds^^os2 <((c2, stt2, astt2, bt2))> ->
    os1 = os2. 

Definition relative_secure (p:prog * nat) (trans : com -> com)
    (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop :=
  seq_same_obs p c st1 st2 ast1 ast2 ->
  spec_same_obs p (trans c) st1 st2 ast1 ast2.
  
(** * Ultimate Speculative Load Hardening *)

Definition is_empty {A} (l:list A) := match l with [] => true | _ => false end.

Lemma is_empty_app {A} : forall (l l' : list A),
  is_empty (l ++ l') = is_empty l && is_empty l'.
Proof.
  now destruct l.
Qed.

Fixpoint vars_aexp (a:aexp) : list string :=
  match a with
  | ANum n => []
  | AId x => [x]
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ be ? a1 : a2 }> => vars_bexp be ++ vars_aexp a1 ++ vars_aexp a2
  end
with vars_bexp (a:bexp) : list string :=
  match a with
  | <{ true }> | <{ false }> => []
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ ~b }> => vars_bexp b
  | <{ b1 && b2 }> => vars_bexp b1 ++ vars_bexp b2
  end.

Fixpoint ultimate_slh (c:com) :=
  (match c with
   | <{{skip}}> => <{{skip}}>
   | <{{x := e}}> => <{{x := e}}>
   | <{{c1; c2}}> => <{{ultimate_slh c1; ultimate_slh c2}}>
   | <{{if be then c1 else c2 end}}> =>
       let be' := if is_empty (vars_bexp be) then be (* optimized *)
                                             else <{{"b" = 0 && be}}> in
         <{{if be' then "b" := be' ? "b" : 1; ultimate_slh c1
          else "b" := be' ? 1 : "b"; ultimate_slh c2 end}}>
   | <{{while be do c end}}> =>
       let be' := if is_empty (vars_bexp be) then be (* optimized *)
                                             else <{{"b" = 0 && be}}> in
         <{{while be' do "b" := be' ? "b" : 1; ultimate_slh c end;
           "b" := be' ? 1 : "b"}}>
   | <{{x <- a[[i]]}}> =>
       let i' := if is_empty (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                           else <{{("b" = 1) ? 0 : i}}> in
         <{{ x <- a[[i']]}}>
   | <{{a[i] <- e}}> =>
       let i' := if is_empty (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                           else <{{("b" = 1) ? 0 : i}}> in
        <{{ a[i'] <- e}}> (* <- Doing nothing here in the is_empty (vars_aexp i) case okay for Spectre v1,
                   but problematic for return address or code pointer overwrites *)
   | <{{call e}}> =>
       let e' := if is_empty (vars_aexp e) then e 
                                           else <{{("b" = 1) ? 0 : e}}> in
        <{{"callee" := e'; call e'}}>
  end)%string.

(* Not using these anymore:

   Definition add_index {a:Type} (xs:list a) : list (nat * a) :=
  combine (seq 0 (length xs)) xs.

Definition ultimate_slh_prog (p:prog) :=
  map (fun p =>
    let '(i,c) := p in
        <{{"b" := ("callee" = ANum i)? "b" : 1; ultimate_slh c}}>
      ) (add_index p). 
*)

(* Generalization of ultimate_slh_prog *)

(* start from any index, not just 0 (this will help us prove things about uslh_prog on p vs a::p) *)
Definition add_index_gen {a:Type} (xs:list a) (start: nat) : list (nat * a) :=
  combine (seq start (length xs)) xs.

(* this is uslh_prog except with the use of add_index_nth and adding an extra start parameter accordingly *)
Definition ultimate_slh_prog_gen (p:prog) (start: nat) :=
  map (fun p =>
    let '(i,c) := p in
    <{{"b" := ("callee" = ANum i)? "b" : 1; ultimate_slh c}}>) (add_index_gen p start).

(* this is the special case that was ultimate_slh_prog previously *)
Definition ultimate_slh_prog_zero (p: prog) := ultimate_slh_prog_gen p 0.

(** The masking USLH does for indices requires that our arrays are nonempty. *)

Definition nonempty_arrs (ast : astate) :Prop :=
  forall a, 0 < length (ast a).

(** * Ideal small-step evaluation *)

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step (p:prog * nat):
    com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      p |- <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2,
      p |- <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      p |- <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall st ast b c2,
      p |- <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall be ct cf st ast b c' b',
      b' = (is_empty (vars_bexp be) || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      p |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | ISM_If_F : forall be ct cf st ast b c' b',
      b' = (is_empty (vars_bexp be) || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      p |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | ISM_While : forall be c st ast b,
      p |- <((while be do c end, st, ast, b))> -->i_[]^^[]
           <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall x a ie st ast (b :bool) i,
      (if negb (is_empty (vars_aexp ie)) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      p |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
           <((skip, x !-> nth i (ast a) 0; st, ast, b))>
  | ISM_ARead_U : forall x a ie st ast i a' i',
      aeval st ie = i ->
      is_empty (vars_aexp ie) = true ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      p |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i]
           <((skip, x !-> nth i' (ast a') 0; st, ast, true))>
  | ISM_Write : forall a ie e st ast (b :bool) i n,
      aeval st e = n ->
      (if negb (is_empty (vars_aexp ie)) && b then 0 else (aeval st ie)) = i ->
      i < length (ast a) ->
      p |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i]
           <((skip, st, a !-> upd i (ast a) n; ast, b))>
  | ISM_Write_U : forall a ie e st ast i n a' i',
      aeval st e = n ->
      is_empty (vars_aexp ie) = true ->
      aeval st ie = i ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      p |- <((a[ie] <- e, st, ast, true))> -->i_[DStore a' i']^^[OAWrite a i]
           <((skip, st, a' !-> upd i' (ast a') n; ast, true))>
  | ISM_Call : forall e i c st ast b,
      (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i + (snd p) ->
      nth_error (fst p) i = Some c ->
      p |- <((call e, st, ast, b))> -->i_[DStep]^^[OCall (i + snd p)] <((c, st, ast, b))>
  | ISM_Call_F : forall e i j c st ast b,
      (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i + (snd p) ->
      i <> j ->
      nth_error (fst p) j = Some c ->
      p |- <((call e, st, ast, b))> -->i_[DForceCall (j + snd p)]^^[OForceCall] <((c, st, ast, true))>

    where "p |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step p c st ast b ct stt astt bt ds os).

(* HIDE: This one now has again `_U` cases because of out-of-bounds array
   accesses at constant indices. Since the array sizes are also statically
   known, we could easily reject such programs statically.  *)

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (p:prog * nat) (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : p |- <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      p |-<((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      p |-<((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      p |-<((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

          where "p |- <(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal p c st ast b ct stt astt bt ds os).

Lemma multi_ideal_trans_nil_l p c st ast b c' st' ast' b' ct stt astt bt ds os :
  p |- <((c, st, ast, b))> -->i_[]^^[] <((c', st', ast', b'))> ->
  p |- <((c', st', ast', b'))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  p |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r p c st ast b c' st' ast' b' ct stt astt bt ds os :
  p |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  p |- <((c', st', ast', b'))> -->i*_[]^^[] <((ct, stt, astt, bt))> ->
  p |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Definition ideal_same_obs p c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    p |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((c1, stt1, astt1, bt1))> ->
    p |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((c2, stt2, astt2, bt2))> ->
    os1 = os2.

Lemma multi_ideal_combined_executions :
  forall p c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    p |- <((c, st, ast, b))> -->i*_ds^^osm <((cm, stm, astm, bm))> ->
    p |- <((cm, stm, astm, bm))> -->i*_dsm^^ost <((ct, stt, astt, bt))> ->
    p |- <((c, st, ast, b))> -->i*_(ds++dsm)^^(osm++ost) <((ct, stt, astt, bt))>.
Proof.
  intros p c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma multi_ideal_add_snd_com : forall p c st ast ct stt astt ds os c2 b bt,
  p |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  p |- <((c;c2, st, ast, b))> -->i*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

(** * Lemmas for the proof of [ideal_eval_relative_secure] *)

Lemma ideal_eval_small_step_spec_bit_monotonic : forall p c st ast ds ct stt astt bt os,
  p |- <((c, st, ast, true))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros p c st ast ds ct stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall p c st ast ds ct stt astt bt os,
  p |- <((c, st, ast, true))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros p c st ast ds ct stt astt bt os Heval. remember true as b eqn:Eqb.
  induction Heval; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma ideal_eval_final_spec_bit_false_one_step : forall p c st ast ds stt astt os ct,
  p |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros. remember false as b. rewrite Heqb in H at 2. remember false as b'.
  rewrite Heqb' in Heqb.
  revert Heqb Heqb' d H0.
  induction H; intros; (try discriminate); subst; try (now inversion H0).
  + apply IHideal_eval_small_step; tauto.
  + now invert H1.
  + now invert H1.
  + now invert H2.
  + now invert H1.
Qed.

Lemma ideal_eval_final_spec_bit_false : forall p c st ast ds stt astt os ct,
  p |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros. remember false as b. rewrite Heqb in H at 2. remember false as b'.
  rewrite Heqb' in Heqb. revert Heqb Heqb' d H0.
  induction H; intros; subst.
  + now apply in_nil in H0.
  + destruct b'. { now apply multi_ideal_spec_bit_monotonic in H0. }
    apply in_app_iff in H1. destruct H1.
    - eapply ideal_eval_final_spec_bit_false_one_step in H; eassumption.
    - apply IHmulti_ideal; tauto.
Qed.

Lemma ideal_eval_small_step_spec_needs_force : forall p c st ast ds ct stt astt os,
  p |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, true))> ->
      ds = [DForce] \/ exists j, ds = [DForceCall j].
Proof.
  intros p c st ast ds ct stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl in *; try discriminate;
  try (right; exists (j + (snd p))); auto.
Qed.

Lemma multi_ideal_spec_needs_force : forall p c st ast ds ct stt astt os,
  p |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, true))> ->
  In DForce ds \/ exists j, In (DForceCall j) ds.
Proof.
  intros p c st ast ds ct stt astt os Hev.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; subst; simpl in *; try discriminate.
  destruct b' eqn:Eqb'.
  - apply ideal_eval_small_step_spec_needs_force in H.
    destruct H as [ H1 | H2 ]; subst; simpl; try (left; tauto); 
    try (right; tauto). destruct H2 as [j H2]. right. exists j.
    apply in_or_app; left. rewrite H2. simpl. left. auto.
  - specialize (IHHev Logic.eq_refl Logic.eq_refl). 
    destruct IHHev as [ H1 | H2 ].
    + left. apply in_or_app. right. eassumption.
    + right. destruct H2 as [j H2]. exists j. apply in_or_app. 
      right. eassumption.
Qed.

Lemma ideal_eval_spec_bit_deterministic :
  forall p c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    p |- <(( c, st1, ast1, b ))> -->i*_ ds ^^ os1 <(( c1, stt1, astt1, bt1 ))> ->
    p |- <(( c, st2, ast2, b ))> -->i*_ ds ^^ os2 <(( c2, stt2, astt2, bt2 ))> ->
    bt1 = bt2.
Proof.
  intros p c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2 Hev1 Hev2.
  destruct b.
  - apply multi_ideal_spec_bit_monotonic in Hev1, Hev2. congruence.
  - destruct bt1, bt2; try reflexivity.
    + apply multi_ideal_spec_needs_force in Hev1.
      destruct Hev1 as [HevDF | HevDFC].
      * now eapply ideal_eval_final_spec_bit_false in Hev2; [|eassumption].
      * destruct HevDFC as [j HevDFC].
        now eapply ideal_eval_final_spec_bit_false in Hev2; [|eassumption].
    + apply multi_ideal_spec_needs_force in Hev2.
      destruct Hev2 as [HevDF | HevDFC].
      * now eapply ideal_eval_final_spec_bit_false in Hev1; [|eassumption].
      * destruct HevDFC as [j HevDFC].
        now eapply ideal_eval_final_spec_bit_false in Hev1; [|eassumption].
Qed.

Lemma ideal_eval_small_step_obs_length : forall p c st ast b ds ct stt astt bt os,
  p |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof.
  intros p c st ast b ds ct stt astt bt os Hev. induction Hev; simpl; auto.
Qed.

Lemma multi_ideal_obs_length : forall p c st ast b ds ct stt astt bt os,
  p |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof.
  intros p c st ast b ds ct stt astt bt os Hev. induction Hev; simpl; auto.
  do 2 rewrite app_length. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_eval_small_step_final_spec_bit_false : forall p c st ast ds ct stt astt os,
  p |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros p c st ast ds ct stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; subst; intros d Hin; simpl in *; try destruct Hin;
  try discriminate; try contradiction; auto.
Qed.

Lemma multi_ideal_final_spec_bit_false : forall p c st ast ds ct stt astt os,
  p |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, false))> ->
  (forall d, In d ds -> d = DStep).
Proof.
  intros p c st ast ds ct stt astt os Hev. remember false as b eqn:Eqb.
  induction Hev; intros d Hin; simpl in *; subst; try contradiction.
  destruct b' eqn:Eqb'.
  - apply multi_ideal_spec_bit_monotonic in Hev. discriminate.
  - apply in_app_or in Hin as [Hin | Hin].
    + destruct b eqn:Eqb.
      * apply ideal_eval_small_step_spec_bit_monotonic in H. discriminate.
      * eapply ideal_eval_small_step_final_spec_bit_false in Hin; eauto.
    + apply IHHev; auto.
Qed.

Lemma ideal_eval_small_step_no_spec : forall p c st ast ds ct stt astt bt os,
  p |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, bt))> ->
    (forall d, In d ds -> d = DStep) ->
    p |- <((c, st, ast ))> -->^os <((ct, stt, astt))>.
Proof.
  intros p c st ast ds ct stt astt bt os Hev.
  remember false as b eqn:Eqb. induction Hev; intros Hds;
  try (now subst; rewrite ?orb_true_r, ?andb_false_r in *; econstructor; eauto).
  + specialize (Hds DForce). discriminate Hds. now left.
  + specialize (Hds (DLoad a' i')). discriminate Hds. now left.
  + specialize (Hds (DStore a' i')). discriminate Hds. now left.
  + specialize (Hds (DForceCall (j + snd p))). discriminate Hds. now left.
Qed.

Lemma multi_ideal_no_spec : forall p c st ast ds ct stt astt bt os,
    p |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
    (forall d, In d ds -> d = DStep) ->
    p |- <((c, st, ast ))> -->*^os <((ct, stt, astt))>.
Proof.
  intros p c st ast ds ct stt astt bt os Hev.
  remember false as b eqn:Eqb. induction Hev; intros Hds; subst.
  - apply multi_seq_refl.
  - assert (L1: forall d, In d ds1 -> d = DStep).
    { intros d Hd. apply Hds. apply in_or_app. auto. }
    assert (L2: forall d, In d ds2 -> d = DStep).
    { intros d Hd. apply Hds. apply in_or_app. auto. }
    destruct b' eqn:Eqb'.
    + apply ideal_eval_small_step_spec_needs_force in H.
      destruct H as [HDF | HDFC].
      * subst. simpl in L1. 
        specialize (L1 DForce (or_introl (Logic.eq_refl DForce))). 
        discriminate L1.
      * destruct HDFC as [j HDFC]. subst. simpl in L1.
        specialize (L1 (DForceCall j) (or_introl (Logic.eq_refl (DForceCall j)))).
        discriminate L1.
    + apply ideal_eval_small_step_no_spec in H; auto.
      eapply multi_seq_trans.
      * eapply H.
      * apply IHHev; auto.
Qed.

Lemma seq_to_ideal : forall p c st ast ct stt astt os,
  p |- <((c, st, ast ))> -->^os <((ct, stt, astt))> ->
  p |- <((c, st, ast, false))> -->i_(repeat DStep (length os))^^os <((ct, stt, astt, false))>.
Proof.
  intros.
  induction H; try now (constructor; rewrite ?orb_true_r, ?andb_false_r).
Qed. 

Lemma seq_small_step_if_total : forall p c be ct cf st ast,
  c = <{{if be then ct else cf end}}> ->
  exists c' stt astt os,
  p |- <((c, st, ast))> -->^os <((c', stt, astt))> /\ os <> [].
Proof.
  intros c be ct cf st ast Heq. subst.
  repeat econstructor; subst.
  - econstructor.
  - intros Contra. inversion Contra.
Qed.

Lemma seq_small_step_to_multi_seq : forall p c st ast ct stt astt os,
  p |- <((c, st, ast))> -->^os <((ct, stt, astt))> ->
  p |- <((c, st, ast))> -->*^os <((ct, stt, astt))>.
Proof.
  intros p c st ast ct stt astt os Hev.
  rewrite <- app_nil_r. eapply multi_seq_trans; eauto.
  apply multi_seq_refl.
Qed.

Lemma seq_same_obs_com_if (p:prog * nat) : forall be ct cf st1 st2 ast1 ast2,
  seq_same_obs p <{{ if be then ct else cf end }}> st1 st2 ast1 ast2 ->
  beval st1 be = beval st2 be.
Proof.
  intros be ct cf st1 st2 ast1 ast2 Hsec.
  remember <{{if be then ct else cf end}}> as c eqn:Eqc.
  (* assert (L1: exists p c' stt astt os, p |- <((c, st1, ast1))> -->^os <((c', stt, astt))> /\ os <> []). *)
  assert (L1: exists c' stt astt os, p |- <((c, st1, ast1))> -->^os <((c', stt, astt))> /\ os <> []).
  { eapply seq_small_step_if_total; eauto. }   
  assert (L2: exists c' stt astt os, p |- <((c, st2, ast2))> -->^os <((c', stt, astt))> /\ os <> []).
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
      destruct Hpre as [Hpre | Hpre]; simpl in Hpre;
      apply prefix_heads in Hpre; inversion Hpre; auto.
Qed.

Lemma multi_seq_add_snd_com : forall p c st ast ct stt astt os c2,
  p |- <((c, st, ast))> -->*^os <((ct, stt, astt))> ->
  p |- <((c;c2, st, ast))> -->*^os <((ct;c2, stt, astt))>.
Proof.
  intros p c st ast ct stt astt os c2 Hev.
  induction Hev.
  - apply multi_seq_refl.
  - eapply multi_seq_trans.
    + econstructor. eauto.
    + apply IHHev.
Qed.

Lemma seq_same_obs_com_seq (p:prog * nat) : forall c1 c2 st1 st2 ast1 ast2,
  seq_same_obs p <{{ c1; c2 }}> st1 st2 ast1 ast2 ->
  seq_same_obs p c1 st1 st2 ast1 ast2.
Proof.
  intros c1 c2 st1 st2 ast1 ast2 Hsec. unfold seq_same_obs.
  intros stt1 stt2 astt1 astt2 os1 os2 ct1 ct2 Hev1 Hev2.
  eapply multi_seq_add_snd_com in Hev1, Hev2. eapply Hsec in Hev2; eauto.
Qed.

Lemma ideal_one_step_force_obs (p:prog * nat) :
  forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2,
  seq_same_obs p c st1 st2 ast1 ast2 ->
    p |- <((c, st1, ast1, false))> -->i_[DForce]^^os1 <((ct, stt1, astt1, true))> ->
    p |- <((c, st2, ast2, false))> -->i_[DForce]^^os2 <((ct, stt2, astt2, true))> ->
    os1 = os2.
Proof.
  intros c ct st ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 Hobs Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ast2;
  generalize dependent st2.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  remember [DForce] as d. revert Heqd.
  induction Hev1; intros Heqd st2 ast2 Hobs stt2 astt2 os2 Hev2;
  try(inversion Hev2; subst; auto); try discriminate.
  - eapply IHHev1; eauto. eapply seq_same_obs_com_seq; eauto.
  - apply seq_same_obs_com_if in Hobs. rewrite Hobs. reflexivity.
Qed.

Lemma ideal_one_step_forcecall_obs (p:prog * nat) :
  forall c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 j,
  seq_same_obs p c st1 st2 ast1 ast2 ->
    p |- <((c, st1, ast1, false))> -->i_[(DForceCall j)]^^os1 <((ct, stt1, astt1, true))> ->
    p |- <((c, st2, ast2, false))> -->i_[(DForceCall j)]^^os2 <((ct, stt2, astt2, true))> ->
    os1 = os2.
Proof.
  intros c ct st1 ast1 stt1 astt1 os1 st2 ast2 stt2 astt2 os2 j Hobs Hev1.
  generalize dependent os2; generalize dependent astt2;
  generalize dependent stt2; generalize dependent ast2;
  generalize dependent st2.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  remember [(DForceCall j)] as d. revert Heqd. revert j.
  induction Hev1; try discriminate; intros.
  - apply seq_same_obs_com_seq in Hobs. destruct IHHev1 with (j:=j) (st2:=st2) 
    (ast2:=ast2) (stt2:=stt2) (astt2:=astt2) (os2:=os2); auto. inversion H; subst; auto.
    discriminate.
  - inversion H2; auto.
Qed.

(** * Relative Security of Ultimate Speculative Load Hardening *)

(** As in SpecCT and Spectre Declassified, an important step in the proof is
    relating the speculative semantics of the hardened program with the ideal
    semantics, by means of a backwards compiler correctness (BCC) result. *)

Lemma ideal_unused_overwrite_one_step (p:prog) (s: nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  (p, s) |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  (p, s) |- <((c, X !-> n; st, ast, b))> -->i_ds^^os <((c', X !-> n; st', ast', b'))> /\ unused X c'.
Proof.
  intros. remember (unused_prog X p) as unused_p. induction H1.
  - invert H0. repeat econstructor. rewrite t_update_permute; [constructor|assumption].
    now apply aeval_unused_update.
  - invert H0. eapply IHideal_eval_small_step in H2. destruct H2.
    repeat econstructor; assumption.
  - split; [|now invert H0]. apply ISM_Seq_Skip.
  - destruct H0. destruct H3 as [H4 H5]. split; [|now destruct b'; subst]. constructor; [|tauto].
    now rewrite beval_unused_update.
  - destruct H0. destruct H3 as [H4 H5]. split; [|now destruct b'; subst]. constructor; [|tauto].
    now rewrite beval_unused_update.
  - invert H0. now repeat constructor.
  - invert H0. repeat constructor. rewrite t_update_permute; [constructor|assumption].
    { now rewrite aeval_unused_update. } assumption.
  - invert H0. rewrite t_update_permute; [|tauto]. 
    repeat constructor; [now rewrite aeval_unused_update|assumption..].
  - invert H0. repeat constructor; [now rewrite aeval_unused_update..|assumption].
  - invert H0. repeat constructor. 1, 3 : now rewrite aeval_unused_update. all:assumption.
  - split.
    + simpl in *; try (apply ISM_Call); try (rewrite aeval_unused_update); auto.
    + invert Hequnused_p; clear H3. unfold unused_prog in H. 
      rewrite Forall_forall in H. apply H with (x:=c). apply nth_error_In in H2; auto.
  - split.
    + apply ISM_Call_F with (i:=i); auto. rewrite aeval_unused_update; auto.
    + simpl in *. rewrite Hequnused_p in H. unfold unused_prog in H.
      rewrite Forall_forall in H. apply H with (x:=c). apply nth_error_In in H3; auto.
Qed.
  
Lemma ideal_unused_overwrite (p:prog) (s: nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  (p, s) |- <((c, st, ast, b))> -->i*_ds^^os <((c', st', ast', b'))> ->
  (p, s) |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((c', X !-> n; st', ast', b'))>.
Proof.
  intros. induction H1; [constructor|].
  eapply ideal_unused_overwrite_one_step in H1; [|eassumption|eassumption]. destruct H1.
  econstructor; [eassumption|tauto].
Qed.

Lemma ideal_unused_update (p:prog) (s: nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  (p, s) |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((c', X !-> n; st', ast', b'))> ->
  (p, s) |- <((c, st, ast, b))> -->i*_ds^^os <((c', X !-> st X; st', ast', b'))>.
Proof.
  intros. rewrite <- (t_update_same _ st X) at 1.
  eapply ideal_unused_overwrite with (X:=X) (n:=(st X)) in H1; [ |assumption|assumption].
  now rewrite !t_update_shadow in H1.
Qed.

Lemma spec_unused_overwrite_one_step (p:prog * nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X (fst p) ->
  unused X c ->
  p |- <((c, st, ast, b))> -->_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->_ds^^os <((c', X !-> n; st', ast', b'))> /\ unused X c'.
Proof.
  intros. remember (unused_prog X (fst p)) as unused_p. induction H1.
  - invert H0. repeat econstructor. rewrite t_update_permute; [constructor|assumption].
    now apply aeval_unused_update.
  - invert H0. eapply IHspec_eval_small_step in H2. destruct H2.
    repeat econstructor; assumption.
  - split; [|now invert H0]. apply SpecSM_Seq_Skip.
  - destruct H0. destruct H3 as [H4 H5]. split; [|now destruct b'; subst]. constructor; [|tauto].
    now rewrite beval_unused_update.
  - destruct H0. destruct H3 as [H4 H5]. split; [|now destruct b'; subst]. constructor; [|tauto].
    now rewrite beval_unused_update.
  - invert H0. now repeat constructor.
  - invert H0. repeat constructor. rewrite t_update_permute; [constructor|assumption].
    { now rewrite aeval_unused_update. } assumption.
  - invert H0. repeat constructor. rewrite t_update_permute; [|tauto]. 
    now constructor; [apply aeval_unused_update|..].
  - invert H0. now repeat constructor; [apply aeval_unused_update..|].
  - invert H0. now repeat constructor; [apply aeval_unused_update..| |].
  - split.
    + simpl in *; try (apply SpecSM_Call); try (rewrite aeval_unused_update); auto.
    + invert Hequnused_p; clear H3. unfold unused_prog in H. 
      rewrite Forall_forall in H. apply H with (x:=c). apply nth_error_In in H2; auto.
  - split.
    + apply SpecSM_Call_F with (i:=i); auto. rewrite aeval_unused_update; auto.
    + simpl in *. rewrite Hequnused_p in H. unfold unused_prog in H.
      rewrite Forall_forall in H. apply H with (x:=c). apply nth_error_In in H3; auto.
Qed.

Lemma spec_unused_overwrite (p:prog * nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused X c ->
  unused_prog X (fst p) ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->*_ds^^os <((c', X !-> n; st', ast', b'))>.
Proof.
  intros. induction H1; [constructor|].
  eapply spec_unused_overwrite_one_step in H1; [|eassumption|eassumption]. destruct H1.
  econstructor; [eassumption|tauto].
Qed.

Lemma spec_unused_update (p:prog * nat) : forall st ast b ds c c' st' ast' b' os X n,
  unused X c ->
  unused_prog X (fst p) ->
  p |- <((c, X !-> n; st, ast, b))> -->*_ds^^os <((c', X !-> n; st', ast', b'))> ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((c', X !-> st X; st', ast', b'))>.
Proof.
  intros. rewrite <- (t_update_same _ st X) at 1.
  eapply spec_unused_overwrite with (X:=X) (n:=(st X)) in H1; [|assumption|assumption].
  now rewrite !t_update_shadow in H1.
Qed.

Lemma upd_length : forall l i a,
  length (upd i l a) = length l.
Proof.
  induction l; destruct i; auto.
  intros. simpl. now f_equal.
Qed.

Lemma spec_eval_preserves_nonempty_arrs (p:prog * nat) : forall c c' st ast b ds st' ast' b' os,
  nonempty_arrs ast ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  nonempty_arrs ast'.
Proof.
  unfold nonempty_arrs.
  intros. generalize dependent a. induction H0; eauto; subst.
  apply IHmulti_spec. clear IHmulti_spec H1.
  induction H0; eauto; subst.
  2:clear H2 a. 1:rename a into a'.
  all: intros; destruct (String.eqb a a') eqn:Heq.
  2, 4: now apply String.eqb_neq in Heq; rewrite t_update_neq.
  all: now apply String.eqb_eq in Heq; subst; rewrite t_update_eq, upd_length.
Qed.

Lemma ideal_eval_preserves_nonempty_arrs (p:prog * nat) : forall c c' st ast b ds st' ast' b' os,
  nonempty_arrs ast ->
  p |- <((c, st, ast, b))> -->i*_ds^^os <((c', st', ast', b'))> ->
  nonempty_arrs ast'.
Proof.
  unfold nonempty_arrs.
  intros. generalize dependent a. induction H0; eauto; subst.
  apply IHmulti_ideal. clear IHmulti_ideal H1.
  induction H0; eauto; subst.
  + intros a'; destruct (String.eqb a a') eqn:Heq.
    - now apply String.eqb_eq in Heq; subst; rewrite t_update_eq, upd_length.
    - now apply String.eqb_neq in Heq; rewrite t_update_neq.
  + intros a''; destruct (String.eqb a' a'') eqn:Heq.
    - now apply String.eqb_eq in Heq; subst; rewrite t_update_eq, upd_length.
    - now apply String.eqb_neq in Heq; rewrite t_update_neq.
Qed.


Ltac solve_refl :=
  match goal with
  | Heq : beval ?ST _ = _, st_b : ?ST "b" = _, Hbe : is_empty _ = _ |- _ =>
          simpl; eexists; (split; [|discriminate]); (try rewrite !app_nil_l); (try (eapply multi_ideal_trans_nil_l; [constructor|]));
          (eapply multi_ideal_trans_nil_r; [|constructor]); simpl; rewrite ?Heq, ?st_b; simpl;
          rewrite <- ?st_b, ?t_update_shadow, !t_update_same, ?andb_false_r; now (constructor; try rewrite ?Heq, ?Hbe, ?orb_true_r, ?andb_false_r)
  end.

Ltac fold_cons :=
  repeat match goal with
  | |- context [?A :: ?B] =>
    lazymatch B with
    | [] => fail
    | _ => change (A :: B) with ([A] ++ B)
    end
  end.

Ltac com_step :=
  repeat ((try now apply multi_ideal_refl); (try now apply multi_spec_refl);
  lazymatch goal with
  | |- _ |- <(( <{{ skip; _ }}>, _, _, _ ))> -->i*_ _^^_ <(( _, _, _, _ ))> => eapply multi_ideal_trans_nil_l; [now apply ISM_Seq_Skip|]
  | |- _ |- <(( <{{ _; ?C }}>, _, _, _ ))> -->i*_ _^^_ <(( <{{ _; ?C }}>, _, _, _ ))> => apply multi_ideal_add_snd_com; eassumption
  | |- _ |- <(( <{{ _; _ }}>, _, _, _ ))> -->i*_ _^^_ <(( _, _, _, _ ))> => eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com; eassumption|]
  | |- _ |- <(( <{{ if _ then _ else _ end }}>, _, _, _ ))> -->i*_ [_]^^[_] <(( _, _, _, _ ))> => eapply multi_ideal_trans_nil_r; [|now constructor]
  | Heq : beval _ _ = _, Hbe : is_empty _ = _ |- _ |- <(( <{{ if _ then _ else _ end }}>, _, _, _ ))> -->i*_ _^^_ <(( _, _, _, _ ))> =>
    fold_cons; econstructor; [constructor; [(try now rewrite ?Heq, ?Hbe); now rewrite andb_comm, Heq|reflexivity]|]
  | |- _ |- <(( <{{ if _ then _ else _ end }}>, _, _, _ ))> -->i*_ _^^_ <(( _, _, _, _ ))> => fold_cons; econstructor; [now constructor|]
  | |- _ |- <(( <{{ while _ do _ end }}>, _, _, _ ))> -->i*_ _^^_ <(( _, _, _, _ ))> => eapply multi_ideal_trans_nil_l; [now constructor|]
  | |- _ => now constructor
  end).


Definition measure (c : com) (ds : dirs) : nat * nat :=
  (length ds, com_size c).

Definition lex_ord (cds1 cds2: com * dirs) : Prop :=
  lex_nat_nat (measure (fst cds1) (snd cds1)) (measure (fst cds2) (snd cds2)).

Require Import Coq.Wellfounded.Inverse_Image.

(* matches syntactic form of prog_size_ind; easier to apply *)
Lemma lex_ind2 : forall P : com -> dirs -> Prop,
    (forall c ds,
        (forall c' ds',
            lex_nat_nat (measure c' ds') (measure c ds) -> P c' ds') ->
        P c ds) -> forall c ds, P c ds.
Proof.
  intros.
  set (f := fun cds => P (fst cds) (snd cds)).
  replace (P c ds) with (f (c, ds)) by auto.
  eapply well_founded_ind.
  - instantiate (1:=lex_ord). unfold lex_ord. 
    apply wf_inverse_image. apply lex_nat_nat_wf.
  - unfold lex_ord. intros. subst f. simpl in *. eapply H.
    intros. specialize (H0 (c', ds')). simpl in H0. 
    apply H0. apply H1.
Qed.

Lemma unused_prog_unused :
  forall (p : prog) (c : com) (X : string), 
    In c p -> unused_prog X p -> unused X c.
Proof.
  intros. unfold unused_prog in H0. rewrite Forall_forall in H0. 
  specialize H0 with (x:=c). apply H0 in H; auto.
Qed.

Ltac measure1 := rewrite lex_nat_nat_equiv; unfold measure, lex_nat_nat_spec; simpl; try (rewrite !app_length); simpl; lia.
Ltac strs_neq := unfold not; intros; discriminate.

Lemma ultimate_slh_inj: forall c1 c2,
    ultimate_slh c1 = ultimate_slh c2 ->
    c1 = c2.
Proof.
  induction c1; intros; simpl in H.
  - destruct c2; simpl in H; inv H. reflexivity.
  - destruct c2; simpl in H; inv H. reflexivity.
  - destruct c2; simpl in H; inv H.
    + erewrite IHc1_1; eauto. erewrite IHc1_2; eauto.
    + destruct c1_1; simpl in H1; discriminate.
    + destruct c1_2; simpl in H2; discriminate.
  - destruct c2; simpl in H; inv H.
    assert (be = be0).
    { clear - H1.
      destruct (is_empty (vars_bexp be)) eqn: B; destruct (is_empty (vars_bexp be0)) eqn: B0; auto.
      - subst. simpl in B. inv B.
      - subst. simpl in B0. inv B0.
      - inv H1. auto. }
    subst. erewrite IHc1_1; eauto. erewrite IHc1_2; eauto.
  - destruct c2; simpl in H; inv H.
    + destruct c2_1; simpl in H1; discriminate.
    + assert (be = be0).
      { clear - H1.
        destruct (is_empty (vars_bexp be)) eqn: B; destruct (is_empty (vars_bexp be0)) eqn: B0; auto.
        - subst. simpl in B. inv B.
        - subst. simpl in B0. inv B0.
        - inv H1. auto. }
      subst. erewrite IHc1; eauto.
  - destruct c2; inv H.
     assert (i = i0).
      { clear - H3.
        destruct (is_empty (vars_aexp i)) eqn: I; destruct (is_empty (vars_aexp i0)) eqn: I0; auto.
        - subst. simpl in I. inv I.
        - subst. simpl in I0. inv I0.
        - inv H3. auto. }
      subst. auto.
  - destruct c2; inv H.
    assert (i = i0).
    { clear - H2.
      destruct (is_empty (vars_aexp i)) eqn: I; destruct (is_empty (vars_aexp i0)) eqn: I0; auto.
      - subst. simpl in I. inv I.
      - subst. simpl in I0. inv I0.
      - inv H2. auto. }
    subst. auto.
  - destruct c2; inv H.
    + destruct c2_2; simpl in H2; discriminate.
    + assert (p = p0).
    { clear - H1.
      destruct (is_empty (vars_aexp p)) eqn: P; destruct (is_empty (vars_aexp p0)) eqn: P0; auto.
      - subst. simpl in P. inv P.
      - subst. simpl in P0. inv P0.
      - inv H1. auto. }
    subst. auto.
Qed.

Lemma app_cons : forall {A} (x : A) (l : list A), 
  x :: l = [x] ++ l.
Proof. simpl. auto. Qed.

Lemma uslh_prog_cons: forall c p n,
    ultimate_slh_prog_gen (c :: p) n = (<{{ "b" := ("callee" = n) ? "b" : 1; (ultimate_slh c) }}>) :: (ultimate_slh_prog_gen p (S n)).
Proof.
  intros. unfold ultimate_slh_prog_gen. simpl. auto.
Qed.

Lemma ultimate_slh_prog_contents:
  forall p n cmd e st,
  nth_error (ultimate_slh_prog_gen p n) e = Some cmd ->
  exists c', cmd = (<{{("b" := ("callee" = (aeval st (n + e))) ? "b" : 1); (ultimate_slh c') }}>).
Proof.
Admitted.

Lemma minus_zero : forall (n : nat),
  n - 0 = n.
Proof.
  induction n; auto.
Qed.

Lemma uslh_prog_to_uslh_com' :
  forall p n c e st,
    nth_error (ultimate_slh_prog_gen p n) e =
      Some (<{{("b" := ("callee" = (aeval st (n + e))) ? "b" : 1);
                (ultimate_slh c) }}>) ->
  nth_error p e = Some c.
Proof.
  induction p.
  - intros. unfold ultimate_slh_prog_gen in H. simpl in H.
    rewrite nth_error_nil in H; discriminate.
  - intros. rewrite app_cons. rewrite nth_error_app. simpl.
    destruct e; simpl.
    + rewrite app_cons in H. simpl in H. rewrite add_0_r in H.
      injection H. intros. apply ultimate_slh_inj in H0. f_equal. auto.
    + rewrite minus_zero. apply IHp with (n:=(S n)) (st:=st).
      rewrite app_cons in H. unfold ultimate_slh_prog_gen, add_index_gen. 
      simpl in *. assert (E: add n (S e) = S (n + e)). { auto. } 
      rewrite E in H. apply H.
Qed.
    
Lemma uslh_prog_preserves_length: forall p n,
    length p = length (ultimate_slh_prog_gen p n).
Proof.
  induction p; auto. intros.
  rewrite app_cons. rewrite length_app.
  rewrite IHp with (n:=(S n)). simpl. 
  unfold ultimate_slh_prog_gen. do 2 rewrite length_map.
  unfold add_index_gen.
  simpl. auto.
Qed.

Definition admit (excuse: String.string) {T: Type} : T.  Admitted.
Tactic Notation "admit" constr(excuse) := idtac excuse; exact (admit excuse).

(* How to use: cadmit "comment". *)

Lemma add_neq : forall (i j n : nat), 
  ((i =? j)%nat = false) -> ((n + i =? n + j)%nat = false).
Proof.
  intros. induction n; auto.
Qed.

Lemma plus_eq_0 : forall n m,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  induction n; intros; try (simpl in H; rewrite H; tauto); discriminate.
Qed.


Lemma nat_True: forall (n : nat), 
  (n = n) <-> True.
Proof.
  split; intros; auto.
Qed.

Lemma j_not_zero: forall (j : nat),
  (0 <> j) -> (match j with
              | 0 => true
              | S _ => false 
              end) = false.
Proof.
  induction j; intros;
  [unfold not in H; rewrite nat_True in H; contradiction|auto].
Qed.

Require Import Coq.Setoids.Setoid.

Lemma ultimate_slh_bcc_generalized (p:prog) : forall c ds st ast (b b' : bool) c' st' ast' os n,
  nonempty_arrs ast ->
  unused_prog "b" p ->
  unused "b" c ->
  unused_prog "callee" p ->
  unused "callee" c ->
  st "b" = (if b then 1 else 0) ->
  (* would it help to have a similar premise about st "callee"? *)
  ((ultimate_slh_prog_gen p n), n) |- <((ultimate_slh c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
      exists c'', (p, n) |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "callee" !-> st "callee"; "b" !-> st "b"; st', ast', b'))>
  /\ (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0)). (* <- generalization *)
Proof.
  intros c ds. apply lex_ind2 with (c:=c) (ds:=ds). clear.
  intros c ds IH. intros until n. 
  intros ast_arrs unused_p unused_c unused_p_callee unused_c_callee st_b st_st'.
  (* st_st' is target multistep *)
  invert st_st'.
  (* multi_spec_refl *)
  { repeat rewrite t_update_same. eexists. split; [apply multi_ideal_refl|].
    split; [|tauto]. now destruct c. 
  }
  (* multi_spec_trans *)
  (* case analysis on commands, then invert single target step *)
  destruct c; invert H.
  11 : { (* Call *)
        invert H12. invert H0. (* inverting multistep produces refl & trans cases *)
        (* reflexive *)
        - eexists. split; try discriminate.
          simpl. rewrite t_update_permute; [|strs_neq].
          rewrite t_update_shadow. repeat rewrite t_update_same. econstructor.
        (* transitive *)
        - inv H.
          (* now H12 single: skip->c1t / H1 multi: c1t;call->c' *)
          { inv H12. } (* now we have call command exposed in hypothesis *)
          rename p0 into f. 
          destruct (is_empty (vars_aexp f)) eqn: Hf.
          { (* optimization (no variables in expression f) *)
            simpl. inv H1. (* H1 is tgt multistep call f *)
            (* refl *)
            - exists <{{ call f }}>. split; [|intros; inv H].
              rewrite t_update_permute; [|strs_neq].
              rewrite t_update_shadow. do 2 rewrite t_update_same.
              constructor.
            (* trans *)
            - inv H. (* produces 2 cases: DStep++ds2, OCall++os2, call f --> c''
                        and DForceCall++ds2, OForceCall++os2, call f --> c'' *)
              + (* DStep *)
                inv H0.
                (* reflexive : []. 0 steps take place after call step. *)
                * (* cleaning up state *)
                  rewrite t_update_neq; [|strs_neq].
                  rewrite t_update_permute; [|strs_neq].
                  rewrite t_update_shadow.
                  rewrite aeval_unused_update in H2; auto.
                  rewrite t_update_permute; [|strs_neq].
                  (* specify the form of the protected command to 
                     which target executes. Note that it contains 
                     the uslh'd source command, so we can know its 
                     name for later. *)
                  specialize (ultimate_slh_prog_contents p n c' i st H3) as (c'' & A).
                  (* connect this to the form of the command 
                     to which source ideally executes *)
                  subst. eapply uslh_prog_to_uslh_com' in H3.
                  (* then instantiate as destination of src execution *)
                  exists c''. split.
                  2:{ intros. inv H. }
                  (* separate out the call step from the ones following *)
                  econstructor 2.
                  (* ISM_Call *)
                  { simpl in *. econstructor; eauto. rewrite Hf. simpl. eauto. }
                  (* multi_ideal_refl *)
                  do 2 rewrite t_update_same. econstructor.
                (* transitive: ds1++ds0 *)
                * (* cleaning up state in premises *)
                  rewrite aeval_unused_update with (n:=(aeval st f)) in H2; auto.
                  simpl in H2, H3. rewrite H2 in *.
                  (* specify the form of the protected command to 
                     which target executes. Note that it contains 
                     the uslh'd source command, so we can know its 
                     name for later. *)
                  specialize (ultimate_slh_prog_contents p n c'0 i st H3) as (c_src & A).
                  (* connect this to the form of the command 
                     to which source ideally executes. specifically, 
                     subst will swap the specific command in for c'0, 
                     which is where the target execution is said to 
                     begin. This is interesting, because we're beginning with 
                     not call f but the command it jumps to. That's the situation 
                     I couldn't make work further below, so why does it work 
                     now and not then? *)
                  subst. apply uslh_prog_to_uslh_com' in H3. 
                  (* so now we know that our target execution starts from 
                     the protected command that contains the source command 
                     that we'd get to from call in the ideal execution. *)
                  (* We invert all the target execution premises. *)
                  inv H. inv H14. inv H1.
                  -- (* refl *)
                     (* clean up state in goal *)
                     simpl. rewrite t_update_shadow.
                     rewrite t_update_permute; [|strs_neq].
                     rewrite t_update_shadow.
                     simpl in *. do 2 rewrite t_update_eq. 
                     rewrite add_comm. rewrite Nat.eqb_refl.
                     rewrite t_update_permute; [|strs_neq].
                     rewrite add_comm. rewrite <- H2. 
                     rewrite t_update_neq; [|strs_neq].
                     (* 0 steps means we're still at c_src,
                        which we previously established is where 
                        call f steps to *)
                     exists c_src. 
                     (* take care of side cases *)
                     split; try split; auto; try discriminate.
                     (* clean up state *)
                     do 2 (eapply ideal_unused_update; eauto; 
                     eapply ideal_unused_overwrite; eauto).
                     (* separate single step and multisteps from which 
                        multistep is constructed. Then it's just 
                        ISM_Call and multi_ideal_refl. *)
                     eapply multi_ideal_trans_nil_r; try econstructor.
                     rewrite H2. apply ISM_Call; auto. 
                     rewrite Hf. simpl. auto.
                -- (* trans *)
                     (* get rid of skip in tgt starting cmd *)
                     inv H.
                     { inv H14. } (* now tgt uslh c_src - c', multistep *)
                     (* clean up state in H0 *)
                     simpl in H0. rewrite add_comm in H0.
                     rewrite add_comm in H2. simpl.
                     rewrite t_update_eq in H0. rewrite Nat.eqb_refl in H0. 
                     rewrite t_update_same in H0.
                     rewrite <- H2 in H0. 
                     (* now H0 matches IH premise enough to apply it.
                        Note this doesn't mean perfect match: we can have 
                        dirty state (to a point), and we can have different 
                        cmd names, but uslh placement needs to match. 
                        Note that measure premise has c' instantiated as 
                        c_src, and ds' as ds2. How did that happen? 
                        It's because in the premise in the IH corresponding to H0, we 
                        have uslh c', and ds', while in H0 we have uslh c_src, and ds2. *)
                     eapply IH in H0; try measure1; auto; cycle 1.
                     (* next two are cleanup for unused variable subgoals *)
                     { unfold unused_prog in unused_p.
                       rewrite Forall_forall in unused_p.
                       specialize (nth_error_In p i H3).
                       intros. apply unused_p in H; auto.
                     }
                     { unfold unused_prog in unused_p_callee. 
                       rewrite Forall_forall in unused_p_callee. 
                       specialize (nth_error_In p i H3).
                       intros. apply unused_p_callee in H; auto. 
                     }
                     (* now we're ready to look at the ideal multiexecution. *)
                     (* clean up state in H0 and destruct. *)
                     rewrite t_update_neq in H0; [|strs_neq].
                     rewrite t_update_eq in H0. 
                     destruct H0 as [c'' H0].
                     (* now instantiate with c'' *)
                     exists c''.
                     (* inv H0 just splits off the side conditions  *)
                     inv H0.
                     (* clean up H0 state and clean up aftermath of cleaning up *)
                     eapply ideal_unused_update in H; cycle 1.
                     { unfold unused_prog in unused_p. 
                       rewrite Forall_forall in unused_p. eauto. }
                     { unfold unused_prog in unused_p_callee. 
                       rewrite Forall_forall in unused_p_callee. 
                       specialize (nth_error_In p i H3).
                       intros. apply unused_p_callee in H0; auto. 
                     }
                     (* solve side conditions *)
                     split; auto.
                     (* now we have matching premise for multiexecution,
                        so it's time to split single and multi in goal *)
                     rewrite app_cons. rewrite app_cons with (l:=os2).
                     (* multi: works bc H has correct form *)
                     econstructor 2; eauto.
                     (* single *)
                     eapply ISM_Call; simpl; auto. rewrite Hf. simpl. lia.
              + (* DForceCall *) 
                inv H0. 
                (* reflexive : []. 0 steps take place after call step. *)
                * rewrite t_update_neq; [|strs_neq]. 
                  rewrite t_update_permute; [|strs_neq].
                  rewrite t_update_shadow. 
                  rewrite t_update_permute; [|strs_neq].
                  rewrite aeval_unused_update in H2; eauto.
                  simpl in H2, H4.
                  specialize (ultimate_slh_prog_contents p n c' j st H4).
                  intros (c'' & A).
                  subst. eapply uslh_prog_to_uslh_com' in H4.
                  exists c''. split; [|intros; inv H].
                  econstructor 2.
                  -- simpl. econstructor; [rewrite Hf| | ]; eauto.
                  -- do 2 rewrite t_update_same. econstructor.
                (* transitive: ds1++ds0 *)
                * simpl. simpl in H2, H4. rewrite aeval_unused_update in H2; auto.
                  specialize (ultimate_slh_prog_contents p n c'0 j st H4) as (c'' & A).
                  subst. eapply uslh_prog_to_uslh_com' in H4. inv H. inv H15. inv H1.
                  -- (* refl *)
                     rewrite t_update_shadow. rewrite t_update_permute; [|strs_neq].
                     rewrite t_update_shadow. do 2 rewrite t_update_same. 
                     rewrite add_comm in H2. rewrite H2. simpl. do 2 rewrite t_update_eq.
                     rewrite <- eqb_neq in H3. specialize (add_neq i j n H3). intros.
                     rewrite H. exists c''. split; try split; auto; try discriminate.
                     eapply multi_ideal_trans_nil_r; try econstructor.
                     ++ rewrite Hf. simpl. rewrite add_comm in H2. eauto.
                     ++ rewrite eqb_neq in H3. auto.
                     ++ simpl. auto.
                  -- (* trans *)
                     simpl in H. rewrite t_update_eq in H. rewrite <- eqb_neq in H3.
                     specialize (add_neq i j n H3). intros. rewrite add_comm in H2. 
                     rewrite H2 in H. rewrite H1 in H. rewrite eqb_neq in H3. simpl.
                     inv H.
                     { inv H16. }
                     apply IH in H0; try measure1; auto.
                     ** simpl. rewrite t_update_eq in H0. rewrite t_update_neq in H0; [|strs_neq].
                        rewrite t_update_eq in H0. rewrite t_update_permute in H0; [|strs_neq].
                        destruct H0 as [c''0 H0]. inv H0.
                        exists c''0. split; auto. rewrite app_cons. rewrite app_cons with (l:=os2).
                        econstructor 2. 
                        { eapply ISM_Call_F; simpl; eauto. rewrite Hf. simpl. lia. }
                        { eapply ideal_unused_update in H; eauto.
                          - rewrite t_update_neq in H; [|strs_neq].
                            rewrite t_update_permute in H; [|strs_neq].
                            apply ideal_unused_update in H; auto.
                            + rewrite t_update_permute in H; [|strs_neq]. auto.
                            + unfold unused_prog in unused_p.
                              rewrite Forall_forall in unused_p.
                              specialize (nth_error_In p j H4).
                              intros. apply unused_p in H0; auto.
                          - unfold unused_prog in unused_p_callee.
                            rewrite Forall_forall in unused_p_callee.
                            specialize (nth_error_In p j H4).
                            intros. apply unused_p_callee in H0; auto.
                        }
                     ** unfold unused_prog in unused_p. 
                        rewrite Forall_forall in unused_p. 
                        specialize (nth_error_In p j H4).
                        intros. apply unused_p in H; auto.
                     ** unfold unused_prog in unused_p_callee. 
                        rewrite Forall_forall in unused_p_callee. 
                        specialize (nth_error_In p j H4).
                        intros. apply unused_p_callee in H; auto.
          }
          (* no optimization *)
          inv H1.
          (* refl case *)
          { exists <{{ call f }}>. simpl. split.
            2:{ intros. inv H. }
            rewrite t_update_permute; [|unfold not; intros; discriminate].
            rewrite t_update_shadow. do 2 rewrite t_update_same. constructor. 
          }
          (* transitive *)
          inv H; simpl.
          (* DStep/OCall *)
          * Opaque unused. simpl in *.
            (* we can't optimize argument of call, so the masking 
               check is now in our state. It depends on the starting msf, which 
               might be true or false. So we destruct. *)
            destruct b'0 eqn:Hmsf; rewrite st_b in *.
            (* already misspeculating *) 
            { (* mask callee to 0, generally clean up state *)
              rewrite Nat.eqb_refl in *.
              rewrite t_update_neq in *; try discriminate.
              rewrite st_b in H2. rewrite Nat.eqb_refl in H2.
              (* since we'll be jumping to the first command in the program, 
                 we need to know if the program is empty or not *)
              destruct p; simpl in *.
              (* program is empty list *)
              { rewrite nth_error_nil in H3. discriminate. }
              (* program is nonempty list *)
              (* we know we'll be jumping to the cmd at index 0 *)
              symmetry in H2. specialize (plus_eq_0 i n H2) as (i_zero & n_zero).
              rewrite i_zero in H3. rewrite n_zero in H0, H3.
              simpl in H3. injection H3; intros C'0.
              rewrite <- C'0 in H0. 
              (* now we know what that cmd is, but since we protected it, 
                 we need to peel off the masking so we can just have 
                 (uslh c) as starting target cmd. *)
              (* specialize (multi_spec_seq (ultimate_slh_prog_gen (c :: p) 0, 0) <{{"b" := ("callee" = 0) ? "b" : 1}}> 
              (ultimate_slh c) c' ("callee" !-> 0; st) ast'0 true st' ast' b' ds2 os2 H0).
                 intros seq_exists. *)
              apply multi_spec_seq in H0. 
              destruct H0 as [seq1 | seq2].
              (* only one of seq1 and seq2 will correctly apply to this 
                 situation, so I will need to prove the inapplicable one 
                 false. I think seq1 is the one that applies. *)
              - (* seq1 *)
                (* why aren't normal intropatterns working :( *)
                destruct seq1 as [st'0 rest].
                destruct rest as [ast'1 rest].
                destruct rest as [b''0 rest].
                destruct rest as [ds1 rest].
                destruct rest as [ds3 rest].
                destruct rest as [os1 rest].
                destruct rest as [os3 rest].
                destruct rest as [OS rest].
                destruct rest as [DS rest].
                destruct rest as [STEPS1 STEPS2].
                (* now we have STEPS2, which isolates the uslh c to c' step. 
                   The problem is that the state, ds, os, etc, that needs to 
                   line up with the goal state is separated across two 
                   hypotheses now. *)
                (* ilu setoid_rewrite *)
                setoid_rewrite <- st_b at 1.
                rewrite OS, DS. 
                (* take apart the asgn premise since we want its information 
                   to get distributed into the right places, but we don't want 
                   the asgn command as starting command. *)
                inv STEPS1. inv H. inv H0. 
                + simpl. simpl in STEPS2. eapply IH in STEPS2; try measure1; eauto.
                  * setoid_rewrite app_cons at 2. setoid_rewrite app_cons at 4.
                    rewrite t_update_eq in STEPS2. 
                    do 2 rewrite t_update_neq in STEPS2; try strs_neq.
                    rewrite t_update_eq in STEPS2. 

              
              (* this is the previous attempt, but what I'm doing today feels 
                 more thought through. However, I'm encountering the same problem 
                 of the multisteps not quite lining up correctly. *)

              (* inv H3. inv H0.
              (* refl *)
              { rewrite t_update_permute; try (unfold not; intros; discriminate).
                rewrite t_update_shadow. rewrite t_update_permute; try (unfold not; intros; discriminate).
                rewrite <- st_b. rewrite t_update_same. rewrite t_update_same.
                rewrite st_b. unfold unused_prog in unused_p_callee.
                specialize (ultimate_slh_prog_contents (c :: p) n c' i st H1). intros.
                destruct H as [c'0 H]. subst. eapply uslh_prog_to_uslh_com' in H1.
                simpl. rewrite <- H2. symmetry in H2. specialize (plus_eq_0 i n H2). intros.
                destruct H. rewrite H, H0. simpl. rewrite t_update_neq; [|strs_neq]. 
                rewrite H in H1. simpl in H1. injection H1. intros. rewrite <- H3.
                exists c. split; try split; [|discriminate|auto].
                eapply multi_ideal_trans_nil_r; [|econstructor].
                replace (OCall 0) with (OCall (0 + 0)) by auto.
                apply ISM_Call; auto. rewrite Hf. simpl. auto.
              }
              (* trans *)
              rewrite <- H2. symmetry in H2. specialize (plus_eq_0 i n H2). intros.
              destruct H0. rewrite H0, H4 in H1. simpl in H1. rewrite H4 in H.
              rewrite H4. rewrite <- st_b. injection H1. intros. rewrite H4 in H3.
              (* I think the below may have been the wrong direction. *)
              exists c'. 
              split; try split; auto.
              { rewrite app_cons with (l:=(ds1 ++ ds0)). 
                rewrite app_cons with (l:=(os1 ++ os0)).
                econstructor 2.
                - replace (OCall 0) with (OCall (0 + (snd (c :: p, 0)))) by auto.
                  apply ISM_Call; [rewrite Hf|simpl]; eauto.
                - apply ideal_unused_update with (n:=(st "callee")); auto.
                  + unfold unused_prog in unused_p_callee. 
                    rewrite Forall_forall in unused_p_callee. 
                    specialize unused_p_callee with (x:=c).
                    simpl in unused_p_callee. apply unused_p_callee. 
                    left. auto.
                  + apply ideal_unused_overwrite; auto.
                    * unfold unused_prog in unused_p_callee. 
                      rewrite Forall_forall in unused_p_callee.
                      specialize unused_p_callee with (x:=c).
                      simpl in unused_p_callee. 
                      apply unused_p_callee. left. auto.
                    * apply ideal_unused_update with (n:=(st "b")); auto.
                      -- unfold unused_prog in unused_p. 
                         rewrite Forall_forall in unused_p. 
                         specialize unused_p with (x:=c).
                         simpl in unused_p. apply unused_p. 
                         left. auto.
                      -- apply ideal_unused_overwrite; auto.
                         ++ unfold unused_prog in unused_p. 
                            rewrite Forall_forall in unused_p.
                            specialize unused_p with (x:=c).
                            simpl in unused_p. 
                            apply unused_p. left. auto.
                         ++ apply multi_ideal_trans with (c':=c'1) (st':=st'0)
                               (ast':=ast'1) (b':=b'0).
                            ** admit "".
                            ** admit "".             
              }
                 rewrite st_b. admit "". *)
            } 
            (* not yet misspeculated *)
            {
              simpl in H0, H2. rewrite aeval_unused_update in H2; auto.
              rewrite t_update_neq in H2; [|strs_neq]. rewrite st_b in H2.
              simpl in H2. destruct p; simpl in *.
              (* p is empty *)
              { unfold ultimate_slh_prog_gen, add_index_gen in H3; simpl in H3;
                rewrite nth_error_nil in H3; discriminate. }
              (* p is nonempty *)
              inv H3. inv H0.
              (* refl *)
              { rewrite t_update_permute; [|strs_neq]. rewrite t_update_shadow.
                rewrite <- st_b. do 2 rewrite t_update_same. rewrite st_b.
                rewrite t_update_neq; [|strs_neq]. 
                specialize (ultimate_slh_prog_contents (c :: p) n c' i st H1). intros.
                destruct H as [c'0 H]. subst. eapply uslh_prog_to_uslh_com' in H1.
                simpl. exists c'0. split; try split; auto; try discriminate.
                eapply multi_ideal_trans_nil_r; econstructor; simpl; auto.
                rewrite Hf. simpl. auto.
              }
              (* trans *)
              { rewrite <- st_b.
                rewrite app_cons with (l:=(ds1 ++ ds0)).
                rewrite app_cons with (l:=(os1 ++ os0)).
                specialize (ultimate_slh_prog_contents (c :: p) n c'0 i st H1).
                intros. destruct H0 as [c'' H0]. subst.
                eapply uslh_prog_to_uslh_com' in H1. simpl in H. rewrite <- H2.
                rewrite add_comm in H2. rewrite H2 in *.
                admit "".
              }
            }
          (* DForceCall/OForceCall *)
          * simpl in *. destruct b'1 eqn:Hmsf; rewrite st_b in *.
            (* already misspeculating *)
            { simpl in H0, H2. rewrite t_update_neq in H2; [|strs_neq].
              rewrite st_b in H2. simpl in H2. symmetry in H2.
              specialize (plus_eq_0 i n H2). intros. destruct H.
              rewrite H1 in H4. rewrite H1 in H0. rewrite H1.
              rewrite add_0_r. rewrite app_cons with (l:=ds2).
              rewrite app_cons with (l:=os2).
              destruct p.
              (* p is empty *)
              { unfold ultimate_slh_prog_gen, add_index_gen in H4. simpl in H4.
                rewrite nth_error_nil in H4. discriminate.
              }
              (* p is nonempty *)
              { inv H4. inv H0.
                (* refl *)
                { rewrite t_update_permute; try (unfold not; intros; discriminate).
                rewrite t_update_shadow. rewrite t_update_permute; try (unfold not; intros; discriminate).
                rewrite <- st_b. do 2 rewrite t_update_same.
                rewrite st_b. unfold unused_prog in unused_p_callee.
                specialize (ultimate_slh_prog_contents (c :: p) 0 c' j st H6). intros.
                destruct H as [c'0 H]. subst. eapply uslh_prog_to_uslh_com' in H6.
                simpl. rewrite <- H2. simpl. 
                rewrite t_update_neq; [|strs_neq]. 
                (* spec flag will be set to 1 and index will be masked to 0 *)
                exists c'0. split; try split; [|discriminate|auto].
                eapply multi_ideal_trans_nil_r; [|econstructor].
                replace (DForceCall j) with (DForceCall (j + 0)) by auto.
                eapply ISM_Call_F with (i:=0); eauto. rewrite Hf. simpl. auto.
                }
                (* trans *)
                { rewrite <- st_b. 
                  specialize (ultimate_slh_prog_contents (c :: p) 0 c'0 j st H6).
                  intros. destruct H0 as [c_src H0]. subst. 
                  eapply uslh_prog_to_uslh_com' in H6. inv H. inv H15. 
                  inv H1.
                  (* refl *)
                  { rewrite t_update_shadow. rewrite t_update_permute; [|strs_neq]. 
                    rewrite t_update_shadow. do 2 rewrite t_update_same. 
                    rewrite t_update_permute; [|strs_neq]. 
                    rewrite t_update_neq; [|strs_neq]. 
                    rewrite t_update_eq. simpl.
                    specialize (j_not_zero j H3). intros. rewrite j_not_zero; auto.
                    exists c_src. split; try split; auto; try discriminate.
                    eapply multi_ideal_trans_nil_r; try econstructor.
                    replace (DForceCall j) with (DForceCall (j + (snd (c :: p, 0)))) by auto.
                    eapply ISM_Call_F; eauto; rewrite Hf; simpl; auto.
                  }
                  (* trans *)
                  { inv H; try inv H15. simpl. 
                    rewrite t_update_permute; [|strs_neq].
                    simpl in H0. rewrite j_not_zero in H0; auto.
                    rewrite <- st_b in H0. rewrite t_update_permute in H0; 
                    [|strs_neq]. rewrite t_update_same in H0. 
                    rewrite app_cons with (l:=ds2). 
                    rewrite app_cons with (l:=os2).
                    apply IH in H0; try measure1; auto.
                    2 : { unfold unused_prog in unused_p. 
                          rewrite Forall_forall in unused_p. 
                          specialize (nth_error_In (c :: p) j H6).
                          intros. apply unused_p in H; auto.
                        }
                    2 : { unfold unused_prog in unused_p_callee. 
                          rewrite Forall_forall in unused_p_callee. 
                          specialize (nth_error_In (c :: p) j H6).
                          intros. apply unused_p_callee in H; auto.
                        }
                    destruct H0 as [c'' H0]. destruct H0 as [H0 rest].
                    exists c''. split; eauto. 
                    - eapply multi_ideal_trans.
                      + replace (DForceCall j) with (DForceCall (j + (snd (c :: p, 0)))) by auto.
                        eapply ISM_Call_F; eauto; rewrite Hf; simpl; auto.
                      + rewrite t_update_permute; [|strs_neq].
                        rewrite t_update_eq in H0. 
                        rewrite t_update_neq in H0; [|strs_neq].
                        apply ideal_unused_update in H0; auto.
                        unfold unused_prog in unused_p_callee. 
                        rewrite Forall_forall in unused_p_callee. 
                        specialize (nth_error_In (c :: p) j H6).
                        intros. apply unused_p_callee in H; auto.
                    - rewrite st_b; auto.
                  }
                }
              }
            }
            (* not yet misspeculating *)
            simpl in H2. rewrite t_update_neq in H2; [|strs_neq].
            rewrite st_b in H2. simpl in H2. 
            rewrite aeval_unused_update in H2; auto.
            simpl in H0. rewrite H2 in H0. rewrite app_cons with (l:=ds2).
            rewrite app_cons with (l:=os2). destruct p.
            (* p is empty *)
            { unfold ultimate_slh_prog_gen, add_index_gen in H4. simpl in H4.
              rewrite nth_error_nil in H4. discriminate.
            }
            (* p is nonempty *)
            { inv H4. inv H0.
              (* refl *)
              { rewrite t_update_permute; try (unfold not; intros; discriminate).
                rewrite t_update_shadow. rewrite t_update_permute; 
                try (unfold not; intros; discriminate).
                rewrite <- st_b. do 2 rewrite t_update_same.
                unfold unused_prog in unused_p_callee.
                specialize (ultimate_slh_prog_contents (c :: p) n c' j st H1). intros.
                destruct H as [c'0 H]. subst. eapply uslh_prog_to_uslh_com' in H1.
                simpl. rewrite <- H2. simpl. 
                rewrite t_update_neq; [|strs_neq].
                exists c'0. split; try split; [|discriminate|].
                2 : { admit "lemma needed, connecting the fact that 
                              we've gone from not spec to spec so 
                              st b ≠ st' b". }
                eapply multi_ideal_trans_nil_r; [|econstructor].
                replace (DForceCall (j + n)) with (DForceCall (j + (snd ((c :: p), n)))) by auto.
                eapply ISM_Call_F; eauto. rewrite Hf. simpl. auto.
              }
              (* trans *)
              admit "".
            }
      }
  - (* Asgn *)
    invert H0; [|now inversion H].
    eexists. split; [eapply multi_ideal_trans|split; [tauto|] ].
    + apply ISM_Asgn. reflexivity.
    + rewrite t_update_permute with (x1:="b") (x2:=x);
      try (rewrite t_update_permute with (x1:="callee") (x2:=x)); try tauto;
      try (unfold not; intros).
      2 : { unfold not. intros. unfold unused in unused_c_callee; 
        destruct unused_c_callee. contradiction. }
      2 : { unfold not. intros. unfold unused in unused_c.
        destruct unused_c. contradiction. }
      do 2 rewrite t_update_same. constructor.
    + rewrite <- st_b. apply t_update_neq. unfold not. intros.
      unfold unused in unused_c. destruct unused_c. contradiction.
  - (* Seq *)
    eapply multi_spec_seq in H0.
    destruct H0.
    + do 8 destruct H. destruct H0, H1. subst.
      eapply multi_spec_trans in H12; [|apply H1]. clear H1.
      eapply IH in H12; eauto; [|measure1|inversion unused_c|inversion unused_c_callee];
      auto. destruct H12 as (c''&st_x&->&Hx); [reflexivity|]. eapply IH in H2; try tauto.
      { destruct H2, H. exists x6. split; [|tauto]. rewrite !app_assoc. com_step.
        erewrite <- t_update_same, <- t_update_shadow in H at 1.
        apply ideal_unused_update in H; try tauto; [|inversion unused_c_callee; auto].
        rewrite t_update_eq in H. admit.
      }
      { measure1. }
      { eapply ideal_eval_preserves_nonempty_arrs; eassumption. }
      { inversion unused_c; auto. }
      { inversion unused_c_callee; auto. }
    + do 2 destruct H. subst.
      eapply multi_spec_trans in H12; [|apply H0].
      eapply IH in H12; eauto; try measure1; try tauto; 
      [|inversion unused_c|inversion unused_c_callee]; auto.
      destruct H12 as (c''&st_st'&H').
      exists <{{ c''; c2 }}>. split; [|discriminate]. com_step.
  - (* Seq-Skip *)
    destruct c1; invert H2.
    eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; auto. 
    destruct H0 as (c''&st'0_st'&H').
    exists c''. split; [|tauto]. simpl. now com_step.
  - (* If *)
    destruct (is_empty (vars_bexp be)) eqn:Hbe.
    + simpl in H0. destruct (beval st'0 be) eqn:Heq.
      * invert H0; [solve_refl|].
        invert H. invert H12. invert H1; [solve_refl|].
        invert H; [inversion H12|].
        simpl in H0. rewrite st_b, Heq in H0. simpl in H0. rewrite <- st_b, t_update_same in H0.
        eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
        try (destruct H1; auto).
        destruct H0 as (c''&st'0_st'&H').
        exists c''. simpl. split; [|tauto]. now com_step.
      * invert H0; [solve_refl|].
        invert H. invert H12. invert H1; [solve_refl|].
        invert H; [inversion H12|].
        simpl in H0. rewrite st_b, Heq in H0. simpl in H0. rewrite <- st_b, t_update_same in H0.
        eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
        try (destruct H1; auto).
        destruct H0 as (c''&st'0_st'&H').
        exists c''. simpl. split; [|tauto]. now com_step.
    + case (beval st'0 be) eqn:Heq.
      * simpl in H0; destruct b'0; rewrite st_b in H0; simpl in H0.
        ++ invert H0; [solve_refl|]. invert H. invert H12. invert H1; [solve_refl|].
           invert H; [inversion H12|]. simpl in H0. rewrite st_b in H0; simpl in H0. rewrite <- st_b, t_update_same in H0.
           eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
           try (destruct H1; auto).           
           destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite st_b at 2. simpl.
           split; [|eassumption]. now com_step.
        ++ rewrite Heq in H0. invert H0; [solve_refl|]. invert H. invert H12. invert H1; [solve_refl|]. 
           invert H; [inversion H12|].
           simpl in H0. rewrite st_b, Heq in H0. simpl in H0. rewrite <- st_b, t_update_same in H0.
           apply IH in H0; auto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
           try (destruct H1; auto).         
           destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite st_b at 2. simpl.
           split; [|eassumption]. com_step. now rewrite Heq.
      * simpl in H0. rewrite Heq, andb_false_r in H0. invert H0; [solve_refl|]. invert H. invert H12. 
        invert H1; [solve_refl|].
        invert H; [inversion H12|]. simpl in H0. rewrite Heq, andb_false_r in H0. rewrite t_update_same in H0.
        apply IH in H0; auto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
        try (destruct H1; auto).
        destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite Heq, andb_false_r. simpl.
        split; [|eassumption]. now com_step.
  - (* If-Force *)
    destruct (is_empty (vars_bexp be)) eqn:Hbe.
    + simpl in H0. destruct (beval st'0 be) eqn:Heq.
      * invert H0; [solve_refl|].
        invert H. invert H12. invert H1; [solve_refl|].
        invert H; [inversion H12|].
        simpl in H0. rewrite st_b, Heq in H0. simpl in H0.
        eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
        try (destruct H1; auto).
        destruct H0 as (c''&st'0_st'&H'). rewrite t_update_eq in st'0_st'.
        eapply ideal_unused_update in unused_p; eauto.
        -- exists c''. simpl.  split; [|tauto].
           eapply ideal_unused_update in unused_p_callee; eauto.
           admit.
        -- admit.
      * invert H0; [solve_refl|].
        invert H. invert H12. invert H1; [solve_refl|].
        invert H; [inversion H12|].
        simpl in H0. rewrite st_b, Heq in H0. simpl in H0.
        eapply IH in H0; eauto; try measure1; [|inversion unused_c|inversion unused_c_callee]; 
        try (destruct H1; auto).
        destruct H0 as (c''&st'0_st'&H').
        rewrite t_update_eq in st'0_st'. (* apply ideal_unused_update in st'0_st'; try tauto.
                                            exists c''. simpl. split; [|tauto]. now com_step.*) 
        admit.
    + case (beval st'0 be) eqn:Heq.
      * simpl in H0; destruct b; rewrite st_b in H0; simpl in H0.
        -- invert H0; [solve_refl|]. invert H. invert H12. invert H1; [solve_refl|].
           invert H; [inversion H12|]. simpl in H0. rewrite st_b in H0; simpl in H0. rewrite <- st_b, t_update_same in H0.
           apply IH in H0; auto; [|measure1|inversion unused_c|inversion unused_c_callee]; 
           try (destruct H1); auto.
           destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite st_b at 2. simpl.
           split; [|eassumption]. now com_step.
        -- rewrite Heq in H0. invert H0; [solve_refl|]. invert H. invert H12. invert H1; [solve_refl|]. 
           invert H; [inversion H12|].
           simpl in H0. rewrite st_b, Heq in H0. simpl in H0.
           apply IH in H0; auto; [|measure1|inversion unused_c|inversion unused_c_callee]; 
           try (destruct H1); auto. 
           destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite st_b at 2. simpl.
           rewrite t_update_eq in st'0_st'. (* apply ideal_unused_update in st'0_st'; auto; [|tauto].
                                               split; [|eassumption]. com_step. now rewrite Heq.*) admit.
      * simpl in H0. rewrite Heq, andb_false_r in H0. invert H0; [solve_refl|]. invert H. invert H12. 
        invert H1; [solve_refl|].
        invert H; [inversion H12|]. simpl in H0. rewrite Heq, andb_false_r in H0.
        apply IH in H0; auto; [|measure1|inversion unused_c|inversion unused_c_callee]; 
           try (destruct H1); auto.
        destruct H0 as (c''&st'0_st'&H'). eexists. simpl. rewrite Heq, andb_false_r. simpl.
        rewrite t_update_eq in st'0_st'. (* apply ideal_unused_update in st'0_st'; auto; [|tauto].
        split; [|eassumption]. now com_step.*) admit.
  - (* While *)
    invert H12. invert H0.
    (* reflexive multistep *)
    { eexists. split; [|discriminate]. simpl. rewrite t_update_same. rewrite t_update_same. constructor. }
    (* transitive multistep *)
    invert H. invert H12; simpl in *.
    (* step *)
    + destruct (is_empty (vars_bexp be)) eqn:Hbe.
      (* optimization *)
      * destruct (beval st'1 be) eqn:Heq.
        (* be true *)
        -- invert H1; [solve_refl|]. invert H. invert H12. invert H11. invert H12. invert H0; [solve_refl|].
           invert H. invert H12. invert H11; [inversion H12|]. apply multi_spec_seq_assoc in H1.
           destruct H1 as (?&H&H'). apply multi_spec_seq in H. destruct H.
           (* two goals bc conclusion of multi_spec_seq is of form P \/ Q *)
           ++ do 8 destruct H. destruct H0, H1. subst. simpl in H1. rewrite Heq, t_update_same in H1.
              apply IH in H1; auto;[|measure1|inversion unused_c|inversion unused_c_callee]; auto.
              destruct H1 as (c''&H&(->&H'')); [reflexivity|].
              replace <{{while be do "b" := be ? "b" : 1; (ultimate_slh c) end; "b" := be ? 1 : "b"}}> with
                (ultimate_slh <{{ while be do c end }}>) in H2 by now simpl; rewrite Hbe.
              pose proof (ideal_eval_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ ast_arrs H).
              apply IH in H2; auto; [|measure1]. 
              destruct H2 as (c''&H1&H1'').
              eexists. split; [|now intro c'_skip; apply H' in c'_skip; apply H1'']. com_step. simpl.
              eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|].
              erewrite st_b, <- t_update_shadow with (m:=st'). apply ideal_unused_overwrite; simpl; try tauto.
              eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|]. rewrite t_update_shadow. 
              apply ideal_unused_overwrite; auto. 
        (* ideal_unused_overwrite:
        forall (p : prog) (st : state) (ast : astate) (b : bool) 
          (ds : dirs) (c c' : com) (st' : state) (ast' : astate) 
          (b' : bool) (os : obs) (X : string) (n : nat),
        unused_prog X p ->
        unused X c ->
        p |- <(( c, st, ast, b ))> -->i*_ ds ^^ os <(( c', st', ast', b' ))> ->
        p |- <(( c, X !-> n; st, ast, b ))> -->i*_ ds ^^ os <(( c', X !-> n; st', ast', b' ))>

        ideal_unused_update:
        forall (p : prog) (st : total_map nat) (ast : astate) 
          (b : bool) (ds : dirs) (c c' : com) (st' : total_map nat) 
          (ast' : astate) (b' : bool) (os : obs) (X : string) 
          (n : nat),
        unused_prog X p ->
        unused X c ->
        p |- <(( c, X !-> n; st, ast, b ))> -->i*_ ds ^^ os <(( c', X !-> n; st', ast', b' ))> ->
        p |- <(( c, st, ast, b ))> -->i*_ ds ^^ os <(( c', X !-> st X; st', ast', b' ))>


      *)



                            Search unused. eapply ideal_unused_overwrite; eauto. eapply ideal_unused_overwrite in H1; eauto. 
              rewrite t_update_shadow in H1. 
           ++ do 2 destruct H. subst. simpl in H0. rewrite Heq, t_update_same in H0. 
              apply IH in H0; auto; [ |measure1|tauto]. 
              destruct H0, H. eexists. split; [|intro abs; apply H' in abs; discriminate]. com_step. simpl.
              rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds0).
              eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com; eassumption|constructor].
        (* be false *)
        -- invert H1; [solve_refl|]. invert H; [inversion H12|]. invert H0; [solve_refl|]. invert H. 
           invert H1; [|inversion H].
           eexists. split; [|split; [reflexivity|now rewrite t_update_eq; simpl; rewrite Heq] ]. com_step. 
           rewrite t_update_shadow, t_update_same. simpl.
           constructor.
      (* no optimization *)
      * destruct (beval st'1 be) eqn:Heq.
        (* be true *)
        -- destruct b'1. (* b'1 is the start state of semantic spec flag in ideal semantics *)
           (* b'1 true *)
           ++ simpl in H1. rewrite st_b, Heq in H1. simpl in H1. invert H1; [solve_refl|].
              invert H; [inversion H12|]. invert H0; [solve_refl|]. invert H. invert H1; [|inversion H].
              eexists. split; [|split; [reflexivity|now rewrite t_update_eq; simpl; rewrite st_b, Heq] ]. 
              rewrite t_update_shadow, t_update_same.
              com_step. simpl. rewrite st_b, Heq.  simpl. com_step. constructor; [now rewrite Hbe, Heq|reflexivity].
           (* b'1 false *)
           ++ simpl in H1. rewrite st_b, Heq in H1. simpl in H1. apply multi_spec_seq_assoc in H1.
              destruct H1 as (?&H&H'). apply multi_spec_seq in H. destruct H.
              (* two goals bc conclusion of multi_spec_seq is of form P \/ Q *)
              ** do 8 destruct H. destruct H0, H1. subst. simpl in H1. invert H1. invert H. invert H13. 
                 invert H0. invert H; [inversion H13|].
                 simpl in H1. rewrite st_b, Heq in H1. simpl in H1. rewrite <- st_b, t_update_same in H1.
                 apply IH in H1; auto; [ |measure1|tauto].
                 destruct H1 as (c''&H&(->&H'')); [reflexivity|].
                 replace <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; 
                   (ultimate_slh c) end; "b" := ("b" = 0 && be) ? 1 : "b"}}> with
                  (ultimate_slh <{{ while be do c end }}>) in H2 by now simpl; rewrite Hbe.
                 pose proof (ideal_eval_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ ast_arrs H).
                 apply IH in H2; auto; [|measure1].
                 destruct H2 as (c''&H1&H1'').
                 eexists. split; [|now intro c'_skip; apply H' in c'_skip; apply H1'']. simpl. rewrite st_b, Heq. 
                 simpl. fold_cons.
                 eapply multi_ideal_trans_nil_l; [constructor|]. econstructor; 
                 [now constructor; [rewrite Hbe|reflexivity] |].
                 eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|]. 
                 eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|].
                 erewrite st_b, <- t_update_shadow with (m:=st'). apply ideal_unused_overwrite; simpl; try tauto. 
                 eassumption.
              ** do 2 destruct H. subst. invert H0.
                 { eexists. split; [|intro abs; apply H' in abs; discriminate]. simpl. rewrite t_update_same, st_b, Heq. 
                   simpl. com_step. now constructor; [rewrite Hbe|]. }
                 invert H. invert H12. invert H1.
                 { eexists. split; [|intro abs; apply H' in abs; discriminate]. simpl.
                   rewrite t_update_shadow, t_update_same, st_b, Heq. simpl. com_step. now constructor; [rewrite Hbe|]. }
                 invert H; [inversion H12|]. simpl in H0. rewrite st_b, Heq in H0. simpl in H0. 
                 rewrite <- st_b, t_update_same in H0.
                 apply IH in H0; auto; [ |measure1|tauto].
                 destruct H0, H. eexists. split; [|intro Hc'; apply H' in Hc'; discriminate]. simpl. 
                 rewrite st_b, Heq. simpl.
                 com_step. apply multi_ideal_add_snd_com. rewrite <- st_b. eassumption.
        (* be false *)
        -- simpl in H1. rewrite Heq, andb_false_r in H1. invert H1; [solve_refl|]. invert H; [inversion H12|]. 
           invert H0; [solve_refl|]. invert H. invert H1; [|inversion H].
           eexists. split; [|split; [reflexivity|now simpl; rewrite t_update_eq, Heq, andb_false_r, st_b] ]. simpl. 
           rewrite Heq, andb_false_r, t_update_shadow, t_update_same.
           com_step. now constructor; [rewrite Heq, andb_false_r|].
    (* force *)
    + destruct (is_empty (vars_bexp be)) eqn:Hbe.
      (* optimization *)
      * destruct (beval st'1 be) eqn:Heq.
        (* be true *)
        -- invert H1; [solve_refl|]. invert H; [inversion H12|]. invert H0; [solve_refl|]. invert H. 
           invert H1; [|inversion H].
           eexists. split; [|split; [reflexivity|now simpl; rewrite t_update_eq, Heq] ]. simpl. 
           rewrite t_update_shadow, t_update_same. com_step.
           now constructor; [rewrite Hbe, Heq|].
        (* be false *)
        -- invert H1; [solve_refl|]. invert H. invert H12. invert H11. invert H12. invert H0; [solve_refl|].
           invert H. invert H12. invert H11; [inversion H12|]. apply multi_spec_seq_assoc in H1.
           destruct H1 as (?&H&H'). apply multi_spec_seq in H. destruct H.
           (* two goals bc conclusion of multi_spec_seq is of form P \/ Q *)
           ++ do 8 destruct H. destruct H0, H1. subst. simpl in H1. rewrite Heq in H1.
              apply IH in H1; auto; [|measure1|tauto].
              destruct H1 as (c''&H&(->&H'')); [reflexivity|]. rewrite t_update_eq in H.
              apply ideal_unused_update in H; try tauto.
              replace <{{while be do "b" := be ? "b" : 1; (ultimate_slh c) end; "b" := be ? 1 : "b"}}> with
                (ultimate_slh <{{ while be do c end }}>) in H2 by now simpl; rewrite Hbe.
              pose proof (ideal_eval_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ ast_arrs H).
              apply IH in H2; auto; [|measure1]. destruct H2 as (c''&H1&H1'').
              eexists. split; [|now intro c'_skip; apply H' in c'_skip; apply H1'']. com_step. simpl.
              eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|].
              erewrite st_b, <- t_update_shadow with (m:=st'). apply ideal_unused_overwrite; 
              simpl; try tauto. eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|]. eassumption.          
           ++ do 2 destruct H. subst. simpl in H0. rewrite Heq in H0. apply IH in H0; auto; [ |measure1|tauto].
              destruct H0, H. eexists. split; [|intro abs; apply H' in abs; discriminate]. 
              simpl. com_step. rewrite t_update_eq in H.
              apply ideal_unused_update in H; auto; [|tauto].
              apply multi_ideal_add_snd_com. eassumption.
      (* no optimization *)
      * destruct (beval st'1 be) eqn:Heq.
        (* be true *)
        -- simpl in H1. rewrite st_b, Heq in H1. destruct b'0.
           ++ simpl in H1. invert H1; [solve_refl|]. invert H. invert H12. invert H11. invert H12. 
              invert H0; [solve_refl|]. invert H. invert H12.
              invert H11; [inversion H12|]. apply multi_spec_seq_assoc in H1.
              destruct H1 as (?&H&H'). apply multi_spec_seq in H. destruct H.
              ** do 8 destruct H. destruct H0, H1. subst. simpl in H1. rewrite st_b, Heq in H1. simpl in H1. 
                 rewrite <- st_b, t_update_same in H1.
                 apply IH in H1; auto; [ |measure1|tauto].
                 destruct H1 as (?&Hc&(->&x0b)); [reflexivity|].
                 replace <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; 
                   (ultimate_slh c) end; "b" := ("b" = 0 && be) ? 1 : "b"}}> with
                   (ultimate_slh <{{ while be do c end }}>) in H2 by now simpl; rewrite Hbe.
                 pose proof (ideal_eval_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ ast_arrs Hc). 
                 apply IH in H2; auto; [|measure1].
                 destruct H2, H0. eexists. split; [|now intro Hc'; apply H1, H']. simpl. rewrite st_b, Heq.
                 pose proof (multi_ideal_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ Hc). subst. 
                 rewrite st_b, <- x0b, t_update_same in Hc.
                 rewrite x0b in H0. simpl. fold_cons. eapply multi_ideal_trans_nil_l; [constructor|]. 
                 econstructor; [now constructor; [rewrite Hbe, Heq|] |].
                 eapply multi_ideal_combined_executions; [eapply multi_ideal_add_snd_com; eassumption|]. 
                 eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|eassumption].
              ** do 2 destruct H. subst. simpl in H0. rewrite st_b, Heq in H0. simpl in H0. 
                 rewrite <- st_b, t_update_same in H0.
                 apply IH in H0; auto; [ |measure1|tauto]. 
                 destruct H0, H. eexists. split; [|intro abs; apply H' in abs; discriminate]. simpl. rewrite st_b, Heq. 
                 simpl. com_step. apply multi_ideal_add_snd_com. rewrite <- st_b. eassumption.
           ++ simpl in H1. invert H1; [solve_refl|]. invert H; [inversion H12|]. invert H0; [solve_refl|]. invert H. invert H1; [|inversion H].
              eexists. split; [|split; [reflexivity|now simpl; rewrite t_update_eq, st_b, Heq] ]. simpl. rewrite t_update_shadow, t_update_same, st_b, Heq. simpl.
              com_step. now constructor; [rewrite Hbe, Heq|].
        (* be false *)
        -- simpl in H1. rewrite Heq, andb_false_r in H1.
           invert H1; [solve_refl|]. invert H. invert H12. invert H11. invert H12. invert H0; [solve_refl|]. invert H. invert H12.
           invert H11; [inversion H12|]. apply multi_spec_seq_assoc in H1.
           destruct H1 as (?&H&H'). apply multi_spec_seq in H. destruct H.
           ++ do 8 destruct H. destruct H0, H1. subst. simpl in H1. rewrite Heq, andb_false_r in H1.
              apply IH in H1; auto; [ |measure1|tauto].
              destruct H1 as (?&Hc&(->&x0b)); [reflexivity|].
              replace <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; (ultimate_slh c) end; "b" := ("b" = 0 && be) ? 1 : "b"}}> with
                (ultimate_slh <{{ while be do c end }}>) in H2 by now simpl; rewrite Hbe.
              pose proof (ideal_eval_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ ast_arrs Hc). 
              apply IH in H2; auto; [|measure1].
              destruct H2, H0. eexists. split; [|now intro Hc'; apply H1, H']. simpl.
              rewrite Heq, andb_false_r.
              pose proof (multi_ideal_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ Hc). subst.
              rewrite t_update_eq, <- x0b, t_update_same in Hc. rewrite x0b in H0. simpl. 
              fold_cons. eapply multi_ideal_trans_nil_l; [constructor|].
              eapply ideal_unused_update; simpl; try tauto. rewrite x0b in Hc. 
              rewrite !app_comm_cons. 
              assert (app_cons : forall [A : Type] (x : A) (l : list A), 
                        x :: l = [x] ++ l).
              { intros. simpl. reflexivity. }
              rewrite app_cons. rewrite (app_cons observation (OBranch false) x5). 
              rewrite <- app_assoc. rewrite <- (app_assoc [OBranch false] x5 x6).
              (* is there a more graceful way to target the exact rewrites I want? *)
              econstructor; [now constructor; [rewrite beval_unused_update, Heq, andb_false_r|] |].
              eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com; eassumption|]. 
              now eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|].
           ++ do 2 destruct H. subst. simpl in H0. rewrite Heq, andb_false_r in H0.
              apply IH in H0; auto; [ |measure1|tauto].
              destruct H0, H. rewrite t_update_eq in H. apply ideal_unused_update in H; try tauto.
              eexists. split; [|intro abs; apply H' in abs; discriminate]. simpl. rewrite Heq, andb_false_r. com_step. apply multi_ideal_add_snd_com. eassumption.
  - (* Read *)
    invert H0; [|inversion H].
    destruct (is_empty (vars_aexp i)) eqn:Heq.
    + eexists. split; [|split; [reflexivity|rewrite t_update_neq; tauto] ]. repeat econstructor; [now rewrite Heq|tauto|].
      rewrite t_update_permute, t_update_same; [constructor|tauto].
    + eexists. split; [|split; [reflexivity|rewrite t_update_neq; tauto] ]. repeat econstructor; [now simpl; rewrite Heq, st_b; destruct b'|tauto|].
      rewrite t_update_permute, t_update_same; [constructor|tauto].
  - (* Load *)
    destruct (is_empty (vars_aexp i)) eqn:Heq.
    + invert H0; [|inversion H]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
      eexists. split; [|split; [reflexivity|rewrite t_update_neq; tauto] ]. repeat econstructor; tauto.
    + simpl in H14. rewrite st_b in H14. simpl in H14.
      specialize (ast_arrs a). lia.
  - (* Write *)
    invert H0; [|inversion H].
    destruct (is_empty (vars_aexp i)) eqn:Heq.
    + eexists. split; [|tauto]. repeat econstructor; [now rewrite Heq|tauto|]. rewrite t_update_same. constructor.
    + eexists. split; [|tauto]. repeat econstructor; [now simpl; rewrite Heq, st_b; destruct b'|tauto|]. rewrite t_update_same. constructor.
  - (* Store *)
    destruct (is_empty (vars_aexp i)) eqn:Heq.
    + invert H0; [|inversion H]. rewrite t_update_same.
      eexists. split; [|tauto]. repeat econstructor; tauto.
    + simpl in H15. rewrite st_b in H15. simpl in H15.
      specialize (ast_arrs a). lia.
  - (* Call *) invert H12. invert H0.
    (* reflexive *)
    + eexists. split; try discriminate.
      simpl. rewrite t_update_permute; [|unfold not; intros; discriminate].
      rewrite t_update_same. 
             
      

    (* transitive *)
    + admit. 
    admit.
Admitted.

(* HIDE: YH:
         How about a statement like this?
         This means all commands in the program satisfy backwards compiler correctness of uslh."

Lemma ultimate_slh_bcc (p:prog) : forall c ds st ast (b b' : bool) c' st' ast' os,
  nonempty_arrs ast ->
  unused_prog p ->
  In c p ->
  st "b" = (if b then 1 else 0) ->
  p |- <((ultimate_slh c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
      exists c'', p |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st', ast', b'))>.
Proof.
 *)
Lemma ultimate_slh_bcc (p:prog) : forall c ds st ast (b b' : bool) c' st' ast' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  p |- <((ultimate_slh c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
      exists c'', p |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st', ast', b'))>.
Proof.
  intros. apply ultimate_slh_bcc_generalized in H2; eauto; firstorder.
  unfold unused_prog.
Admitted.

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

Lemma ideal_dirs_split (p:prog) : forall ds c st ast stt astt os ct,
  p |- <(( c, st, ast, false ))> -->i*_ ds ^^ os <(( ct, stt, astt, true ))> ->
  exists ds1 ds2, (forall d, In d ds1 -> d = DStep) /\ ds = ds1 ++ [DForce] ++ ds2 .
Proof.
  intros. remember false as b. remember true as b'.
  revert Heqb Heqb'.
  induction H; intros; subst; try discriminate.
  destruct b'.
  + apply ideal_eval_small_step_spec_needs_force in H.
    subst. exists [], ds2. now repeat econstructor.
  + destruct IHmulti_ideal; [reflexivity..|]. do 2 destruct H1. subst.
    exists (ds1++x), x0. split; [|now rewrite app_assoc].
    intros. apply in_app_or in H2. destruct H2; [|now apply H1].
    now eapply ideal_eval_small_step_final_spec_bit_false in H; [|eassumption].
Qed.

Lemma ideal_eval_small_step_obs_length_zero_one : forall c st ast b ct stt astt bt ds os,
  <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  os = [] \/ length os = 1.
Proof.
  induction c; intros; invert H; auto.
  eapply IHc1. eassumption.
Qed.

Lemma ideal_eval_small_step_split_by_dir : forall c ct st ast b d ds stt astt bt o os,
  <((c, st, ast, b))> -->i*_d::ds^^o::os <((ct, stt, astt, bt))> ->
  exists cm stm astm bm cm' stm' astm' bm',
    <((c, st, ast, b))> -->i*_[]^^[] <((cm, stm, astm, bm))> /\
    <((cm, stm, astm, bm))> -->i_[d]^^[o] <((cm', stm', astm', bm'))> /\
    <((cm', stm', astm', bm'))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. remember (d::ds) as ds0. remember (o::os) as os0.
  revert o os d ds Heqds0 Heqos0. induction H; intros; [discriminate|].
  edestruct ideal_eval_small_step_obs_length_zero_one; [apply H|subst; simpl in *; subst..].
  + apply app_eq_cons in Heqds0. destruct Heqds0.
    2:{ do 2 destruct H1; subst. apply ideal_eval_small_step_obs_length in H. simpl in H. lia. }
    destruct H1; subst. edestruct IHmulti_ideal; [reflexivity..|].
    do 8 destruct H1. destruct H2. eapply multi_ideal_trans in H1; [|eassumption].
    repeat eexists; eassumption.
  + apply app_eq_cons in Heqos0. destruct Heqos0; [destruct H2; subst; simpl in *; lia|].
    do 2 destruct H2. subst. simpl in H1. invert H1. apply length_zero_iff_nil in H3. subst.
    assert (ds1 = [d]).
    { apply ideal_eval_small_step_obs_length in H. apply app_eq_cons in Heqds0.
      destruct Heqds0; [destruct H1; subst; simpl in *; lia|]. do 2 destruct H1.
      subst. simpl in H. invert H. apply length_zero_iff_nil in H2. now subst. }
    subst. simpl in *. invert Heqds0. repeat eexists; [constructor|eassumption..].
Qed.

Lemma ideal_eval_small_step_split_by_dirs : forall ds1 c ct st ast b ds stt astt bt os ds2,
  <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  ds = ds1 ++ ds2 ->
  exists cm stm astm bm os1 os2,
    <((c, st, ast, b))> -->i*_ds1^^os1 <((cm, stm, astm, bm))> /\
    <((cm, stm, astm, bm))> -->i*_ds2^^os2 <((ct, stt, astt, bt))> /\
    os = os1++os2.
Proof.
  induction ds1; intros; subst.
  - simpl in H. repeat eexists; [constructor|eassumption|reflexivity].
  - simpl in *. destruct os.
    { apply multi_ideal_obs_length in H. simpl in H. lia. }
    apply ideal_eval_small_step_split_by_dir in H. do 9 destruct H. destruct H0.
    eapply IHds1 in H1; [|reflexivity]. do 7 destruct H1. destruct H2. subst.
    eapply multi_ideal_trans in H1; [|eassumption].
    eapply multi_ideal_combined_executions in H1; [|eassumption]. simpl in H1. clear H H0.
    repeat econstructor; eauto.
Qed.

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

Lemma eval_no_vars : forall st st',
  (forall a,
    is_empty (vars_aexp a) = true ->
    aeval st a = aeval st' a) /\
  (forall b,
    is_empty (vars_bexp b) = true ->
    beval st b = beval st' b).
Proof.
  intros st st'. apply aexp_bexp_mutind; simpl; intros; try reflexivity; try discriminate.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite !is_empty_app in H2. apply andb_prop in H2. destruct H2. apply andb_prop in H3. destruct H3.
    apply H in H2. apply H0 in H3. apply H1 in H4. now rewrite H2, H3, H4.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
  + apply H in H0. now rewrite H0.
  + rewrite is_empty_app in H1. apply andb_prop in H1. destruct H1. apply H in H1. apply H0 in H2. now rewrite H1, H2.
Qed.

Lemma aeval_no_vars : forall st st' a,
  is_empty (vars_aexp a) = true ->
  aeval st a = aeval st' a.
Proof. intros st st' a H. now eapply eval_no_vars. Qed.

Lemma beval_no_vars : forall st st' b,
  is_empty (vars_bexp b) = true ->
  beval st b = beval st' b.
Proof. intros st st' b H. now eapply eval_no_vars. Qed.

Lemma ideal_misspeculated_unwinding_one_step : forall c ds st1 st2 ast1 ast2 stt1 stt2 astt1 astt2 os1 os2 c1 c2,
  <((c, st1, ast1, true))> -->i_ds^^os1 <((c1, stt1, astt1, true))> ->
  <((c, st2, ast2, true))> -->i_ds^^os2 <((c2, stt2, astt2, true))> ->
  os1 = os2 /\ c1 = c2.
Proof.
  intros. remember true as b. rewrite Heqb in H at 2, H0 at 2. remember true as b'.
  rewrite Heqb' in Heqb.
  revert Heqb Heqb' st2 ast2 c2 os2 stt2 astt2 H0. induction H; intros.
  + now invert H0.
  + invert H0.
    - apply IHideal_eval_small_step in H12; try tauto.
      now destruct H12; subst.
    - inversion H.
  + now invert H0.
  + invert H1. destruct (is_empty (vars_bexp be)) eqn:Hempty; simpl; [|tauto].
    apply beval_no_vars with (st:=st) (st':=stt2) in Hempty. now rewrite Hempty.
  + invert H1. destruct (is_empty (vars_bexp be)) eqn:Hempty; simpl; [|tauto].
    apply beval_no_vars with (st:=st) (st':=stt2) in Hempty. now rewrite Hempty.
  + now invert H0.
  + invert H1. destruct (is_empty (vars_aexp ie)) eqn:Hempty; simpl; [|tauto].
    apply aeval_no_vars with (st:=st) (st':=st2) in Hempty. now rewrite Hempty.
  + invert H3. split; [|tauto]. do 2 f_equal. now apply aeval_no_vars.
  + invert H2. destruct (is_empty (vars_aexp ie)) eqn:Hempty; simpl; [|tauto].
    apply aeval_no_vars with (st:=st) (st':=stt2) in Hempty. now rewrite Hempty.
  + invert H4. split; [|tauto]. do 2 f_equal. now apply aeval_no_vars.
Qed.

Lemma ideal_misspeculated_unwinding : forall c ds st1 st2 ast1 ast2 stt1 stt2 astt1 astt2 os1 os2 c1 c2,
  <((c, st1, ast1, true))> -->i*_ds^^os1 <((c1, stt1, astt1, true))> ->
  <((c, st2, ast2, true))> -->i*_ds^^os2 <((c2, stt2, astt2, true))> ->
  os1 = os2.
Proof.
  intros c ds st1 st2 ast1 ast2 stt1 stt2 astt1 astt2 os1 os2 c1 c2 H.
  remember true as b. rewrite Heqb in H at 2. remember true as b'.
  rewrite Heqb' in Heqb.
  revert Heqb Heqb' st2 ast2 stt2 astt2 os2 c2. induction H; intros.
  - symmetry. apply length_zero_iff_nil. apply multi_ideal_obs_length in H. now rewrite <- H.
  - invert H1.
    + symmetry in H7. apply app_eq_nil in H7. destruct H7; subst.
      apply multi_ideal_obs_length in H0. apply ideal_eval_small_step_obs_length in H.
      apply length_zero_iff_nil. now rewrite app_length, <- H, <- H0.
    + assert (b' = true) by now apply ideal_eval_small_step_spec_bit_monotonic in H. subst.
      assert (b'0 = true) by now apply ideal_eval_small_step_spec_bit_monotonic in H3. subst.
      assert(Eqds : ds0 = ds1).
      { apply app_eq_prefix in H2. apply prefix_eq_length; [|tauto].
        do 2 (erewrite ideal_eval_small_step_obs_length; [|eassumption]).
        eapply ideal_small_step_obs_length; eassumption. } subst.
      apply app_inv_head in H2. subst.
      assert(HH:os3 = os1 /\ c'0 = c') by (eapply ideal_misspeculated_unwinding_one_step; eassumption).
      destruct HH; subst. f_equal.
      eapply IHmulti_ideal; eauto.
Qed.

Lemma multi_ideal_single_force_direction :
  forall c st ast ct astt stt os,
    <(( c, st, ast, false ))> -->i*_ [DForce]^^ os <((ct, stt, astt, true))> ->
    exists cm1 stm1 astm1 cm2 stm2 astm2,
    <((c, st, ast, false))> -->i*_[]^^[] <((cm1, stm1, astm1, false))> /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os <((cm2, stm2, astm2, true))> /\
    <((cm2, stm2, astm2, true))>  -->i*_[]^^[] <((ct, stt, astt, true))>.
Proof.
  intros c st ast ct astt stt os Hev. remember [DForce] as ds eqn:Eqds.
  remember false as b eqn:Eqb; remember true as bt eqn:Eqbt.
  induction Hev; try discriminate; subst.
  assert (L: ds1 = [] \/ ds2 = []).
  { destruct ds1; auto; destruct ds2; auto. inversion Eqds.
    apply app_eq_nil in H2 as [_ Contra]. inversion Contra. }
  destruct L as [L | L]; subst; simpl in *.
  - assert (Hb': b' = false).
    { destruct b' eqn:Eqb'; auto. apply ideal_eval_small_step_spec_needs_force in H. discriminate H. }
    apply IHHev in Eqds; auto; subst.
    destruct Eqds as [cm1 [stm1 [astm1 [cm2 [stm2 [astm2 [H1 [H2 H3] ] ] ] ] ] ] ].
    exists cm1, stm1, astm1, cm2, stm2, astm2.
    assert (os1 = []). { apply length_zero_iff_nil. apply ideal_eval_small_step_obs_length in H. now rewrite <- H. } subst.
    split; [| split]; auto.
    replace ([] :dirs) with ([]++[] :dirs) by (apply app_nil_l).
    rewrite <- app_nil_l with (l:=[]:obs). eapply multi_ideal_trans; eauto.
  - rewrite app_nil_r in Eqds. subst.
    assert (Hb': b' = true).
    { destruct b' eqn:Eqb'; auto. apply ideal_eval_small_step_final_spec_bit_false with (d:=DForce) in H; simpl; auto.
      inversion H. } subst.
    exists c; exists st; exists ast; exists c'; exists st'; exists ast'.
    assert (os2 = []). { apply length_zero_iff_nil. apply multi_ideal_obs_length in Hev. now rewrite <- Hev. } subst.
    rewrite !app_nil_r.
    split; [| split]; auto.
    apply multi_ideal_refl.
Qed.

(* This lemma was replaced by [ideal_exec_split_v2] and is here only as an
   initial idea on how to prove the new version. *)
Lemma ideal_exec_split : forall c st ast ds stt astt os ds1 ds2 cm3,
  <((c, st, ast, false))> -->i*_ds^^os <((cm3, stt, astt, true))> ->
  (forall d, In d ds1 -> d = DStep) ->
  ds = ds1 ++ [DForce] ++ ds2 ->
  exists cm1 stm1 astm1 os1 cm2 stm2 astm2 os2 os3,
    <((c, st, ast, false))> -->i*_ds1^^os1 <((cm1, stm1, astm1, false))>  /\
    <((cm1, stm1, astm1, false))>  -->i_[DForce]^^os2 <((cm2, stm2, astm2, true))> /\
    <((cm2, stm2, astm2, true))> -->i*_ds2^^os3  <((cm3, stt, astt, true))> /\
    os = os1 ++ os2 ++ os3.
Proof.
  intros.
  apply ideal_eval_small_step_split_by_dirs with (ds1:=ds1) (ds2:=[DForce]++ds2) in H; [|assumption].
  do 7 destruct H. destruct H2. subst.
  assert (x2 = false). { destruct x2; [|reflexivity]. now apply multi_ideal_spec_needs_force, H0 in H. } subst.
  apply ideal_eval_small_step_split_by_dirs with (ds1:=[DForce]) (ds2:=ds2) in H2; [|reflexivity].
  destruct H2. do 6 destruct H1. destruct H2. subst.
  assert (x7 = true). { destruct x7; [reflexivity|]. apply multi_ideal_final_spec_bit_false with (d:=DForce) in H1; [discriminate|now left]. } subst.
  eapply multi_ideal_single_force_direction in H1. do 7 destruct H1. destruct H3.
  do 9 econstructor. split.
  { rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds1). eapply multi_ideal_combined_executions; eassumption. }
  repeat econstructor; [eassumption|]. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds2). eapply multi_ideal_combined_executions; eassumption.
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
  ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2 Hev1 Hev2.
  eapply ideal_eval_spec_bit_deterministic in Hev1 as SameB; try eassumption. subst.
  destruct bt1 eqn:Eqbt1.
  - (* with mis-speculation *)
    eapply ideal_dirs_split in Hev1 as L.
    destruct L as [ds1 [ds2 [Hds1 Heq] ] ]. subst.
    eapply ideal_exec_split in Hev1; eauto.
    destruct Hev1 as [cm1 [stm1 [astm1 [os1_1 [cm2 [stm2 [astm2 [os1_2 [os1_3 [Hsmall1 [Hone1 [Hbig1 Hos1] ] ] ] ] ] ] ] ] ] ] ].
    eapply ideal_exec_split in Hev2; eauto.
    destruct Hev2 as [cm1' [stm1' [astm1' [os2_1 [cm2' [stm2' [astm2' [os2_2 [os2_3 [Hsmall2 [Hone2 [Hbig2 Hos2] ] ] ] ] ] ] ] ] ] ] ].
    assert (Hlen2: length os1_1 = length os2_1).
    { apply multi_ideal_obs_length in Hsmall1, Hsmall2. congruence. }
    assert (L: os1_1 = os2_1).
    { apply multi_ideal_no_spec in Hsmall1, Hsmall2; auto.
      eapply Hsec in Hsmall1. eapply Hsmall1 in Hsmall2 as Hpre.
      apply prefix_eq_length in Hpre; auto. } subst.
    assert (L : cm1' = cm1).
    { eapply multi_ideal_no_spec in Hsmall1, Hsmall2; eauto.
      eapply multi_ideal_lock_step; eauto.
      all: intro; (do 3 destruct H). all:eapply seq_to_ideal in H; simpl in *.
      2: assert (os1_2 = []) by now (apply length_zero_iff_nil; eapply ideal_small_step_obs_length in Hone1; eauto; rewrite <- Hone1).
      1: assert (os2_2 = []) by now (apply length_zero_iff_nil; eapply ideal_small_step_obs_length in Hone2; eauto; rewrite <- Hone2).
      all:subst. 2: now eapply ideal_eval_small_step_obs_length in Hone1.
      now eapply ideal_eval_small_step_obs_length in Hone2. } subst.
    assert (Hsec2: seq_same_obs cm1 stm1 stm1' astm1 astm1').
    { apply multi_ideal_no_spec in Hsmall1, Hsmall2; auto.
      eapply multi_seq_preserves_seq_same_obs; eauto. }
    assert (L: cm2 = cm2').
    { eapply ideal_small_step_com_deterministic in Hone2; eauto. } subst.
    eapply ideal_one_step_force_obs in Hone2; eauto.
    eapply ideal_misspeculated_unwinding in Hbig1; eauto. congruence.
  - (* without mis-speculation *)
    (* LATER: this case is similar to the start of the more interesting case
              above; we can likely share more (e.g. use the same obs_length lemma) *)
    assert (Hds: forall d, In d ds -> d = DStep).
    { intros; eapply ideal_eval_final_spec_bit_false in Hev1; eauto. }
    apply multi_ideal_obs_length in Hev1 as Hos1.
    apply multi_ideal_obs_length in Hev2 as Hos2.
    rewrite Hos1 in Hos2. clear Hos1. unfold seq_same_obs in Hsec.
    eapply multi_ideal_no_spec in Hev1; try assumption.
    eapply multi_ideal_no_spec in Hev2; try assumption.
    assert(H:prefix os1 os2 \/ prefix os2 os1). { eapply Hsec; eassumption. }
    apply prefix_eq_length; assumption.
Qed.

(* LATER: Strengthen the conclusion so that our theorem is termination sensitive
   (and also error sensitive) by looking at prefixes there too. *)

(* HIDE: YH:This pairs with the new bcc lemma definition I suggested above.
Theorem ultimate_slh_relative_secure :
  forall c st1 st2 ast1 ast2,
    (* some extra assumptions needed by slh_bcc *)
    unused_prog p ->
    In c p ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure ultimate_slh c st1 st2 ast1 ast2.
Proof.

Question: Do we need to define relative security for programs?
          I think that in languages like Imp that we're dealing with,
          we could define it as satisfying relative security for all commands in the program.
          Though for languages with a structure that starts from main, like C,
          we would need to define it differently.
 *)

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
    astt1 astt2 bt1 bt2 os1 os2 c1 c2 Hev1 Hev2.
  apply ultimate_slh_bcc in Hev1; try assumption. destruct Hev1 as [c1' Hev1].
  apply ultimate_slh_bcc in Hev2; try assumption. destruct Hev2 as [c2' Hev2].
  eapply (ideal_eval_relative_secure c st1 st2); eassumption.
Qed.
