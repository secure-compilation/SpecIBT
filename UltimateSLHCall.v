(** * UltimateSLH: Relative Security Against Speculation Attacks*)

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

Inductive seq_eval_small_step (p:prog) :
    com -> state -> astate ->
    com -> state -> astate -> obs -> Prop :=
  | SSM_Asgn  : forall st ast e n x,
      aeval st e = n ->
      p |- <((x := e, st, ast))> -->^[] <((skip, x !-> n; st, ast))>
  | SSM_Seq : forall c1 st ast os c1t stt astt c2,

      p |- <((c1, st, ast))>  -->^os <((c1t, stt, astt))>  ->
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
      aeval st e = i ->
      nth_error p i = Some c ->
      p |- <((call e, st, ast))> -->^[OCall i] <((c, st, ast))>

  where "p |- <(( c , st , ast ))> -->^ os  <(( ct ,  stt , astt ))>" :=
    (seq_eval_small_step p c st ast ct stt astt os).

Reserved Notation
   "p '|-' '<((' c , st , ast '))>' '-->*^' os '<((' ct , stt , astt '))>'"
   (at level 40, c custom com at level 99, ct custom com at level 99,
    st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_seq (p:prog) (c:com) (st:state) (ast:astate) :
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

Inductive spec_eval_small_step (p:prog) :
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
      aeval st e = i ->
      nth_error p i = Some c ->
      p |- <((call e, st, ast, b))> -->_[DStep]^^[OCall i] <((c, st, ast, b))>
  | SpecSM_Call_F : forall e i j c st ast b,
      aeval st e = i ->
      i <> j ->
      nth_error p j = Some c ->
      p |- <((call e, st, ast, b))> -->_[DForceCall j]^^[OForceCall] <((c, st, ast, true))>

  where "p |- <(( c , st , ast , b ))> -->_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (spec_eval_small_step p c st ast b ct stt astt bt ds os).

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_spec (p:prog) (c:com) (st:state) (ast:astate) (b:bool) :
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

Definition relative_secure (p:prog) (trans : com -> com)
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

(*  *)
Fixpoint ultimate_slh (c:com) :=
  (match c with
   | <{{skip}}> => <{{(*"from_call" := 0;*) skip}}>
   | <{{x := e}}> => <{{(*"from_call" := 0;*) x := e}}>
   | <{{c1; c2}}> => <{{ (*"from_call" := 0;*) ultimate_slh c1; ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      let be' := if is_empty (vars_bexp be) then be (* optimized *)
                                            else <{{"b" = 0 && be}}> in
        <{{if be' then "b" := be' ? "b" : 1; ultimate_slh c1
          else "b" := be' ? 1 : "b"; (*"from_call" := 0;*) ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      let be' := if is_empty (vars_bexp be) then be (* optimized *)
                                            else <{{"b" = 0 && be}}> in
        <{{while be' do "b" := be' ? "b" : 1; (*"from_call" := 0;*) ultimate_slh c end;
           "b" := be' ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
      let i' := if is_empty (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                          else <{{("b" = 1) ? 0 : i}}> in
        <{{(*"from_call" := 0;*) x <- a[[i']]}}>
  | <{{a[i] <- e}}> =>
      let i' := if is_empty (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                          else <{{("b" = 1) ? 0 : i}}> in
        <{{(* "from_call" := 0;*) a[i'] <- e}}> (* <- Doing nothing here in the is_empty (vars_aexp i) case okay for Spectre v1,
                   but problematic for return address or code pointer overwrites *)

  | <{{call e}}> =>
      let e' := if is_empty (vars_aexp e) then e 
                                          else <{{("b" = 1) ? 0 : e}}> in
        <{{"callee" := e'; (*"from_call" := 1;*) call e'}}>

  end)%string.

Definition add_index {a:Type} (xs:list a) : list (nat * a) :=
  combine (seq 0 (length xs)) xs.

Definition ultimate_slh_prog (p:prog) :=
  map (fun p =>
    let '(i,c) := p in
    (* <{{ "b" := ("from_call" = 1 && "callee" <> ANum i) ? 1 : "b"; ultimate_slh c }}>)
       (add_index p).*)
    <{{"b" := ("callee" = ANum i)? "b" : 1; ultimate_slh c}}>
       ) (add_index p).

Compute (add_index [<{{call 1}}>;<{{X:=40}}>;<{{Y:=2}}>;<{{Z:=X+Y}}>]).
(* = [
      (0, <{{ call 1 }}>); 
      (1, <{{ "X" := 40 }}>); 
      (2, <{{ "Y" := 2 }}>);
      (3, <{{ "Z" := "X" + "Y" }}>)
     ] : list (nat * com) *)

Compute (ultimate_slh_prog [<{{call 1}}>;<{{X:=40}}>;<{{Y:=2}}>;<{{Z:=X+Y}}>]).
(*  
   [<{{ "b" := ("callee" = 0) ? "b" : 1; "callee" := 1; call 1 }}>; <-- fine if "callee" initialized to 0
   <{{ "b" := ("callee" = 1) ? "b" : 1; "X" := 40 }}>; <-- fine because "callee" would have been set to 1 
                                                           as the first part of <{{ call 1 }}> sequence
   <{{ "b" := ("callee" = 2) ? "b" : 1; "Y" := 2 }}>; <-- not fine because "callee" will still be 1 but 
                                                          now we're checking whether it's 2. The spec flag 
                                                          will be set incorrectly.
   <{{ "b" := ("callee" = 3) ? "b" : 1; "Z" := "X" + "Y" }}>] 

This program would have had false positives for speculation, and the ending condition for bcc where 
"b" must match b would not have been met. The least invasive solution I could come up with for now 
was to add a "from_call" variable that gets set to 1 when current command is call and 0 otherwise.
Then before each command, there's now a check where if the previous command was a call AND the 
call wasn't going to the correct index, we set the spec flag accordingly. Otherwise we leave it alone 
(this way we avoid having to add updates to "callee" so that it matches the next sequential index 
when there's no call command involved).

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

Inductive ideal_eval_small_step (p:prog):
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
      (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i ->
      nth_error p i = Some c ->
      p |- <((call e, st, ast, b))> -->i_[DStep]^^[OCall i] <((c, st, ast, b))>
  | ISM_Call_F : forall e i j c st ast b,
      (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i ->
      i <> j -> 
      nth_error p j = Some c ->     
      p |- <((call e, st, ast, b))> -->i_[DForceCall j]^^[OForceCall] <((c, st, ast, true))>

    where "p |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step p c st ast b ct stt astt bt ds os).

(* HIDE: This one now has again `_U` cases because of out-of-bounds array
   accesses at constant indices. Since the array sizes are also statically
   known, we could easily reject such programs statically.  *)

Reserved Notation
  "p '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (p:prog) (c:com) (st:state) (ast:astate) (b:bool) :
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
  try (right; exists j); auto.
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
  + specialize (Hds (DForceCall j)). discriminate Hds. now left.
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

Lemma seq_same_obs_com_if (p:prog) : forall be ct cf st1 st2 ast1 ast2,
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

Lemma seq_same_obs_com_seq (p:prog) : forall c1 c2 st1 st2 ast1 ast2,
  seq_same_obs p <{{ c1; c2 }}> st1 st2 ast1 ast2 ->
  seq_same_obs p c1 st1 st2 ast1 ast2.
Proof.
  intros c1 c2 st1 st2 ast1 ast2 Hsec. unfold seq_same_obs.
  intros stt1 stt2 astt1 astt2 os1 os2 ct1 ct2 Hev1 Hev2.
  eapply multi_seq_add_snd_com in Hev1, Hev2. eapply Hsec in Hev2; eauto.
Qed.

Lemma ideal_one_step_force_obs (p:prog) :
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

Lemma ideal_one_step_forcecall_obs (p:prog) :
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

Lemma ideal_unused_overwrite_one_step (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  p |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->i_ds^^os <((c', X !-> n; st', ast', b'))> /\ unused X c'.
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
  
Lemma ideal_unused_overwrite (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  p |- <((c, st, ast, b))> -->i*_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((c', X !-> n; st', ast', b'))>.
Proof.
  intros. induction H1; [constructor|].
  eapply ideal_unused_overwrite_one_step in H1; [|eassumption|eassumption]. destruct H1.
  econstructor; [eassumption|tauto].
Qed.

Lemma ideal_unused_update (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  p |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((c', X !-> n; st', ast', b'))> ->
  p |- <((c, st, ast, b))> -->i*_ds^^os <((c', X !-> st X; st', ast', b'))>.
Proof.
  intros. rewrite <- (t_update_same _ st X) at 1.
  eapply ideal_unused_overwrite with (X:=X) (n:=(st X)) in H1; [ |assumption|assumption].
  now rewrite !t_update_shadow in H1.
Qed.

Lemma spec_unused_overwrite_one_step (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused_prog X p ->
  unused X c ->
  p |- <((c, st, ast, b))> -->_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->_ds^^os <((c', X !-> n; st', ast', b'))> /\ unused X c'.
Proof.
  intros. remember (unused_prog X p) as unused_p. induction H1.
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

Lemma spec_unused_overwrite (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused X c ->
  unused_prog X p ->
  p |- <((c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  p |- <((c, X !-> n; st, ast, b))> -->*_ds^^os <((c', X !-> n; st', ast', b'))>.
Proof.
  intros. induction H1; [constructor|].
  eapply spec_unused_overwrite_one_step in H1; [|eassumption|eassumption]. destruct H1.
  econstructor; [eassumption|tauto].
Qed.

Lemma spec_unused_update (p:prog) : forall st ast b ds c c' st' ast' b' os X n,
  unused X c ->
  unused_prog X p ->
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

Lemma spec_eval_preserves_nonempty_arrs (p:prog) : forall c c' st ast b ds st' ast' b' os,
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

Lemma ideal_eval_preserves_nonempty_arrs (p:prog) : forall c c' st ast b ds st' ast' b' os,
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

Require Import Coq.Arith.Wf_nat.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Wellfounded.Inverse_Image.

Definition measure (c : com) (ds : dirs) : nat * nat :=
  (length ds, com_size c).

Definition lex_ord (cds1 cds2: com * dirs) : Prop :=
  lex_nat_nat (measure (fst cds1) (snd cds1)) (measure (fst cds2) (snd cds2)).

(* Lemma lex_ord_wf: *)
(*   well_founded lex_ord. *)
(* Proof. *)
  
(*   revert H. intros. inv H. econstructor. intros. *)
(*   Print well_founded_induction_type. *)
(* Admitted.  *)
(* lex_nat_nat_wf: well_founded lex_nat_nat
 *)
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
  { instantiate (1:= lex_ord). unfold lex_ord. admit. }
  intros. subst f. eapply H. intros.
  - intros x. instantiate (1:= (fun cds1 cds2 => lex_nat_nat (measure (fst  ds') (measure c ds
    
  
  { instantiate (1:= f).  }
(*   unfold lex_ord. subst f. intros. *)
(*   destruct x; simpl in *. *)
(*   eapply H. intros. *)
(*   specialize (H0 (c', ds')). simpl in H0. auto. *)
  (* Qed. *)
Admitted.

Section EXAMPLE.

Variable p: prog.

Lemma unused_prog_unused :
  forall (p : prog) (c : com) (X : string), 
    In c p -> unused_prog X p -> unused X c.
Proof.
  intros. unfold unused_prog in H0. rewrite Forall_forall in H0. 
  specialize H0 with (x:=c). apply H0 in H; auto.
Qed.

(* Lemma unused_prog_unused :
  forall c, In c p -> unused_prog "b" p -> unused "b" c.
Proof.
  intros. unfold unused_prog in H0. rewrite Forall_forall in H0. 
  specialize H0 with (x:=c). apply H0 in H; auto.
   Qed.*)

Definition Property (c:com) (ds: dirs) := forall st ast (b b':bool) c' st' ast' os,
  nonempty_arrs ast ->
  unused_prog "b" p ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  p |- <(( (ultimate_slh c), st, ast, b ))> -->*_ ds ^^ os <(( c', st', ast', b' ))> ->
  exists c'' : com,
    p |- <(( c, st, ast, b ))> -->i*_ ds ^^ os <(( c'', "b" !-> st "b"; st', ast', b' ))> /\
    (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0)).

Lemma induction_example : forall c ds, Property c ds.
Proof.
  intros c ds. apply lex_ind2 with (c:=c) (ds:=ds). clear.
  intros c ds IH.
  destruct c; simpl in *.
  8:{
    red. intros. invert H3.
    { admit. (* star refl *) }
    simpl in H4.
    invert H4. simpl in *.
    unfold Property in IH.
    admit. }
Abort.

End EXAMPLE.

Ltac measure1 := unfold measure, lex_nat_nat_spec; simpl; try (rewrite !app_length); simpl; lia.
Ltac strs_neq := unfold not; intros; discriminate.

(* exploring how to get from uslh_prog p in premise to p in conclusion
   (commented out so I can look at the initial conditions motivating it again)*)

(* Lemma ultimate_slh_prog_length :
  forall p, length (ultimate_slh_prog_aux p) = length p.
Proof.
  intros. unfold ultimate_slh_prog.
(*   rewrite length_map. *)
(*   unfold add_index. *)
(*   rewrite length_combine. *)
(*   rewrite length_seq. rewrite min_id. reflexivity. *)
(* Qed. *)
    *)

(* Lemma combine_app_comm :
  forall {X : Type} (x : X) (l : list X),
  combine (seq 0 (Datatypes.length ([x] ++ l))) ([x] ++ l) = 
  (combine (seq 0 (Datatypes.length [x])) [x]) ++
  (combine (seq 1 (Datatypes.length l)) l).
Proof.
  intros. reflexivity.
   Qed. *)

(* Lemma ultimate_slh_prog_contents:
  forall p cmd e st,
  nth_error (ultimate_slh_prog p) e = Some cmd ->
  exists c', cmd = (<{{("b" := ("callee" = (aeval st e)) ? "b" : 1); (ultimate_slh c') }}>).
Proof.
  induction p; intros.
  - simpl. unfold ultimate_slh_prog in H. 
    unfold add_index in H. simpl in H.
    induction e; discriminate.
  
  - destruct e.
    + simpl in H. injection H. intros.
      subst. simpl. exists a. reflexivity.
      (* rewrite <- H0. admit. *)
    + unfold ultimate_slh_prog in *. simpl.
      unfold add_index in *. simpl in H.
      apply IHp with (st:=st).           
   Admitted. *)

(* - previous attempts

unfold ultimate_slh_prog in H. *)
  (*   unfold add_index in H. *)
    
  (*   assert (ultimate_slh_prog (a :: p) = (<{{ "b" := ("callee" =  *)
  (*   (aeval st e)) ? "b" : 1; (ultimate_slh a) }}>) :: ultimate_slh_prog p). *)
  (*   { assert (a :: p = [a] ++ p). { simpl; reflexivity. } *)
  (*     rewrite H0. unfold ultimate_slh_prog. unfold add_index. *)
      
  (*     rewrite combine_app_comm.  *)
  (*     rewrite map_app. simpl.  *)
  (*     rewrite H0 in H. unfold ultimate_slh_prog in H. *)
  (*     (* remember (fun '(i, c) => <{{ "b" := ("callee" = i) ? "b" : 1; (ultimate_slh c) }}>) as f. *)
  (*        rewrite <- Heqf in H. why doesn't it see the subterm? *) admit. *)

(* I'll come back to this assert, but for the moment it seemed easier to 
       prove this by searching up relevant theorems for nth_error and 
       map and seq and trying to transform things that way. Until I 
       ran into the p issue. *)
      (* assert (ultimate_slh_prog (a :: p) = (<{{ "b" := ("callee" = (aeval st e)) ? "b" : 1; (ultimate_slh a) }}>) :: ultimate_slh_prog p).
    { unfold ultimate_slh_prog, add_index. simpl. apply nth_error_split in H.
       destruct H as [l1 H]. destruct H as [l2 H]. } *)

(* Lemma uslh_prog_to_uslh_com' : 
  forall p c e st,
  nth_error (ultimate_slh_prog p) e = Some (<{{("b" := ("callee" = (aeval st e)) ? "b" : 1); 
                     (ultimate_slh c) }}>) ->
  nth_error p e = Some c.
Proof.
  induction p; intros.
  - destruct e; try discriminate.
  - destruct e.
    + simpl in *. 
     (* now I need to prove things about uslh_prog (a :: p) vs p ?? *)
   Admitted.*)

(* If I'm right about uslh_prog issue, add unused for "from_call".
   Also try removing uslh_prog p and add the actual 
   annotation / sequence command on c in speculative premise (maybe unfolding it in advance 
   will make it easier to see where I'm stuck, or easier to push it through) *)
Lemma ultimate_slh_bcc_generalized (p:prog) : forall c ds st ast (b b' : bool) c' st' ast' os,
  nonempty_arrs ast ->
  unused_prog "b" p ->
  unused "b" c ->
  unused_prog "callee" p ->
  unused "callee" c ->
  st "b" = (if b then 1 else 0) ->
  (* isn't uslh_prog already applying uslh to each command c? is having both here correct? *)
  (ultimate_slh_prog p) |- <((ultimate_slh c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
      exists c'', p |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "callee" !-> st "callee"; "b" !-> st "b"; st', ast', b'))>
  /\ (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0)). (* <- generalization *)
Proof.
  intros c ds. apply lex_ind with (c:=c) (ds:=ds). clear.
  intros c ds IH. intros until os. 
  intros ast_arrs unused_p unused_c unused_p_callee unused_c_callee st_b st_st'.
  (* st_st' is target multistep *)
  invert st_st'.
  (* multi_spec_refl *)
  { repeat rewrite t_update_same. eexists. split; [apply multi_ideal_refl|].
    split; [|tauto]. now destruct c. }
  (* multi_spec_trans *)
  (* case analysis on commands, then invert single target step *)
  
  destruct c; (*simpl in *;*) invert H.
  11 : { (* Call *)
        (* hypotheses: single and multi spec, hardened prog 
          h12: single, invert first. h0: multi. *)
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
            (* trans: we now have H: tgt single step call f --> c'0
               and H0: tgt multi, ds os not concat, c'0 --> c'  *)
            - inv H. (* produces 2 cases: DStep++ds2, OCall++os2, call f --> c''
                                      and DForceCall++ds2, OForceCall++os2, call f --> c'' *)
              + (* DStep *)
                inv H0. (* inverting multi produces refl and trans cases.
                           refl: ds2/os2 instantiated as [] 
                           trans: ds2/os2 instantiated as ds1++ds0/os1++os0 *)
                (* reflexive : []. 0 steps take place after call step. *)
                * rewrite t_update_neq; [|strs_neq]. 
                  rewrite t_update_permute; [|strs_neq].
                  rewrite t_update_shadow. 
                  rewrite aeval_unused_update with (n:=(aeval st f)); auto.
                  rewrite aeval_unused_update with (n:=(aeval st f)) in H3; auto.
                  rewrite t_update_permute; [|strs_neq]. 
                  exists c'. split; try split; auto.
                  do 2 rewrite t_update_same. apply multi_ideal_trans with
                    (c':=c') (st':=st) (ast':=ast') (b':=b');
                    [|apply multi_ideal_refl].
                  apply ISM_Call; [rewrite Hf; auto|].
                  (* uslh_prog p ≠ p. *)
                  admit.

                (* transitive: ds1++ds0 *)
                * rewrite aeval_unused_update with (n:=(aeval st f)); auto.
                  rewrite aeval_unused_update with (n:=(aeval st f)) in H3; auto.
                  
                  (* here again the problem of uslh c ≠ c 

                     exists c'. split; try split; auto.
                  -- eapply multi_ideal_trans.
                     ++ eapply ISM_Call; [rewrite Hf; eauto|]. *)
                  (* assert (exists c'', c'0 = <{{ "b" := ("callee" = (aeval st f)) ? "b" : 1; 
                     (ultimate_slh c'') }}>).
                  { admit. (* H3 *) }
                  destruct H0 as [c'' COM].
                     subst.*)

              + (* DForceCall *) admit.
          }
      (* no optimization *)
      inv H1.
      (* refl case *)
      { exists <{{ call f }}>. simpl. split.
        2:{ intros. inv H. }
        rewrite t_update_permute; [|unfold not; intros; discriminate].
        rewrite t_update_shadow. do 2 rewrite t_update_same. constructor. }
      (* transitive *)
      inv H; simpl.
      (* DStep/OCall *)
      * (* simpl in *. *) Opaque unused. simpl in *.
        destruct b'0 eqn:Hmsf; rewrite st_b in *.
        (* already misspeculating *) 
        { rewrite Nat.eqb_refl in *.
          rewrite t_update_neq in *; try discriminate.
          rewrite st_b in *. rewrite Nat.eqb_refl in *.
          destruct p; simpl in *.
          (* program is empty list *)
          { inv H3.  }
          (* program is nonempty list *)
          inv H3. inv H0.
          { rewrite t_update_permute; try (unfold not; intros; discriminate).
            rewrite t_update_shadow. rewrite t_update_permute; try (unfold not; intros; discriminate).
            rewrite <- st_b. rewrite t_update_same. rewrite t_update_same.
            rewrite st_b. unfold unused_prog in unused_p_callee.
            admit. }
          inv H. inv H12. inv H1.
          { simpl. rewrite t_update_neq; [|strs_neq]. eapply IH in ast_arrs; eauto.
            - destruct ast_arrs as [c'' A]. destruct A as [STEPS SKIP].
              exists c''. split; auto; [|intros; discriminate]. 
              rewrite <- st_b. rewrite t_update_shadow. rewrite t_update_permute; [|strs_neq].
              rewrite t_update_shadow. rewrite t_update_permute; [|strs_neq]. eapply STEPS.
            - admit. (* uh oh *)
            - auto.
            - simpl. rewrite Hf. admit.
          }
          inv H.
          { inv H12. }
          simpl in *. rewrite t_update_neq in H0; try discriminate.
          eapply IH in H0; auto; cycle 1.
          { measure1. }
          { inv unused_p. auto. }
          { inv unused_p_callee. auto. }
          { destruct H0 as [c'' A]. destruct A as [STEPS SKIP].
            exists c''. split; auto. fold_cons. econstructor 2.
            { econstructor.
              - rewrite Hf. simpl. auto.
              - simpl. auto. }
            rewrite t_update_eq in *; try discriminate.
            rewrite t_update_neq in *; try discriminate.
            rewrite t_update_eq in *; try discriminate.
            rewrite t_update_permute in STEPS; [|unfold not; intros; discriminate].
            eapply ideal_unused_update in STEPS; eauto.
            2:{ apply unused_prog_unused with (p:=(c :: p)); auto.
                unfold In. left; reflexivity. }
            rewrite t_update_permute in STEPS; [|unfold not; intros; discriminate].
            rewrite t_update_neq in *; try discriminate.
            rewrite t_update_permute; [|unfold not; intros; discriminate].
            rewrite t_update_same in STEPS. rewrite st_b in STEPS. auto.
          }
        }
        (* not yet misspeculated *)
        { simpl. simpl in H0, H3. 
          admit. }
      (* DForceCall/OForceCall *)
      * simpl in *. admit. }
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
