(** * FvSLH: Flexible Value SLH *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps SpecCT FiSLH UltimateSLH_optimized.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

(* Combining Selective Value SLH and Ultimate SLH *)

Fixpoint flex_vslh (P :pub_vars) (c:com) : com :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ flex_vslh P c1; flex_vslh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{if be' then "b" := be' ? "b" : 1; flex_vslh P c1
                   else "b" := be' ? 1 : "b"; flex_vslh P c2 end}}>
  | <{{while be do c end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{while be' do "b" := be' ? "b" : 1; flex_vslh P c end;
             "b" := be' ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    let i' := if label_of_aexp P i then i else <{{("b" = 1) ? 0 : i}}> in
    if P x && label_of_aexp P i then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}> else <{{x <- a[[i']]}}>
  | <{{a[i] <- e}}> => let i' := if label_of_aexp P i then i else <{{("b" = 1) ? 0 : i}}> in
                       <{{a[i'] <- e}}>
  end)%string.

(** * Ideal small-step evaluation *)

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval_small_step :
    pub_vars -> com -> state -> astate -> bool ->
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | ISM_Asgn  : forall P st ast b e n x,
      aeval st e = n ->
      P |- <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))>
  | ISM_Seq : forall P c1 st ast b ds os c1t stt astt bt c2,
      P |- <((c1, st, ast, b))> -->i_ds^^os <((c1t, stt, astt, bt))>  ->
      P |- <(((c1;c2), st, ast, b))> -->i_ds^^os <(((c1t;c2), stt, astt, bt))>
  | ISM_Seq_Skip : forall P st ast b c2,
      P |- <(((skip;c2), st, ast, b))> -->i_[]^^[] <((c2, st, ast, b))>
  | ISM_If : forall P be ct cf st ast b c' b' l,
      P |-b- be \in l ->
      b' = (l || negb b) && beval st be ->
      c' = (if b' then ct else cf) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))>
  | ISM_If_F : forall P be ct cf st ast b c' b' l,
      P |-b- be \in l ->
      b' = (l || negb b) && beval st be ->
      c' = (if b' then cf else ct) ->
      P |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))>
  | ISM_While : forall P be c st ast b,
      P |- <((while be do c end, st, ast, b))> -->i_[]^^[]
            <((if be then c; while be do c end else skip end, st, ast, b))>
  | ISM_ARead : forall P x a ie st ast (b :bool) i v li,
      P |-a- ie \in li ->
      (if (negb li) && b then 0 else (aeval st ie)) = i ->
      (if P x && li && b then 0 else nth i (ast a) 0) = v ->
      i < length (ast a) ->
      P |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i]
            <((skip, x !-> v; st, ast, b))>
  | ISM_ARead_U : forall P x a ie st ast i a' i' v,
      aeval st ie = i ->
      P |-a- ie \in public ->
      (if P x then 0 else nth i' (ast a') 0) = v ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i]
            <((skip, x !-> v; st, ast, true))>
  | ISM_Write : forall P a ie e st ast (b :bool) i n l i',
      aeval st e = n ->
      aeval st ie = i ->
      P |-a- ie \in l ->
      (if b && negb l then 0 else i) = i' ->
      i' < length (ast a) ->
      P |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i']
            <((skip, st, a !-> upd i' (ast a) n; ast, b))>
  | ISM_Write_U : forall P a ie e st ast i n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      P |-a- ie \in public ->
      i >= length (ast a) ->
      i' < length (ast a') ->
      P |- <((a[ie] <- e, st, ast, true))> -->i_[DStore a' i']^^[OAWrite a i]
            <((skip, st, a' !-> upd i' (ast a') n; ast, true))>

  where "P |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (ideal_eval_small_step P c st ast b ct stt astt bt ds os).

Reserved Notation
  "P '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'"
  (at level 40, c custom com at level 99, ct custom com at level 99,
   st constr, ast constr, stt constr, astt constr at next level).

Inductive multi_ideal (P:pub_vars) (c:com) (st:state) (ast:astate) (b:bool) :
    com -> state -> astate -> bool -> dirs -> obs -> Prop :=
  | multi_ideal_refl : P |- <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))>
  | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool)
                (c'':com) (st'':state) (ast'':astate) (b'':bool)
                (ds1 ds2 : dirs) (os1 os2 : obs) :
      P |- <((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> ->
      P |- <((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> ->
      P |- <((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))>

  where "P |- <(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" :=
    (multi_ideal P c st ast b ct stt astt bt ds os).

Lemma multi_ideal_trans_nil_l P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_[]^^[] <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_l. rewrite <- app_nil_l with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_trans_nil_r P c st ast b c' st' ast' b' ct stt astt bt ds os :
  P |- <((c, st, ast, b))> -->i_ds^^os <((c', st', ast', b'))> ->
  P |- <((c', st', ast', b'))> -->i*_[]^^[] <((ct, stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))>.
Proof.
  intros. rewrite <- app_nil_r. rewrite <- app_nil_r with (l:=ds). eapply multi_ideal_trans; eassumption.
Qed.

Lemma multi_ideal_combined_executions :
  forall P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost,
    P |- <((c, st, ast, b))> -->i*_ds^^osm <((cm, stm, astm, bm))> ->
    P |- <((cm, stm, astm, bm))> -->i*_dsm^^ost <((ct, stt, astt, bt))> ->
    P |- <((c, st, ast, b))> -->i*_(ds++dsm)^^(osm++ost) <((ct, stt, astt, bt))>.
Proof.
  intros P c st ast b ds cm stm astm bm osm dsm ct stt astt bt ost Hev1 Hev2.
  induction Hev1.
  - do 2 rewrite app_nil_l. apply Hev2.
  - do 2 rewrite <- app_assoc. eapply multi_ideal_trans.
    + eapply H.
    + apply IHHev1. apply Hev2.
Qed.

Lemma multi_ideal_add_snd_com : forall P c st ast ct stt astt ds os c2 b bt,
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c;c2, st, ast, b))> -->i*_ds^^os <((ct;c2, stt, astt, bt))>.
Proof.
  intros. induction H; repeat econstructor; eauto.
Qed.

Lemma ideal_eval_small_step_obs_length : forall P c st ast b ds ct stt astt bt os,
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof. intros. induction H; simpl; auto. Qed.

Lemma ideal_eval_small_step_same_length : forall P c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2,
  P |- <((c, st1, ast1, b1))> -->i_ds1^^os1 <((ct1, stt1, astt1, bt1))> ->
  P |- <((c, st2, ast2, b2))> -->i_ds2^^os2 <((ct2, stt2, astt2, bt2))> ->
  length ds1 = length ds2.
Proof.
  intros P c st1 st2 ast1 ast2 b1 b2 ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 ds1 ds2. intros. revert st2 ast2 b2 ct2 stt2 astt2 bt2 H0.
  induction H; simpl; intros.
  + now invert H0.
  + invert H0; [|inversion H].
    eapply IHideal_eval_small_step; eassumption.
  + invert H0; [inversion H12|reflexivity].
  + now invert H2.
  + now invert H2.
  + now invert H0.
  + now invert H3.
  + now invert H4.
  + now invert H4.
  + now invert H4.
Qed.

Lemma multi_ideal_obs_length : forall P c st ast b ds ct stt astt bt os,
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  length ds = length os.
Proof. intros. induction H; [tauto|].
  do 2 rewrite length_app. apply ideal_eval_small_step_obs_length in H.
  auto.
Qed.

Lemma ideal_eval_small_step_spec_bit_monotonic : forall P c st ast ds ct stt astt bt os,
  P |- <((c, st, ast, true))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto.
Qed.

Lemma multi_ideal_spec_bit_monotonic : forall P c st ast ds ct stt astt bt os,
  P |- <((c, st, ast, true))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  bt = true.
Proof.
  intros. remember true as b eqn:Eqb.
  induction H; subst; eauto. apply ideal_eval_small_step_spec_bit_monotonic in H; subst.
  auto.
Qed.

Lemma ideal_eval_small_step_spec_needs_force : forall P c st ast ct stt astt ds os,
  P |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, true))> ->
  ds = [DForce].
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  induction H; intros; subst; try discriminate; try reflexivity.
  now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_spec_needs_force : forall P c st ast ct stt astt ds os,
  P |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, true))> ->
  In DForce ds.
Proof.
  intros. remember false as b. remember true as bt. revert Heqb Heqbt.
  induction H; intros; subst; [discriminate|]. apply in_or_app.
  destruct b'.
  + apply ideal_eval_small_step_spec_needs_force in H. subst. left. now left.
  + right. now apply IHmulti_ideal.
Qed.

Lemma ideal_eval_small_step_no_spec : forall P c st ast ct stt astt ds os,
  P |- <((c, st, ast, false))> -->i_ds^^os <((ct, stt, astt, false))> ->
  ds = [DStep] \/ ds = [].
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; try discriminate; (try now left); try now right.
  now apply IHideal_eval_small_step.
Qed.

Lemma multi_ideal_no_spec : forall P c st ast ct stt astt ds os,
  P |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, false))> ->
  exists n, ds = repeat DStep n.
Proof.
  intros. remember false as b in H at 1. remember false as bt in H. revert Heqb Heqbt.
  induction H; intros; subst; [now exists 0|].
  destruct b'; [now apply multi_ideal_spec_bit_monotonic in H0|].
  apply ideal_eval_small_step_no_spec in H. destruct IHmulti_ideal as (n&->); [reflexivity..|].
  destruct H; subst; [|now exists n].
  exists (1 + n). now rewrite repeat_app.
Qed.

Lemma multi_ideal_spec_bit_deterministic : forall P c st1 st2 ast1 ast2 b ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
  P |- <(( c, st1, ast1, b ))> -->i*_ ds ^^ os1 <(( c1, stt1, astt1, bt1 ))> ->
  P |- <(( c, st2, ast2, b ))> -->i*_ ds ^^ os2 <(( c2, stt2, astt2, bt2 ))> ->
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

Lemma ideal_eval_small_step_dirs_obs : forall P c st ast b ct stt astt bt ds os,
  P |- <((c, st, ast, b))> -->i_ ds ^^ os <((ct, stt, astt, bt))> ->
  (ds = [] /\ os = []) \/ (exists d o, ds = [d] /\ os = [o]).
Proof. intros. now induction H; eauto. Qed.

Lemma ideal_eval_small_step_silent_step : forall P c st ast b ct stt astt bt,
  P |- <((c, st, ast, b))> -->i_ [] ^^ [] <((ct, stt, astt, bt))> ->
  b = bt /\ ast = astt.
Proof. intros. remember [] as ds in H at 1. revert Heqds. now induction H; intros; eauto. Qed.

Lemma multi_ideal_factorize : forall P c st ast b ct stt astt bt d ds os,
  P |- <((c, st, ast, b))> -->i*_ d :: ds ^^ os <((ct, stt, astt, bt))> ->
  exists c' st' ct' stt' astt' bt' o os',
  os = o :: os' /\
  P |- <((c, st, ast, b))> -->i*_[]^^[] <((c', st', ast, b))> /\
  P |- <((c', st', ast, b))> -->i_[d]^^[o] <((ct', stt', astt', bt'))> /\
  P |- <((ct', stt', astt', bt'))> -->i*_ds^^os' <((ct, stt, astt, bt))>.
Proof.
  intros. remember (d :: ds) as ds'. revert d ds Heqds'. induction H; intros; try discriminate.
  apply ideal_eval_small_step_dirs_obs in H as Heq.
  destruct Heq.
  + destruct H1. subst. simpl in Heqds'. subst. simpl.
    specialize (IHmulti_ideal d ds Logic.eq_refl).
    destruct IHmulti_ideal as (?&?&?&?&?&?&?&?&->&?&?&?).
    apply ideal_eval_small_step_silent_step in H as Heq. destruct Heq. subst.
    eapply multi_ideal_trans in H1; [|eassumption]. simpl in H1. now eauto 20.
  + destruct H1 as (d'&o&->&->). simpl in Heqds'. invert Heqds'. simpl.
    repeat eexists; [|eassumption..]. now constructor.
Qed.

Lemma ideal_eval_small_step_preserves_wt : forall P PA c st ast b ct stt astt bt pc ds os,
  P & PA, pc |-- c ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  P & PA, pc |-- ct.
Proof.
  intros. induction H0; try now constructor.
  + invert H. constructor; tauto.
  + now invert H.
  + invert H. eapply bexp_has_label_inj in H0; [|eassumption]. subst. destruct pc.
    - unfold join in *. destruct l. { now destruct b, (beval st be). }
      simpl in *. fold secret in *. fold public. apply wt_relax in H8, H9. now destruct b, (beval st be).
    - unfold join in *. now destruct l, b, (beval st be).
  + invert H. eapply bexp_has_label_inj in H0; [|eassumption]. subst. destruct pc.
    - unfold join in *. destruct l. { now destruct b, (beval st be). }
      simpl in *. fold secret in *. fold public. apply wt_relax in H8, H9. now destruct b, (beval st be).
    - unfold join in *. now destruct l, b, (beval st be).
  + invert H. econstructor; [eassumption| |constructor]. constructor; [tauto|]. econstructor; [eassumption|].
    unfold join in *. now destruct pc, l.
Qed.

Lemma multi_ideal_preserves_wt : forall P PA c st ast b ct stt astt bt pc ds os,
  P & PA, pc |-- c ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P & PA, pc |-- ct.
Proof.
  intros. induction H0; [tauto|].
  eapply IHmulti_ideal, ideal_eval_small_step_preserves_wt; eassumption.
Qed.

Lemma ideal_eval_small_step_noninterference : forall P PA c st1 st2 ast1 ast2 b ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 pc ds os,
  P & PA, pc |-- c ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA ast1 ast2) ->
  P |- <((c, st1, ast1, b))> -->i_ds^^os <((ct1, stt1, astt1, bt1))> ->
  P |- <((c, st2, ast2, b))> -->i_ds^^os <((ct2, stt2, astt2, bt2))> ->
  ct1 = ct2 /\ bt1 = bt2 /\ pub_equiv P stt1 stt2 /\ (bt1 = false -> pub_equiv PA astt1 astt2).
Proof.
  intros P PA c st1 st2 ast1 ast2 b ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 pc ds os.
  intros Hwt Hequiv Hequiv' H. revert ct2 st2 ast2 stt2 astt2 bt2 Hwt Hequiv Hequiv'. induction H; simpl; intros.
  + invert H0. invert Hwt. unfold can_flow, join in H3. apply orb_prop in H3. destruct H3.
    - apply andb_prop in H. destruct H; subst. erewrite noninterferent_aexp; [|eassumption..].
      repeat econstructor; [|tauto]. destruct (P x) eqn:Hx; [now apply pub_equiv_update_public|now apply pub_equiv_update_secret].
    - apply negb_true_iff in H. repeat econstructor; [|tauto]. now apply pub_equiv_update_secret.
  + invert H0; [|inversion H]. invert Hwt. eapply IHideal_eval_small_step in H3; [|eassumption..]. destruct H3; subst. tauto.
  + now invert H; [inversion H12|].
  + now invert H2.
  + now invert H2.
  + now invert H.
  + invert H3. do 2 split; [reflexivity|]. split; [|tauto]. destruct (P x) eqn:Hx; [|now apply pub_equiv_update_secret].
    eapply aexp_has_label_inj in H9; [|apply H]. subst. invert Hwt. unfold can_flow, join in H6. rewrite Hx, orb_false_r in H6.
    apply andb_prop in H6. destruct H6. apply andb_prop in H1. destruct H1. subst. eapply aexp_has_label_inj in H4; [|apply H]. subst.
    destruct bt2; [now apply pub_equiv_update_public|]. apply Hequiv' in H3; [|tauto]. rewrite H3. now apply pub_equiv_update_public.
  + invert H4. repeat econstructor; try tauto. destruct (P x) eqn:Hx; [now apply pub_equiv_update_public|now apply pub_equiv_update_secret].
  + invert H4. repeat econstructor; try tauto. intro. subst. simpl in *. destruct (PA a) eqn:Ha; [|apply pub_equiv_update_secret; tauto].
    invert Hwt. unfold can_flow, join in H7. rewrite Ha, orb_false_r in H7. apply andb_prop in H7. destruct H7. apply andb_prop in H0. destruct H0.
    subst. apply Hequiv' in Ha as H; [|tauto]. eapply noninterferent_aexp in H6; [|eassumption]. rewrite H, H6. apply pub_equiv_update_public; tauto.
  + now invert H4.
Qed.

Lemma ideal_eval_seq_eval : forall P c st ast ct stt astt bt n os,
  P |- <((c, st, ast, false))> -->i_ repeat DStep n ^^ os <((ct, stt, astt, bt))> ->
  <((c, st, ast ))> -->^os <((ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert Heqb Heqds.
  induction H; intros; subst; try discriminate; try now econstructor.
  + constructor. now apply IHideal_eval_small_step.
  + rewrite orb_true_r. constructor.
  + symmetry in Heqds. change ([DForce]) with ([] ++ [DForce]) in Heqds.
    now apply repeat_eq_elt in Heqds.
  + rewrite ?andb_false_r in *. now constructor.
Qed.

Lemma multi_ideal_multi_seq : forall P c st ast ct stt astt bt n os,
  P |- <((c, st, ast, false))> -->i*_ repeat DStep n ^^ os <((ct, stt, astt, bt))> ->
  <((c, st, ast ))> -->*^os <((ct, stt, astt))>.
Proof.
  intros. remember false as b in H. remember (repeat DStep n) as ds in H. revert n Heqb Heqds.
  induction H; intros; subst; [constructor|].
  symmetry in Heqds. apply repeat_eq_app in Heqds. destruct Heqds.
  remember (length ds1) as n1. remember (length ds2) as n2. clear Heqn1 Heqn2 H0. subst.
  destruct b'. { apply ideal_eval_small_step_spec_needs_force in H. change ([DForce]) with ([] ++ [DForce]) in H. now apply repeat_eq_elt in H. }
  apply ideal_eval_seq_eval in H. econstructor; [eassumption|].
  now eapply IHmulti_ideal; eauto.
Qed.

Definition ideal_same_obs P c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 c1 c2,
    P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((c1, stt1, astt1, bt1))> ->
    P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((c2, stt2, astt2, bt2))> ->
    os1 = os2.

Lemma ideal_eval_preserves_nonempty_arrs : forall P c st ast b ct stt astt bt ds os,
  nonempty_arrs ast ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  nonempty_arrs astt.
Proof.
  intros.
  induction H0; [tauto..|now apply t_update_nonempty_arrs|now apply t_update_nonempty_arrs].
Qed.

Lemma multi_ideal_preserves_nonempty_arrs : forall P c st ast b ct stt astt bt ds os,
  nonempty_arrs ast ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  nonempty_arrs astt.
Proof.
  intros. induction H0; [tauto|].
  apply ideal_eval_preserves_nonempty_arrs in H0; tauto.
Qed.

Lemma ideal_unused_overwrite : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, st, ast, b))> -->i_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, X !-> n; st, ast, b))> -->i_ds^^os <((ct, X !-> n; stt, astt, bt))> /\ unused X ct.
Proof.
  intros. induction H0; simpl in *.
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. constructor. now rewrite aeval_unused_update.
  + repeat constructor; tauto.
  + now repeat constructor.
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [eassumption|now rewrite beval_unused_update|tauto].
  + split; [|rewrite_eq; destruct b'; tauto]. econstructor; [eassumption|now rewrite beval_unused_update|tauto].
  + now repeat constructor.
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [eassumption|now rewrite aeval_unused_update|eassumption|tauto].
  + split; [|trivial]. rewrite t_update_permute; [|tauto]. econstructor; [now rewrite aeval_unused_update|eassumption..].
  + split; [|trivial]. econstructor; [now rewrite ?aeval_unused_update..|eassumption|now subst|now subst].
  + split; [|trivial]. econstructor; try tauto. all: now rewrite aeval_unused_update.
Qed.

Lemma multi_ideal_unused_overwrite : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, stt, astt, bt))> ->
  P |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((ct, X !-> n; stt, astt, bt))>.
Proof.
  intros. induction H0; [constructor|].
  eapply ideal_unused_overwrite in H0; [|eassumption].
  destruct H0. now econstructor; eauto.
Qed.

Lemma multi_ideal_unused_update : forall P c st ast b ct stt astt bt ds os X n,
  unused X c ->
  P |- <((c, X !-> n; st, ast, b))> -->i*_ds^^os <((ct, X !-> n; stt, astt, bt))> ->
  P |- <((c, st, ast, b))> -->i*_ds^^os <((ct, X !-> st X; stt, astt, bt))>.
Proof.
  intros. eapply multi_ideal_unused_overwrite with (n:=st X) in H0; [|eassumption].
  now rewrite !t_update_shadow, t_update_same in H0.
Qed.

Ltac solve_refl :=
  now (do 2 eexists); split; [|split; [(try discriminate); (try now repeat econstructor)|(try discriminate); tauto] ]; rewrite ?t_update_shadow, t_update_same;
  repeat econstructor; (repeat rewrite_eq); rewrite ?andb_false_r; (try now apply label_of_exp_sound).

Lemma flex_vslh_bcc_generalized : forall c ds P st ast (b:bool) c' st' ast' b' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh P c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' c'', P |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st'', ast', b'))> /\
    (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0) /\ st'' = st').
Proof.
  intros c ds P. eapply prog_size_ind with (c:=c) (ds:=ds). clear.
  intros c ds IH. intros until os. intros Harrs Hunused st_b H.
  destruct c; simpl in *.
  + invert H; [solve_refl|]. invert H0.
  + invert H; [solve_refl|]. invert H0. invert H1; [|inversion H].
    exists (x !-> aeval st e; st). eexists. rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor. rewrite t_update_neq; tauto.
  + apply multi_spec_seq in H. destruct H.
    - do 8 destruct H. destruct H0, H1. subst.
      eapply spec_eval_preserves_nonempty_arrs in Harrs as Harrs'; [|eassumption]. apply IH in H1; [|prog_size_auto|tauto..].
      destruct H1, H, H, H0; [tauto|]. destruct H1. subst.
      eapply spec_eval_preserves_nonempty_arrs in Harrs' as Harrs''; [|eassumption]. apply IH in H2; [|prog_size_auto|tauto..].
      destruct H2, H0, H0. do 2 eexists. eapply multi_ideal_unused_overwrite with (X:="b") (n:=st "b") in H0; [|tauto].
      rewrite t_update_shadow in H0. split; [|apply H2].
      eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|].
      eapply multi_ideal_trans_nil_l; [do 2 constructor|]. apply H0.
    - do 2 destruct H. subst. apply IH in H0; [|prog_size_auto|tauto..]. destruct H0, H, H.
      do 2 eexists. split; [|discriminate]. apply multi_ideal_add_snd_com. eassumption.
  + invert H; [solve_refl|].
    invert H0.
    - destruct (beval st'0 be) eqn:Hbe.
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = label_of_bexp P be || negb b'0)
          by now destruct (label_of_bexp P be); simpl; rewrite ?st_b, Hbe; destruct b'0. rewrite Heq in *.
        destruct (label_of_bexp P be || negb b'0) eqn:Hlb_b.
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|].
           invert H; [inversion H12|]. simpl in H1. rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H, H. do 2 eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
           rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H, H. do 2 eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct (label_of_bexp P be); simpl; rewrite Hbe, ?andb_false_r. rewrite Heq in *.
        invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
        rewrite Heq, t_update_same in H1. apply IH in H1; [|prog_size_auto|tauto..]. destruct H1, H, H. do 2 eexists.
        split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq; rewrite andb_false_r|tauto].
    - destruct (beval st'0 be) eqn:Hbe.
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = label_of_bexp P be || negb b)
          by now destruct (label_of_bexp P be); simpl; rewrite ?st_b, Hbe; destruct b. rewrite Heq in *.
        destruct (label_of_bexp P be || negb b) eqn:Hlb_b.
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|].
           invert H; [inversion H12|]. simpl in H1. rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H, H. do 2 eexists. split; [|apply H0]. rewrite !app_nil_l. rewrite t_update_eq in H.
           apply multi_ideal_unused_update in H; [|tauto].
           repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
        ++ invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
           rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..]. rewrite t_update_eq in H1.
           destruct H1, H, H. apply multi_ideal_unused_update in H; [|tauto].
           do 2 eexists. split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq|tauto].
      * assert (Heq : beval st'0 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now destruct (label_of_bexp P be); simpl; rewrite Hbe, ?andb_false_r. rewrite Heq in *.
        invert H1; [solve_refl|]. invert H. invert H12. invert H0; [solve_refl|]. invert H; [inversion H12|]. simpl in H1.
        rewrite Heq in H1. apply IH in H1; [|prog_size_auto|tauto..]. destruct H1, H, H. do 2 eexists. rewrite t_update_eq in H.
        apply multi_ideal_unused_update in H; [|tauto].
        split; [|apply H0]. rewrite !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now repeat rewrite_eq; rewrite andb_false_r|tauto].
  + invert H; [solve_refl|]. invert H0. invert H12. invert H1; [solve_refl|]. invert H. invert H12.
    - destruct (beval st'1 be && (label_of_bexp P be || (st'1 "b" =? 0)%nat)) eqn:Heq.
      * apply andb_prop in Heq. destruct Heq. apply orb_prop in H1.
        assert (Heq : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct H1 as [->|H1], (label_of_bexp P be); simpl; repeat rewrite_eq.
        rewrite Heq in H0. apply multi_spec_seq_assoc in H0. do 2 destruct H0. apply multi_spec_seq in H0. destruct H0.
        ++ do 8 destruct H0. destruct H3, H4. subst. invert H4. invert H0. invert H16. simpl in H3. rewrite Heq, t_update_same in H3.
           invert H3. invert H0; [inversion H16|]. apply IH in H4; [|prog_size_auto|tauto..]. destruct H4, H0, H0, H3 as (->&?); [reflexivity|].
           pose proof (multi_ideal_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ Harrs H0).
           remember (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) as be'.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh P c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh P <{{ while be do c end }}>) in H5
            by now simpl; rewrite Heqbe'.
           apply IH in H5; [|prog_size_auto|simpl; tauto..]. destruct H5, H5, H5, H3.
           eapply multi_ideal_unused_overwrite with (X:="b") (n:=st'0 "b") in H5; [|simpl; tauto]. rewrite t_update_shadow in H5.
           do 2 eexists. split; [|intro Hc'; now apply H6, H2]. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { subst. now destruct (label_of_bexp P be); simpl; rewrite ?st_b; destruct b'1. } { reflexivity. }
           rewrite Heq. simpl. eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H0|]. subst.
           eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|apply H5].
        ++ do 2 destruct H0. subst. invert H3.
           { do 2 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
           invert H0. invert H15. invert H4.
           { do 2 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. erewrite t_update_same, !app_nil_r with (l:=[]).
             repeat econstructor; [apply label_of_exp_sound|now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b]. }
           invert H0; [inversion H15|]. simpl in H3. rewrite Heq, t_update_same in H3. apply IH in H3; [|prog_size_auto|tauto..].
           destruct H3, H0, H0. do 2 eexists. split; [|intro Hc'; apply H2 in Hc'; discriminate]. econstructor; [constructor|].
           econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'1; simpl; rewrite ?st_b. } { reflexivity. }
           rewrite Heq. simpl. apply multi_ideal_add_snd_com, H0.
      * assert (Heq' : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now rewrite <- Heq at 6; destruct (label_of_bexp P be); simpl; destruct (beval st'1 be), (st'1 "b").
        rewrite Heq' in H0. invert H0.
        { do 2 eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
        invert H; [inversion H12|]. invert H1.
        {do 2 eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. }
        invert H. invert H0; [|inversion H]. do 2 eexists. split; [|split; [reflexivity|now simpl; rewrite Heq'] ].
        rewrite t_update_shadow, t_update_same. econstructor; [constructor|]. econstructor; [econstructor|].
        { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
        simpl. econstructor.
    - destruct (beval st'1 be && (label_of_bexp P be || (st'1 "b" =? 0)%nat)) eqn:Heq.
      * apply andb_prop in Heq. destruct Heq. apply orb_prop in H1.
        assert (Heq : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = true)
          by now destruct H1 as [->|H1], (label_of_bexp P be); simpl; repeat rewrite_eq.
        rewrite Heq in H0. invert H0.
        { do 2 eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
        invert H2; [inversion H14|]. invert H3.
        { do 2 eexists. split; [|discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
          now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
        invert H0. invert H2; [|inversion H0]. do 2 eexists.
        split; [|split; [reflexivity|now simpl; rewrite Heq] ]. rewrite t_update_shadow, t_update_same. rewrite Heq. repeat econstructor; [apply label_of_exp_sound|].
        rewrite <- Heq. now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b.
      * assert (Heq' : beval st'1 (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) = false)
          by now rewrite <- Heq at 6; destruct (label_of_bexp P be); simpl; destruct (beval st'1 be), (st'1 "b").
        rewrite Heq' in H0. apply multi_spec_seq_assoc in H0. destruct H0, H. apply multi_spec_seq in H. destruct H.
        ++ do 8 destruct H. destruct H1, H2. subst. invert H2. invert H. invert H14. invert H1. invert H; [inversion H14|].
           simpl in H2. rewrite Heq' in H2. apply IH in H2; [|prog_size_auto|tauto..]. destruct H2, H, H, H1 as (->&?); [reflexivity|].
           rewrite t_update_eq in H. apply multi_ideal_unused_update in H; [|simpl; tauto].
           pose proof (multi_ideal_preserves_nonempty_arrs _ _ _ _ _ _ _ _ _ _ _ Harrs H).
           remember (if label_of_bexp P be then be else <{{ "b" = 0 && be }}>) as be' in H3.
           replace <{{ while be' do "b" := be' ? "b" : 1; (flex_vslh P c) end; "b" := be' ? 1 : "b" }}> with (flex_vslh P <{{ while be do c end }}>) in H3
            by now simpl; rewrite Heqbe'.
           apply IH in H3; [|prog_size_auto|simpl; tauto..]. destruct H3, H3, H3, H1. subst.
           eapply multi_ideal_unused_overwrite with (X:="b") (n:=st'1 "b") in H3; [|simpl; tauto]. rewrite t_update_shadow in H3.
           do 2 eexists. split; [|intro Hc'; apply H4, H0, Hc']. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
           eapply multi_ideal_combined_executions; [apply multi_ideal_add_snd_com, H|]. eapply multi_ideal_trans_nil_l; [apply ISM_Seq_Skip|apply H3].
        ++ do 2 destruct H. subst. invert H1.
           { do 2 eexists. split; [|intro Hc'; apply H0 in Hc'; discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
           invert H. invert H13. invert H2.
           { do 2 eexists. split; [|intro Hc'; apply H0 in Hc'; discriminate]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|].
             now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. }
           invert H; [inversion H13|]. simpl in H1. rewrite Heq' in H1. apply IH in H1; [|prog_size_auto|tauto..].
           destruct H1, H, H. rewrite t_update_eq in H. apply multi_ideal_unused_update in H; [|tauto]. do 2 eexists.
           split; [|intro Hc'; apply H0 in Hc'; discriminate]. econstructor; [constructor|]. econstructor; [econstructor|].
           { apply label_of_exp_sound. } { now destruct (label_of_bexp P be), b'0; simpl; rewrite ?st_b. } { rewrite Heq'. reflexivity. }
           simpl. apply multi_ideal_add_snd_com, H.
  + destruct (P x && label_of_aexp P i) eqn:Hx.
    - invert H; [solve_refl|]. apply andb_prop in Hx. destruct Hx as (Hx&Hi). invert H0. invert H12.
      * invert H1.
        { exists (x !-> (if P x && label_of_aexp P i && b' then 0 else nth (aeval st i) (ast' a) 0); st).
          eexists. split; [|discriminate]. rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|now rewrite Hi|tauto]. }
        invert H; [inversion H12|]. invert H0.
        { exists (x !-> (if P x && label_of_aexp P i && b' then 0 else nth (aeval st i) (ast' a) 0); st).
          eexists. split; [|discriminate]. rewrite t_update_permute; [|tauto]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound|now rewrite Hi|tauto]. }
        invert H. invert H1; [|inversion H]. do 2 eexists. do 2 (rewrite t_update_neq; [|tauto]). split; [|now repeat econstructor]. rewrite t_update_shadow, t_update_permute; [|tauto].
        rewrite t_update_same, !app_nil_l. repeat econstructor; [apply label_of_exp_sound|now rewrite Hi|tauto|rewrite Hi]. simpl. rewrite t_update_neq; [|tauto]. rewrite st_b.
        rewrite t_update_eq. rewrite Hx. destruct b'; constructor.
      * invert H1.
        { exists (x !-> 0; st). eexists. split; [|discriminate]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
          repeat econstructor; [|tauto..|rewrite Hx; constructor]. unfold public. rewrite <- Hi. apply label_of_exp_sound. }
        invert H; [inversion H12|]. invert H0.
        { exists (x !-> 0; st). eexists. split; [|discriminate]. rewrite t_update_permute; [|tauto]. rewrite t_update_same, app_nil_l.
          repeat econstructor; [|tauto..|rewrite Hx; constructor]. unfold public. rewrite <- Hi. apply label_of_exp_sound. }
        invert H. invert H1; [|inversion H]. do 2 (rewrite t_update_neq; [|tauto]). rewrite t_update_shadow. do 2 eexists. split; [|now repeat econstructor].
        rewrite t_update_permute; [|tauto]. rewrite t_update_same, !app_nil_l. repeat econstructor; [unfold public; rewrite <- Hi; apply label_of_exp_sound|tauto..|simpl].
        rewrite t_update_neq; [|tauto]. rewrite t_update_eq, st_b, Hx. constructor.
    - invert H; [solve_refl|]. invert H0.
      * invert H1; [|inversion H]. do 2 eexists. rewrite t_update_neq; [|tauto]. split; [|now repeat econstructor]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
        destruct (label_of_aexp P i) eqn:Hi.
        { rewrite andb_true_r in Hx. repeat econstructor; [apply label_of_exp_sound|now rewrite Hi|tauto|]. rewrite Hx. constructor. }
        repeat econstructor; [apply label_of_exp_sound|now simpl; rewrite Hi, st_b; destruct b'|tauto|]. rewrite Hi, andb_false_r. constructor.
      * invert H1; [|inversion H]. do 2 eexists. rewrite t_update_neq; [|tauto]. split; [|now repeat econstructor]. rewrite t_update_permute; [|tauto]. rewrite t_update_same.
        destruct (label_of_aexp P i) eqn:Hi.
        { rewrite andb_true_r in Hx. repeat econstructor; [|try tauto..|try rewrite Hx; constructor]. unfold public. rewrite <- Hi. apply label_of_exp_sound. }
        simpl in H14. rewrite st_b in H14. simpl in H14. specialize (Harrs a). lia.
  + invert H; [solve_refl|]. invert H0.
    - invert H1; [|inversion H]. do 2 eexists. split; [|tauto]. rewrite t_update_same. repeat econstructor; [apply label_of_exp_sound| |tauto].
      now destruct b', (label_of_aexp P i); simpl; rewrite ?st_b.
    - invert H1; [|inversion H]. do 2 eexists. split; [|tauto]. rewrite t_update_same. destruct (label_of_aexp P i) eqn:Heq.
      { repeat econstructor; [|tauto..]. unfold public. rewrite <- Heq. apply label_of_exp_sound. }
      simpl in H15. rewrite st_b in H15. specialize (Harrs a). simpl in H15. lia.
Qed.

Lemma flex_vslh_bcc : forall c ds P st ast (b:bool) c' st' ast' b' os,
  nonempty_arrs ast ->
  unused "b" c ->
  st "b" = (if b then 1 else 0) ->
  <((flex_vslh P c, st, ast, b))> -->*_ds^^os <((c', st', ast', b'))> ->
  exists st'' c'', P |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "b" !-> st "b"; st'', ast', b'))> /\ (c' = <{{ skip }}> -> st'' = st').
Proof.
  intros. apply flex_vslh_bcc_generalized in H2; [|tauto..]. do 3 destruct H2. do 2 eexists. split; [apply H2|apply H3].
Qed.

Lemma seq_same_obs_com_read : forall x a i st1 st2 ast1 ast2,
  aeval st1 i < length (ast1 a) ->
  aeval st2 i < length (ast2 a) ->
  seq_same_obs <{{ x <- a[[i]] }}> st1 st2 ast1 ast2 ->
  aeval st1 i = aeval st2 i.
Proof.
  intros. remember <{{ x <- a[[i]] }}> as c.
  assert (<((c, st1, ast1))> -->*^[OARead a (aeval st1 i)] <((skip, x !-> nth (aeval st1 i) (ast1 a) 0; st1, ast1))>).
  { rewrite <- app_nil_r, Heqc. now repeat econstructor. }
  assert (<((c, st2, ast2))> -->*^[OARead a (aeval st2 i)] <((skip, x !-> nth (aeval st2 i) (ast2 a) 0; st2, ast2))>).
  { rewrite <- app_nil_r, Heqc. now repeat econstructor. }
  eapply H1 in H2. apply H2, prefix_or_heads in H3. now invert H3.
Qed.

Lemma seq_same_obs_com_write : forall e a i st1 st2 ast1 ast2,
  aeval st1 i < length (ast1 a) ->
  aeval st2 i < length (ast2 a) ->
  seq_same_obs <{{ a[i] <- e }}> st1 st2 ast1 ast2 ->
  aeval st1 i = aeval st2 i.
Proof.
  intros. 
  intros. remember <{{ a[i] <- e }}> as c.
  assert (<((c, st1, ast1))> -->*^[OAWrite a (aeval st1 i)] <((skip, st1, (a !-> upd (aeval st1 i) (ast1 a) (aeval st1 e); ast1)))>).
  { rewrite <- app_nil_r, Heqc. now repeat econstructor. }
  assert (<((c, st2, ast2))> -->*^[OAWrite a (aeval st2 i)] <((skip, st2, (a !-> upd (aeval st2 i) (ast2 a) (aeval st2 e); ast2)))>).
  { rewrite <- app_nil_r, Heqc. now repeat econstructor. }
  eapply H1 in H2. apply H2, prefix_or_heads in H3. now invert H3.
Qed.

Lemma ideal_misspeculated_unwinding_one_step : forall P c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds,
  pub_equiv P st1 st2 ->
  P |- <((c, st1, ast1, true))> -->i_ds^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i_ds^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2 /\ ct1 = ct2.
Proof.
  intros P c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 ds. intros Hequiv H.
  remember true as b in H at 1. remember true as bt in H.
  revert st2 ast2 ct2 stt2 astt2 os2 Heqb Heqbt Hequiv. induction H; simpl; intros; subst.
  + now invert H0.
  + invert H0; [|inversion H].
    apply IHideal_eval_small_step in H13; [|tauto..]. destruct H13. now subst.
  + invert H; [inversion H12|tauto].
  + invert H2. eapply bexp_has_label_inj in H; [|eassumption]. subst.
    destruct l; [|tauto]. now erewrite noninterferent_bexp; eauto.
  + invert H2. eapply bexp_has_label_inj in H; [|eassumption]. subst.
    destruct l; [|tauto]. now erewrite noninterferent_bexp; eauto.
  + now invert H.
  + invert H3. eapply aexp_has_label_inj in H; [|eassumption]. subst.
    destruct li; [|tauto]. now erewrite noninterferent_aexp; eauto.
  + invert H4. now erewrite noninterferent_aexp; eauto.
  + invert H4. eapply aexp_has_label_inj in H8; [|apply H1]. subst. destruct l0; [|tauto].
    now erewrite noninterferent_aexp; eauto.
  + invert H4. now erewrite noninterferent_aexp; eauto.
Qed.

Lemma multi_ideal_preserves_seq_same_obs : forall P c st1 st2 ast1 ast2 ct stt1 stt2 astt1 astt2 ds os1 os2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((ct, stt1, astt1, false))> ->
  P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((ct, stt2, astt2, false))> ->
  seq_same_obs ct stt1 stt2 astt1 astt2.
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

Lemma ideal_misspeculated_unwinding : forall P PA c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 pc ds,
  P & PA, pc |-- c ->
  pub_equiv P st1 st2 ->
  P |- <((c, st1, ast1, true))> -->i*_ds^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, true))> -->i*_ds^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2.
Proof.
  intros P PA c st1 ast1 st2 ast2 ct1 stt1 astt1 ct2 stt2 astt2 os1 os2 pc ds.
  intros Hwt Hequiv H. remember true as b in H at 1. remember true as bt in H.
  revert st2 ast2 ct2 stt2 astt2 os2 Heqb Heqbt Hwt Hequiv. induction H; intros; subst.
  + apply multi_ideal_obs_length in H. symmetry in H. simpl in H. now apply length_zero_iff_nil in H.
  + pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ H). subst. invert H1.
    - symmetry in H5. apply app_eq_nil in H5. destruct H5; subst.
      apply multi_ideal_obs_length in H0. apply ideal_eval_small_step_obs_length in H.
      symmetry in H, H0. apply length_zero_iff_nil in H, H0. now subst.
    - assert (ds0 = ds1).
      { apply app_eq_prefix in H2. apply prefix_eq_length; [|tauto]. eapply ideal_eval_small_step_same_length; eassumption. }
      subst. apply app_inv_head in H2. subst.
      pose proof (ideal_eval_small_step_spec_bit_monotonic _ _ _ _ _ _ _ _ _ _ H3). subst.
      pose proof (ideal_misspeculated_unwinding_one_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hequiv H H3). destruct H1; subst.
      eapply ideal_eval_small_step_noninterference in H3 as H'; [|now eauto..]. destruct H' as (_ & _ & Hequiv' & _).
      eapply ideal_eval_small_step_preserves_wt in Hwt; [|now eauto]. f_equal.
      now eapply IHmulti_ideal; eauto.
Qed.

Lemma multi_ideal_misspeculate_split : forall P ds c st ast ct stt astt os,
  P |- <((c, st, ast, false))> -->i*_ds^^os <((ct, stt, astt, true))> ->
  exists n ds2 os1 o os2 c1 c2 st1 st2 ast1 ast2,
  ds = repeat DStep n ++ DForce :: ds2 /\
  os = os1 ++ o :: os2 /\
  P |- <((c, st, ast, false))> -->i*_ repeat DStep n ^^os1 <((c1, st1, ast1, false))> /\
  P |- <((c1, st1, ast1, false))> -->i_[DForce]^^[o] <((c2, st2, ast2, true))> /\
  P |- <((c2, st2, ast2, true))> -->i*_ds2^^os2 <((ct, stt, astt, true))>.
Proof.
  induction ds; intros; [now apply multi_ideal_spec_needs_force in H|].
  apply multi_ideal_factorize in H. do 9 destruct H. destruct H0, H1. subst.
  destruct x4.
  + apply ideal_eval_small_step_spec_needs_force in H1 as Heq. invert Heq.
    change (DForce :: ds) with ([]++[DForce]++ds). change (x5::x6) with ([]++ x5 :: x6).
    exists 0, ds. now eauto 20.
  + apply IHds in H2. destruct H2. do 11 destruct H. destruct H2, H3. subst.
    apply ideal_eval_small_step_no_spec in H1 as Heq. destruct Heq; [|discriminate]. invert H.
    eapply multi_ideal_trans in H1; [|eassumption]. eapply multi_ideal_combined_executions in H1; [|eassumption].
    rewrite !app_comm_cons. exists (1+x4), x7. now eauto 20.
Qed.

Lemma multi_ideal_no_spec_deterministic : forall P c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 ds os1 os2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  P |- <((c, st1, ast1, false))> -->i*_ds^^os1 <((ct1, stt1, astt1, false))> ->
  P |- <((c, st2, ast2, false))> -->i*_ds^^os2 <((ct2, stt2, astt2, false))> ->
  os1 = os2.
Proof.
  intros. apply multi_ideal_no_spec in H0 as Heq.
  destruct Heq as (n&->). apply multi_ideal_obs_length in H0 as Heq, H1 as Heq'.
  rewrite Heq' in Heq. clear Heq'. apply multi_ideal_multi_seq in H1, H0.
  apply prefix_eq_length; [now symmetry|]. eapply H; eassumption.
Qed.

Lemma multi_ideal_stuck_noninterference :
  forall P PA c st1 st2 ast1 ast2 b ct1 ct2 stt1 stt2 astt1 astt2 bt1 bt2 ct1' ct2' stt1' stt2' astt1' astt2' bt1' bt2' ds os d1 d2 o1 o2,
  P & PA, public |-- c ->
  pub_equiv P st1 st2 ->
  (b = false -> pub_equiv PA ast1 ast2) ->
  P |- <((c, st1, ast1, b))> -->i*_ds^^os <((ct1, stt1, astt1, bt1))> ->
  P |- <((ct1, stt1, astt1, bt1))> -->i_[d1]^^[o1] <((ct1', stt1', astt1', bt1'))> ->
  P |- <((c, st2, ast2, b))> -->i*_ds^^os <((ct2, stt2, astt2, bt2))> ->
  P |- <((ct2, stt2, astt2, bt2))> -->i_[d2]^^[o2] <((ct2', stt2', astt2', bt2'))> ->
  ct1 = ct2 /\ bt1 = bt2 /\ pub_equiv P stt1 stt2 /\ (bt2 = false -> pub_equiv PA astt1 astt2).
Proof.
  intros. revert st2 ast2 ct2 stt2 astt2 bt2 ct2' stt2' astt2' bt2' d2 o2 H4 H5 H H0 H1.
  induction H2; intros.
  + invert H4; [tauto|].
    eapply ideal_eval_small_step_same_length in H3 as Heq; [|apply H11].
    apply app_eq_nil in H2. now destruct H2; subst.
  + specialize (IHmulti_ideal H3). invert H4.
    { symmetry in H12. apply app_eq_nil in H12. destruct H12; subst.
      now eapply ideal_eval_small_step_same_length in H; [|apply H5]. }
    eapply ideal_eval_small_step_same_length in H as Heq; [|apply H13].
    apply prefix_eq_length in Heq; [subst|eapply app_eq_prefix, H7].
    apply ideal_eval_small_step_obs_length in H as Heq, H13 as Heq'.
    rewrite Heq' in Heq. apply prefix_eq_length in Heq; [subst|eapply app_eq_prefix, H8].
    apply app_inv_head in H7, H8. clear Heq'. subst.
    eapply ideal_eval_small_step_noninterference in H13 as Heq; [|now eauto..].
    destruct Heq as (<-&<-&?&?). eapply ideal_eval_small_step_preserves_wt in H0; [|eassumption].
    now eapply IHmulti_ideal; eauto.
Qed.

Lemma ideal_eval_small_step_force_obs : forall P c st1 st2 ast1 ast2 ct1 ct2 stt1 stt2 astt1 astt2 os1 os2,
  seq_same_obs c st1 st2 ast1 ast2 ->
  P |- <((c, st1, ast1, false))> -->i_[DForce]^^os1 <((ct1, stt1, astt1, true))> ->
  P |- <((c, st2, ast2, false))> -->i_[DForce]^^os2 <((ct2, stt2, astt2, true))> ->
  os1 = os2.
Proof.
  intros. remember false as b in H0. remember true as bt in H0. remember [DForce] as ds in H0.
  revert st2 ast2 os2 ct2 stt2 astt2 Heqb Heqbt Heqds H H1. induction H0; intros; subst; try discriminate.
  + invert H1. apply seq_same_obs_com_seq in H. eapply IHideal_eval_small_step; [tauto..|eassumption|eassumption].
  + invert H3. apply seq_same_obs_com_if in H2. now rewrite H2, !orb_true_r.
Qed.

Lemma repeat_same_length : forall {A : Type} (a b : A) n n' l l',
  a <> b ->
  repeat a n ++ b :: l = repeat a n' ++ b :: l' ->
  n = n'.
Proof.
  induction n; intros.
  + destruct n'; [reflexivity|exfalso]. apply H.
    simpl in H0. now invert H0.
  + destruct n'.
    - exfalso. apply H. simpl in H0. now invert H0.
    - simpl in H0. invert H0. f_equal. eapply IHn; eassumption.
Qed.

Lemma ideal_eval_relative_secure : forall P PA c st1 st2 ast1 ast2,
  P & PA, public |-- c ->
  pub_equiv P st1 st2 ->
  pub_equiv PA ast1 ast2 ->
  seq_same_obs c st1 st2 ast1 ast2 ->
  ideal_same_obs P c st1 st2 ast1 ast2.
Proof.
  unfold ideal_same_obs. intros.
  eapply multi_ideal_spec_bit_deterministic in H3 as Heq; [|apply H4]. subst.
  destruct bt1; [|eapply multi_ideal_no_spec_deterministic; eassumption].
  apply multi_ideal_misspeculate_split in H3, H4.
  destruct H3 as (n&ds'&?&?&?&?&?&?&?&?&?&->&->&?&?&?).
  destruct H4 as (n'&?&?&?&?&?&?&?&?&?&?&Heq&->&?&?&?).
  apply repeat_same_length in Heq as Heqn; [|discriminate]. subst.
  apply app_inv_head in Heq. invert Heq.
  eapply multi_ideal_no_spec_deterministic in H2 as Heq; [|eassumption..]. subst.
  f_equal. eapply multi_ideal_stuck_noninterference in H4 as Heq; [|now eauto..].
  eapply multi_ideal_preserves_wt in H; [|eassumption].
  destruct Heq as (->&_&?&?). eapply multi_ideal_preserves_seq_same_obs in H2; [|eassumption..].
  clear c st1 st2 ast1 ast2 n' H0 H1 H3 H4.
  eapply ideal_eval_small_step_force_obs in H2; [|eassumption..]. invert H2. f_equal.
  eapply ideal_eval_small_step_noninterference in H as Heq; [|eassumption..].
  destruct Heq as (->&_&?&?). eapply ideal_eval_small_step_preserves_wt in H; [|eassumption].
  eapply ideal_misspeculated_unwinding; eassumption.
Qed.

Theorem flex_vslh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    st1 "b" = 0 ->
    st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_vslh P) c st1 st2 ast1 ast2.
Proof.
  unfold relative_secure, spec_same_obs. intros.
  apply flex_vslh_bcc in H8; [|tauto..].
  apply flex_vslh_bcc in H9; [|tauto..].
  destruct H8 as (st1'&ct1&?&?). destruct H9 as (st2'&ct2&?&?).
  eapply ideal_eval_relative_secure; eassumption.
Qed.

Module RelatingSelSLH.

  Lemma val_sel_slh_is_flex_vslh : forall P PA c,
    P ;; PA |-ct- c ->
    sel_slh P c = flex_vslh P c.
  Proof.
    intros P PA c H. induction H; simpl; repeat rewrite_eq; try reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. rewrite andb_true_r. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
  Qed.

  Lemma ct_well_typed_well_typed : forall P PA c,
    P ;; PA |-ct- c ->
    P & PA, public |-- c.
  Proof. intros. now induction H; econstructor; (try eassumption); unfold join, public in *. Qed.

  Lemma val_sel_slh_relative_secure :
    forall P PA c st1 st2 ast1 ast2,
      P ;; PA |-ct- c ->
      pub_equiv P st1 st2 ->
      pub_equiv PA ast1 ast2 ->
      unused "b" c ->
      st1 "b" = 0 ->
      st2 "b" = 0 ->
      nonempty_arrs ast1 ->
      nonempty_arrs ast2 ->
      relative_secure (sel_slh P) c st1 st2 ast1 ast2.
  Proof.
    unfold relative_secure. intros. erewrite val_sel_slh_is_flex_vslh; [|eassumption].
    apply ct_well_typed_well_typed in H. eapply flex_vslh_relative_secure; eassumption.
  Qed.

  Lemma well_typed_ct_secure_one_step : forall P PA c st1 st2 ast1 ast2 os1 os2 ct1 ct2 stt1 stt2 astt1 astt2,
    P ;; PA |-ct- c ->
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    <((c, st1, ast1))> -->^os1 <((ct1, stt1, astt1))> ->
    <((c, st2, ast2))> -->^os2 <((ct2, stt2, astt2))> ->
    ct1 = ct2 /\ pub_equiv P stt1 stt2 /\ pub_equiv PA astt1 astt2 /\ os1 = os2.
  Proof.
    intros. revert st2 ast2 os2 ct2 stt2 astt2 H H0 H1 H3. induction H2; intros.
    + invert H0. invert H3. repeat econstructor; [|tauto]. destruct (P x) eqn:Heq; [|now apply pub_equiv_update_secret].
      apply pub_equiv_update_public; [tauto..|]. unfold can_flow in H7. rewrite orb_false_r in H7. subst. eapply noninterferent_aexp; eassumption.
    + invert H3; [|inversion H2]. invert H.
      specialize (IHseq_eval_small_step _ _ _ _ _ _ H5 H0 H1 H12). destruct IHseq_eval_small_step.
      subst. tauto.
    + invert H3;[inversion H11|]. tauto.
    + invert H. invert H3. now erewrite noninterferent_bexp; [|eassumption..].
    + invert H. now invert H3.
    + invert H1. invert H4. erewrite noninterferent_aexp; [|eassumption..]. repeat econstructor; [|tauto].
      destruct (P x) eqn:Heq;[|now apply pub_equiv_update_secret].
      apply pub_equiv_update_public; [tauto..|]. unfold can_flow in H9. rewrite orb_false_r in H9. now rewrite H3.
    + invert H2. invert H5. erewrite noninterferent_aexp; [|eassumption..]. repeat econstructor; [tauto|].
      destruct (PA a) eqn:Heq; [|now apply pub_equiv_update_secret]. unfold can_flow in H11. rewrite orb_false_r in H11. subst.
      apply pub_equiv_update_public; [tauto..|]. erewrite @noninterferent_aexp with (s1:=st); [|eassumption..].
      now rewrite H4.
  Qed.

  Lemma seq_eval_small_step_preserves_well_typed :
    forall P PA c st ast ct stt astt os,
    P ;; PA |-ct- c ->
    <((c, st, ast))> -->^os <((ct, stt, astt))> ->
    P ;; PA |-ct- ct.
  Proof.
    intros. revert st ast os ct stt astt H0. induction H; intros.
    + now invert H0.
    + invert H1. constructor.
    + invert H1; [|tauto]. constructor; [|tauto]. eapply IHct_well_typed1; eassumption.
    + invert H2. now destruct (beval stt b).
    + invert H1. now repeat constructor.
    + invert H1. constructor.
    + invert H2. constructor.
  Qed.

  Lemma well_typed_ct_secure :
    forall P PA c st1 st2 ast1 ast2,
      P ;; PA |-ct- c ->
      pub_equiv P st1 st2 ->
      pub_equiv PA ast1 ast2 ->
      seq_same_obs c st1 st2 ast1 ast2.
  Proof.
    unfold seq_same_obs. intros. revert st2 ast2 os2 c2 stt2 astt2 H H0 H1 H3. induction H2; intros; [now left; apply prefix_nil|].
    invert H4; [now right; apply prefix_nil|]. specialize (well_typed_ct_secure_one_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H1 H3 H H5).
    destruct 1 as (<-&HP&HPA&<-). eapply seq_eval_small_step_preserves_well_typed in H0; [|eassumption].
    specialize (IHmulti_seq _ _ _ _ _ _ H0 HP HPA H6). unfold prefix.
    destruct IHmulti_seq as [(?&<-)|(?&<-)]; [left|right]; rewrite app_assoc; repeat eexists.
  Qed.

  Theorem val_sel_slh_spec_ct_secure :
    forall P PA c st1 st2 ast1 ast2,
      P ;; PA |-ct- c ->
      pub_equiv P st1 st2 ->
      pub_equiv PA ast1 ast2 ->
      unused "b" c ->
      st1 "b" = 0 ->
      st2 "b" = 0 ->
      nonempty_arrs ast1 ->
      nonempty_arrs ast2 ->
      spec_same_obs (sel_slh P c) st1 st2 ast1 ast2.
  Proof. intros. eapply val_sel_slh_relative_secure; [eassumption..|eapply well_typed_ct_secure; eassumption]. Qed.

End RelatingSelSLH.

Module RelatingUltimateSLH.

  Lemma AllSecrets_no_vars :
    (forall a, label_of_aexp AllSecret a = is_empty (vars_aexp a)) /\ (forall b, label_of_bexp AllSecret b = is_empty (vars_bexp b)).
  Proof.
    apply aexp_bexp_mutind; intros; simpl; unfold AllSecret, join, public, secret; rewrite ?is_empty_app; auto.
    4:now rewrite <- H, <- H0, <- H1.
    all:now rewrite <- H, <- H0.
  Qed.

  Corollary AllSecrets_aexp_no_vars :
    forall a, label_of_aexp AllSecret a = is_empty (vars_aexp a).
  Proof. now apply AllSecrets_no_vars. Qed.

  Corollary AllSecrets_bexp_no_vars :
    forall b, label_of_bexp AllSecret b = is_empty (vars_bexp b).
  Proof. now apply AllSecrets_no_vars. Qed.

  Lemma ultimate_slh_is_flex_vslh : forall c,
    ultimate_slh c = flex_vslh AllSecret c.
  Proof.
    induction c; try reflexivity.
    + simpl. now repeat rewrite_eq.
    + simpl. repeat rewrite_eq. now rewrite AllSecrets_bexp_no_vars.
    + simpl. rewrite_eq. now rewrite AllSecrets_bexp_no_vars.
    + simpl. now rewrite AllSecrets_aexp_no_vars.
    + simpl. unfold all_secret. now rewrite AllSecrets_aexp_no_vars.
  Qed.

  Lemma AllSecret_pub_equiv : forall {A : Type} (m1 m2 : total_map A),
    pub_equiv AllSecret m1 m2.
  Proof. unfold pub_equiv. intros. invert H. Qed.

  Lemma AllSecret_wt : forall c,
    AllSecret & AllSecret, secret |-- c.
  Proof.
    induction c; try now constructor.
    + econstructor; [apply label_of_exp_sound|]. now unfold can_flow, join, AllSecret, secret.
    + econstructor; [apply label_of_exp_sound|now unfold join, secret in *..].
    + econstructor; [apply label_of_exp_sound|now unfold join, secret in *..].
    + econstructor; [apply label_of_exp_sound|now unfold join, secret in *..].
    + econstructor; [apply label_of_exp_sound..|now unfold join, secret in *].
  Qed.

  Theorem ultimate_slh_relative_secure :
    forall c st1 st2 ast1 ast2,
      unused "b" c ->
      st1 "b" = 0 ->
      st2 "b" = 0 ->
      nonempty_arrs ast1 ->
      nonempty_arrs ast2 ->
      relative_secure ultimate_slh c st1 st2 ast1 ast2.
  Proof.
    unfold relative_secure. intros. rewrite ultimate_slh_is_flex_vslh.
    eapply flex_vslh_relative_secure; [apply wt_relax, AllSecret_wt|apply AllSecret_pub_equiv|apply AllSecret_pub_equiv|tauto..].
  Qed.

End RelatingUltimateSLH.
