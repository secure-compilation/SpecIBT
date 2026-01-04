Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import TestingLib.
From SECF Require Import Utils.
From SECF Require Import MiniCET.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import ExtLib.Data.Monads.OptionMonad.
From SECF Require Import Maps.
From SECF Require Import MapsFunctor.
From SECF Require Import sflib.
From SECF Require Import MiniCET_Index.

Set Default Goal Selector "!".

Import FunctionalExtensionality.

Import MCC.

Notation t_update_eq := TotalMap.t_update_eq.
Notation t_update_neq := TotalMap.t_update_neq.

Definition Rsync1 (sr tr: reg) (ms: bool) : Prop :=
  (forall x, x <> msf /\ x <> callee -> sr ! x = tr ! x).
Definition ms_msf_match (tr: reg) (ms: bool) : Prop :=
  (tr ! msf = N (if ms then 1 else 0)).

Variant match_cfgs_ext (p: prog) : state ideal_cfg -> state spec_cfg -> Prop :=
| match_cfgs_ext_intro ic sc
  (MATCH: match_cfgs p ic sc) :
  match_cfgs_ext p (S_Running ic) (S_Running sc)
| match_cfgs_ext_ct1 (* call target *)
  l blk r m stk ms r' stk'      
  (CT: nth_error p l = Some (blk, true))
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& l)) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 0), r', m, stk'), true, ms))
| match_cfgs_ext_ct2 (* call target msf *)
  l blk r m stk ms r' stk'
  (CT: nth_error p l = Some (blk, true))
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& l)) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 1), r', m, stk'), false, ms))
| match_cfgs_ext_call
  pc fp r m stk ms pc' r' stk'
  (CALL: p[[pc]] = Some <{{ call fp }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk')
  (MS: r' ! callee = (eval r' <{{ (msf = 1) ? & 0 : fp }}>)) :
  match_cfgs_ext p (S_Running ((pc, r, m, stk), ms))
                   (S_Running ((pc' + 1, r', m, stk'), false, ms))
| match_cfgs_ext_call_fault
  pc i r m stk ms
  (CT: (uslh_prog p)[[pc]] = Some i)
  (CTN: i <> <{{ ctarget }}>) :
  match_cfgs_ext p S_Fault
                   (S_Running ((pc, r, m, stk), true, ms))
| match_cfgs_ext_br_true1
  l l' r m stk (ms: bool) r' stk'
  fl fo e
  (FROM: (uslh_prog p) [[(fl, fo)]] = Some <{{ branch ((msf = 1) ? 0 : e) to l' }}>)
  (TO: (uslh_prog p) [[(l', 0)]] =
         Some <{{ msf := (~((msf = 1) ? 0 : e)) ? 1 : msf }}>)
  (MS: eval r' <{{ (~ ((msf = 1) ? 0 : e)) ? 1 : msf }}> = N (if ms then 1 else 0))
  (BT1: Datatypes.length p <= l')
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 0), r', m, stk'), false, ms))
| match_cfgs_ext_br_true2
  l l' r m stk ms r' stk'
  (BT1: Datatypes.length p <= l')
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 1), r', m, stk'), false, ms))
| match_cfgs_ext_br_false
  pc pc' l e  r r' m stk stk' (ms:bool)
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (FROM: (uslh_prog p) [[pc']] = Some <{{ branch ((msf = 1) ? 0 : e) to l }}>)
  (TO: (uslh_prog p) [[pc'+1]] = Some <{{ msf := ((msf = 1) ? 0 : e) ? 1 : msf }}>)
  (MS: eval r' <{{ ((msf = 1) ? 0 : e) ? 1 : msf }}> = N (if ms then 1 else 0))
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running ((pc + 1, r, m, stk), ms))
                   (S_Running ((pc' + 1, r', m, stk'), false, ms))
| match_cfgs_ext_fault :
  match_cfgs_ext p S_Fault S_Fault
| match_cfgs_ext_term :
  match_cfgs_ext p S_Term S_Term
.

Lemma ultimate_slh_bcc_single (p: prog) ic1 sc1 sc2 ds os
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (WFDS: wf_ds' (uslh_prog p) ds)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (MATCH: match_cfgs_ext p ic1 sc1)
  (TGT: uslh_prog p |- <(( sc1 ))> -->_ ds^^os <(( sc2 ))>) :
     exists ic2, p |- <(( ic1 ))> -->i*_ ds ^^ os <(( ic2 ))> 
          /\ match_cfgs_ext p ic2 sc2.
Proof.
  inv MATCH; try sfby inv TGT.
  (* common match *)
  - admit.
  (* target = ctarget *)
  - assert (CT': (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>).
    { admit. (* by CT *) }
    inv TGT; clarify. esplits.
    + econs.
    + eapply match_cfgs_ext_ct2; eauto.
  (* target = msf := (callee = (& (fst pc))) ? msf : 1 *)
  - assert (CT': (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>).
    { admit. (* by CT *) }
    exploit head_call_target; eauto. i. des; clarify.
    replace ((l0, 0) + 1) with (l0, 1) in x2 by ss.
    inv TGT; clarify.
    esplits; econs.
    econs; eauto.
    + unfold pc_sync. simpl. rewrite CT. destruct blk.
      { admit. (* nonempty *) }
      simpl. eauto.
    + red in REG. econs.
      * i. des. admit.
      * rewrite t_update_eq. eauto.
  (* call *)
  - assert (TCALL: (uslh_prog p)[[pc' + 1]] = Some <{{ call ((msf = 1) ? & 0 : fp) }}>).
    { admit. }
    inv TGT; clarify.
    destruct pc'0 as [l' o'].
    red in WFDS. inv WFDS. inv H2. red in H1. unfold is_some in H1.
    des_ifs.
    assert (i = ICTarget \/ i <> ICTarget).
    { destruct i; try (sfby (right; ii; clarify)). auto. }
    des; subst.
    + exploit head_call_target; eauto. i. des; clarify.
      replace [DCall(l0, 0)] with ([DCall (l0, 0)] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.
      assert (exists blk, nth_error p l0 = Some (blk, true)).
      { admit. }
      des. esplits.
      * do 2 econs; eauto.
        inv REG.
        rewrite <- H8. simpl. rewrite H2. destruct ms; ss.
        admit.
      * eapply match_cfgs_ext_ct1; eauto.
        { red. inv REG. eauto. }
        { inv REG. admit. }
        inv REG. simpl. rewrite MS. ss. rewrite H2.
        destruct ms; ss.
        { des_ifs. }
        { rewrite H2 in H8. ss. unfold to_fp in H8. des_ifs_safe.
          simpl in Heq2. clarify. destruct (l =? l0)%nat eqn:JMP; ss.
          + rewrite Nat.eqb_sym. rewrite JMP. auto.
          + rewrite Nat.eqb_sym. rewrite JMP. auto. }
    + assert (exists i, p[[(l', o')]] = Some i).
      { admit. }
      des. simpl in H0. des_ifs_safe. destruct p0. simpl in H0.
      replace [DCall(l', o')] with ([DCall (l', o')] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.
      esplits.
      { econs.
        - eapply ISMI_Call_F; eauto.
          + rewrite <- H8. admit. (* see above *)
          + ii. ss. clarify. admit. (* no ctarget -> no call target blk or o' <> 0 *)
        - econs. }
      econs; eauto.
  - inv TGT; clarify. esplits; econs.
  - inv TGT; clarify.
    esplits.
    + econs.
    + eapply match_cfgs_ext_br_true2; eauto.
      red. split.
      * ii. des. admit.
      * rewrite t_update_eq. simpl. ss.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      assert (exists blk, nth_error p l = Some (blk, false)).
      { admit. (* wf_prog -> wf lbl *) }
      des. unfold pc_sync. simpl. rewrite H.
      destruct blk as [|i blk].
      { admit. (* nonempty blk *) }
      simpl. auto.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      * admit.
      * split; ii.
        { des. rewrite t_update_neq; eauto. }
        { rewrite t_update_eq. eauto. }
Admitted.

Lemma multi_ideal_inst_trans2
  p ic1 ic2 ic3 ds1 ds2 os1 os2
  (STEPS1: p |- <(( ic1 ))> -->i*_ ds1 ^^ os1 <(( ic2 ))>)
  (STEPS2: p |- <(( ic2 ))> -->i*_ ds2 ^^ os2 <(( ic3 ))>) :
  p |- <(( ic1 ))> -->i*_ ds1 ++ ds2 ^^ os1 ++ os2 <(( ic3 ))>.
Proof.
  ginduction STEPS1; ii; ss.
  do 2 rewrite <- app_assoc. econs; eauto.
Qed.

Lemma ultimate_slh_bcc' (p: prog) ic1 sc1 sc2 ds os
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (WFDS: wf_ds' (uslh_prog p) ds)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (MATCH: match_cfgs_ext p ic1 sc1)
  n
  (TGT: uslh_prog p |- <(( sc1 ))> -->*_ ds^^os^^n <(( sc2 ))>) :
     exists ic2, p |- <(( ic1 ))> -->i*_ ds ^^ os <(( ic2 ))> 
          /\ match_cfgs_ext p ic2 sc2.
Proof.
  ginduction n; ii.
  { inv TGT. esplits; eauto. econs. }
  inv TGT. exploit ultimate_slh_bcc_single; try eapply H0; eauto.
  { admit. (* already proven before *) }
  i. des.
  exploit IHn; try eapply H5; eauto.
  { admit. (* already proven before *) }
  i. des. esplits; eauto.
  eapply multi_ideal_inst_trans2; eauto.
Admitted.

(** * Safety Presevation *)

(* YH: This could be merge. *)

Definition safe_imm_seq (p: prog) (st: state cfg) : Prop :=
  match st with
  | S_Running c => exists os stt, p |- <(( S_Running c ))> -->^ os <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False (* Unreachable *)
  end.

Definition safe_imm_ideal (p: prog) (st: state ideal_cfg) : Prop :=
  match st with
  | S_Running sc => exists ds os stt, p |- <(( S_Running sc ))> -->i_ ds ^^ os  <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False (* Unreachable *)
  end.

Definition safe_imm_spec (p: prog) (st: state spec_cfg) : Prop :=
  match st with
  | S_Running sc => exists ds os stt, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False (* Unreachable *)
  end.

Definition seq_nostep (p: prog) (st: state cfg) : Prop :=
  ~ (exists os stt, p |- <(( st ))> -->^ os <(( stt ))>).

Definition ideal_nostep (p: prog) (st: state ideal_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->i_ ds ^^ os  <(( stt ))>).

Definition spec_nostep (p: prog) (st: state spec_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->_ ds ^^ os  <(( stt ))>).

(* Arbitrary Running state that reachable from initial state can progress *)
Definition seq_exec_safe (p: prog) (c: cfg) : Prop :=
  forall os ct,
    p |- <(( S_Running c ))> -->*^ os <(( S_Running ct ))> ->
    exists os' ctt, p |- <(( S_Running ct ))> -->^ os' <(( ctt ))>.

Definition ideal_exec_safe (p: prog) (ic: ideal_cfg) : Prop :=
  forall ds os ict,
    p |- <(( S_Running ic ))> -->i*_ ds ^^ os  <(( S_Running ict ))> ->
    exists ds' os' stt, p |- <(( S_Running ict ))> -->i_ ds' ^^ os'  <(( stt ))>.

Definition spec_exec_safe (p: prog) (sc: spec_cfg) : Prop :=
  forall ds os n sct (WFDS: wf_ds' p ds),
    p |- <(( S_Running sc ))> -->*_ ds ^^ os ^^ n <(( S_Running sct ))> ->
    exists ds' os' stt, p |- <(( S_Running sct ))> -->_ ds' ^^ os'  <(( stt ))>.

Definition seq_ideal_match (st1: state cfg) (st2: state ideal_cfg) : Prop :=
  match st1, st2 with
  | S_Term, S_Term => True
  | _, S_Fault => True
  | S_Undef, _ => True
  | S_Running c, S_Running (c', b) => c = c' /\ b = false
  | _, _ => False
  end.

Definition nonempty_mem (m: mem) : Prop :=
  Datatypes.length m > 0.

Lemma seq_ideal_nonspec
  p pc r m stk os stt
  (SEQ: p |- <(( S_Running (pc, r, m, stk) ))> -->^ os <(( stt ))>) :
  exists ds stt',
    p |- <(( S_Running (pc, r, m, stk, false) ))> -->i_ ds ^^ os <(( stt' ))>
  /\ seq_ideal_match stt stt'.
Proof.
  inv SEQ; try (sfby (esplits; try econs; eauto)).
  - exists [DBranch (not_zero n)]. esplits.
    { econs; eauto. }
    ss. split; auto. rewrite eqb_reflx. ss.
  - exists [DCall (l, 0)].
    destruct (nth_error p l) eqn:PL; cycle 1.
    { esplits.
      - eapply ISMI_Call_F; eauto. ii. ss; clarify.
      - econs. }
    destruct p0. destruct b; cycle 1.
    { esplits.
      - eapply ISMI_Call_F; eauto. ii. ss; clarify. ss. auto.
      - econs. }
    esplits.
    + econs; eauto.
    + ss. split; auto. rewrite Nat.eqb_refl. auto.
Qed.

Lemma seq_ideal_safety_preservation
  p c
  (SEQ: seq_exec_safe p c) :
  ideal_exec_safe p (c, false).
Proof.
  red. ii. destruct ict as [c' ms].
  destruct c as [cl stk]. destruct cl as [cl m]. destruct cl as [pc r].
  destruct c' as [cl' stk']. destruct cl' as [cl' m']. destruct cl' as [pc' r'].
  destruct ms; cycle 1.
  { red in SEQ.
    exploit multi_ideal_nonspec_seq; eauto. i.
    eapply SEQ in x0. des. eapply seq_ideal_nonspec in x0.
    des. eauto. }
  destruct (p[[pc']]) eqn:PC'; cycle 1.
  { admit. (* wf_prog, wf_dir -> contradiction *) }
  destruct i.
  - esplits. econs; eauto.
  - esplits. econs 2. eauto.
  - esplits. econs 3; eauto.
  - esplits. econs 4; eauto.
  - esplits. econs 5; ss; eauto.
    admit. (* nonempty memory *)
  - esplits. econs 6; ss; eauto.
  - exists [DCall (0, 0)], [OCall 0].
    esplits. econs; eauto. 
    + admit. (* nonempty program *)
    + admit. (* 0th program is a call target *)
  - admit. (* no call target in the source code *)
  - destruct stk'.
    + esplits. eapply ISMI_Term. eauto.
    + esplits. eapply ISMI_Ret. eauto.
      Unshelve. all: repeat (econs).
Admitted.

Lemma seq_spec_safety_preservation
  p b c
  (SEQ: seq_exec_safe p c)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (MATCH: match_cfgs_ext p (S_Running (c, false)) (S_Running (c, b, false))) :
  spec_exec_safe (uslh_prog p) (c, b, false).
Proof.
  ii. eapply seq_ideal_safety_preservation in SEQ.
  red in SEQ.
  exploit ultimate_slh_bcc'; eauto.
  i. des. destruct ic2.
  - exploit SEQ; eauto. i. des.
    (* match -> source progress -> target progress *)
    admit.
  - admit. (* contradiction *)
  - admit. (* if source is fault -> target should progress to fault state *)
  - inv x1.
Admitted.

