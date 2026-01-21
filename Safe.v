Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
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
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& l)) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 0), r', m, stk'), true, ms))
| match_cfgs_ext_ct2 (* call target msf *)
  l blk r m stk ms r' stk'
  (CT: nth_error p l = Some (blk, true))
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (CT2: (uslh_prog p)[[(l, 1)]] = Some <{{ msf := (callee = (& l)) ? msf : 1 }}>)
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& l)) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 1), r', m, stk'), false, ms))
| match_cfgs_ext_call
  pc fp r m stk ms pc' r' stk'
  (CALL: p[[pc]] = Some <{{ call fp }}>)
  (TCALL: (uslh_prog p)[[pc' + 1]] = Some <{{ call ((msf = 1) ? & 0 : fp) }}>)
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
  pc fl fo e
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (FROM: (uslh_prog p) [[(fl, fo)]] = Some <{{ branch ((msf = 1) ? 0 : e) to l' }}>)
  (TO: (uslh_prog p) [[(l', 0)]] =
         Some <{{ msf := (~((msf = 1) ? 0 : e)) ? 1 : msf }}>)
  (MS: eval r' <{{ (~ ((msf = 1) ? 0 : e)) ? 1 : msf }}> = N (if ms then 1 else 0))
  (* (BT1: Datatypes.length p <= l') *)
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync1 r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 0), r', m, stk'), false, ms))
| match_cfgs_ext_br_true2
  pc e l l' r m stk ms r' stk'
  (* (BT1: Datatypes.length p <= l') *)
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 1), r', m, stk'), false, ms))
| match_cfgs_ext_br_false
  pc pc' l e  r r' m stk stk' (ms:bool)
  (* (BR: p[[pc]] = Some <{{ branch e to l }}>) *)
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

Lemma src_lookup
  p pc pc' (* i' *)
  (* (TGT: (uslh_prog p) [[pc']] = Some i') *)
  (SYNC: pc_sync p pc = Some pc') :
  exists i, p[[pc]] = Some i.
Proof.
  unfold pc_sync in SYNC. des_ifs.
  destruct pc; ss. des_ifs; eauto.
Qed.

Lemma tgt_inv
  p pc pc' i'
  (NCT: no_ct_prog p)
  (TGT: (uslh_prog p) [[pc']] = Some i')
  (SYNC: pc_sync p pc = Some pc') :
  exists i, p[[pc]] = Some i /\ match_inst_uslh p pc i i'.
Proof.
  exploit src_lookup; eauto. i. des.
  exploit src_inv; eauto. i. des; clarify. eauto.
Qed.

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
  - inv TGT; inv MATCH0; clarify.
    (* skip *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.
      esplits.
      { econs 2; econs. eauto. }
      econs. econs; eauto.
      exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
      destruct pc0. unfold pc_sync in *. ss. des_ifs_safe.
      replace (add n0 1) with (S n0) by lia.
      erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
      rewrite add_1_r. auto.
    (* asgn *)
    + exploit tgt_inv; eauto. i. des. inv x0.
      (* normal asgn *)
      * inv MATCH.
        replace (@nil direction) with ((@nil direction) ++ []) by ss.
        replace (@nil observation) with ((@nil observation) ++ []) by ss.
        esplits.
        { econs 2; [econs 2|econs]. eauto. }
        econs. econs; eauto.
        { exploit block_always_terminator_prog; try eapply x1; eauto. i. des.
          destruct pc0. unfold pc_sync in *. ss. des_ifs_safe.
          replace (add n0 1) with (S n0) by lia.
          erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
          rewrite add_1_r. auto. }
        { eapply unused_prog_lookup in UNUSED1; eauto.
          eapply unused_prog_lookup in UNUSED2; eauto. ss; des.
          inv REG. econs.
          - i. destruct (string_dec x x0); subst.
            { do 2 rewrite t_update_eq. apply eval_regs_eq; eauto. }
            { rewrite t_update_neq; auto. rewrite t_update_neq; auto. }
          - erewrite t_update_neq; eauto. }
      (* callee asgn *)
      * clarify. esplits; [econs|].
        eapply match_cfgs_ext_call; eauto.
        { inv REG. split; i.
          - des. rewrite t_update_neq; eauto.
          - rewrite t_update_neq; eauto. ii; clarify. }
        { rewrite t_update_eq. rewrite eval_unused_update; eauto.
          exploit unused_prog_lookup; try eapply x1; eauto. i. ss. }
    (* branch *)
    + exploit tgt_inv; eauto. i. des. inv x1.
      { inv MATCH. }
      clarify.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss; des.

      replace [DBranch b'] with ([DBranch b'] ++ []) by ss.
      replace [OBranch (not_zero n)] with ([OBranch (not_zero n)] ++ []) by ss.
      esplits.
      { econs; econs; eauto. simpl in H1. inv REG. rewrite H2 in H1.
        ss. rewrite <- H1. destruct ms; ss. erewrite eval_regs_eq; eauto. }
      destruct pc as [b o]. destruct pc0 as [b0 o0].
      destruct b'.
      (* true *)
      * eapply match_cfgs_ext_br_true1; eauto.
        { simpl. rewrite IN. ss. }
        { clear -H1 REG. inv REG. rewrite H0 in H1. ss. rewrite H0. ss.
          destruct ms; ss. unfold to_nat in H1. des_ifs_safe.
          destruct n; ss; clarify. }
        { ss. rewrite IN. ss. }
        { inv REG. red. eauto. }
      (* false *)
      * eapply match_cfgs_ext_br_false; try eapply H0; eauto.
        { clear -H1 REG. inv REG. rewrite H0 in H1. ss. rewrite H0. ss.
          destruct ms; ss. unfold to_nat in H1. des_ifs_safe.
          destruct n; ss; clarify. }
        { inv REG. red. eauto. }
    (* jump *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.

      exists (S_Running (l, 0, r0, m, stk, ms)). split; econs; [|econs|].
      * eapply ISMI_Jump; eauto.
      * econs; eauto.
        exploit wf_prog_lookup; try eapply x0; eauto. i.
        ss. unfold pc_sync, wf_lbl in *. ss. des_ifs_safe. ss.
        subst. inv WFP. rewrite Forall_forall in H1.
        eapply nth_error_In in Heq. eapply H1 in Heq.
        red in Heq. des. ss.
    (* load *)
    + exploit tgt_inv; eauto. i. des. inv x0. inv MATCH.
      exists (S_Running ((pc0 + 1), x !-> v'; r0, m, stk, ms)).

      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss; des.
      destruct pc as [b o]. destruct pc0 as [b0 o0].
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace [OLoad n] with ([OLoad n] ++ []) by ss.
      split; econs; eauto; [|econs|].
      * econs; eauto. inv REG. rewrite <- H1. ss.
        rewrite H3. ss. destruct ms; ss. erewrite eval_regs_eq; eauto.
      * econs; eauto.
        { exploit block_always_terminator_prog; try eapply x1; eauto. i. des.
          unfold pc_sync in *. ss. des_ifs_safe.
          replace (add o0 1) with (S o0) by lia.
          erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
          rewrite add_1_r. auto. }
        { red. splits; i.
          - destruct (string_dec x x0); subst.
            { do 2 rewrite t_update_eq; eauto. }
            { rewrite t_update_neq; eauto. rewrite t_update_neq; eauto.
              inv REG. eauto. }
          - inv REG. ss. des. rewrite t_update_neq; eauto. }
    (* store *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss. des.

      exists (S_Running (pc0+1, r0, (upd n m (eval r0 e')), stk, ms)).

      destruct pc as [b o]. destruct pc0 as [b0 o0].
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace [OStore n] with ([OStore n] ++ []) by ss.

      split.
      * econs; [|econs]. simpl. eapply ISMI_Store; eauto.
        inv REG. rewrite <- H1. rewrite H2. destruct ms; ss.
        erewrite eval_regs_eq; eauto.
      * dup REG. inv REG. econs.
        erewrite <- eval_regs_eq with (r := r0) (r' := r); eauto.
        econs; eauto.
        exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
        unfold pc_sync in *. ss. des_ifs_safe. replace (add o0 1) with (S o0) by lia.
        erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
        rewrite add_1_r. auto.
    (* call *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
    (* (* ctarget *) *)
    (* + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH. *)
    (*   esplits. *)
    (*   { econs. } *)
    (*   econs. econs. *)
    (* ret - return *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      destruct stk; try sfby ss.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.
      esplits.
      * econs 2; [|econs]. eapply ISMI_Ret; eauto.
      * econs. simpl in STK. des_ifs.
    (* ret - term *)
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      destruct stk.
      2:{ ss. des_ifs. }
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.
      esplits.
      * econs 2; [|econs]. eapply ISMI_Term; eauto.
      * econs.
  (* target = ctarget *)
  - inv TGT; clarify. esplits.
    + econs.
    + eapply match_cfgs_ext_ct2; eauto.
      exploit head_call_target; eauto. i. des; clarify; eauto.
  (* target = msf := (callee = (& (fst pc))) ? msf : 1 *)
  - (* exploit head_call_target; eauto. i. des; clarify. *)
    (* replace ((l0, 0) + 1) with (l0, 1) in x2 by ss. *)
    inv TGT; clarify.
    esplits; econs.
    econs; eauto.
    + unfold pc_sync. simpl. rewrite CT. destruct blk.
      { inv WFP. rewrite Forall_forall in H0. eapply nth_error_In in CT.
        eapply H0 in CT. red in CT. des; ss. }
      simpl. eauto.
    + red in REG. econs.
      * i. des. rewrite t_update_neq; eauto.
      * rewrite t_update_eq. eauto.
  (* call *)
  - inv TGT; clarify.
    destruct pc'0 as [l' o'].
    red in WFDS. inv WFDS. inv H2. red in H1. unfold is_some in H1.
    des_ifs.
    assert (i = ICTarget \/ i <> ICTarget).
    { destruct i; try (sfby (right; ii; clarify)). auto. }
    des; subst.
    + exploit head_call_target; eauto. i. des; clarify.
      replace [DCall(l0, 0)] with ([DCall (l0, 0)] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.

      exploit unused_prog_lookup; try eapply UNUSED1; eauto.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto.

      destruct (nth_error p l0) as [|blk' b'] eqn:CTSRC; cycle 1.
      {  unfold uslh_prog in Heq. des_ifs.
         hexploit new_prog_ct_cut; try eapply Heq0; eauto.
         { eapply new_prog_no_ct. eauto. }
         i. simpl in H. des_ifs_safe.
         rewrite nth_error_None in CTSRC.
         assert (l0 < Datatypes.length l1) by (rewrite <- nth_error_Some; ii; clarify).

         eapply mapM_perserve_len in Heq0. rewrite length_add_index in Heq0. lia. }

      destruct p0 as [blk' b']. destruct b'; cycle 1.
      { eapply no_ctarget_exists with (o:=0) in CTSRC; eauto. clarify. }

      des. esplits.
      * do 2 econs; eauto.
        inv REG.
        rewrite <- H8. simpl. rewrite H0. destruct ms; ss.
        erewrite eval_regs_eq; eauto.
      * simpl. rewrite andb_true_r. eapply match_cfgs_ext_ct1; eauto.
        { red. inv REG. eauto. }
        { inv REG. simpl. rewrite STK.
          exploit block_always_terminator_prog; try eapply CALL; eauto. i. des.
          destruct pc as [b o]. unfold pc_sync in *. ss. des_ifs_safe.
          replace (add o 1) with (S o) by lia.
          erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
          rewrite <- add_1_r. rewrite add_assoc. auto. }
        inv REG. simpl. rewrite MS. ss. rewrite H0.
        destruct ms; ss.
        { des_ifs. }
        { rewrite H0 in H8. ss. unfold to_fp in H8. des_ifs_safe.
          simpl in Heq2. clarify. destruct (l =? l0)%nat eqn:JMP; ss.
          + rewrite Nat.eqb_sym. rewrite JMP. auto.
          + rewrite Nat.eqb_sym. rewrite JMP. auto. }
    + replace [DCall(l', o')] with ([DCall (l', o')] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.

      exploit unused_prog_lookup; try eapply UNUSED1; eauto.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto.

      destruct (p[[(l', o')]]) eqn:ISRC; cycle 1.
      { simpl in ISRC. des_ifs.
        - destruct o'.
          + destruct p0 as [blk' b']. simpl in ISRC.
            assert (blk' = []) by des_ifs. clear ISRC. subst.
            eapply nth_error_In in Heq0.
            inv WFP. rewrite Forall_forall in H2. eapply H2 in Heq0.
            inv Heq0. red in H3. ss. lia.
          + esplits.
            { econs; [|econs]. eapply ISMI_Call_F; eauto.
              - rewrite <- H8. inv REG. simpl.
                rewrite H2. destruct ms; ss.
                erewrite eval_regs_eq; eauto.
              - ii. right. ss. }
          econs; eauto.
        - esplits.
          { econs; [|econs]. eapply ISMI_Call_F; eauto.
            - rewrite <- H8. inv REG. simpl.
              rewrite H2. destruct ms; ss.
              erewrite eval_regs_eq; eauto.
            - ii. ss. clarify. }
          econs; eauto. }      
      esplits.
      { econs.
        - eapply ISMI_Call_F; eauto.
          + rewrite <- H8. inv REG. simpl.
            rewrite H2. destruct ms; ss.
            erewrite eval_regs_eq; eauto.
          + ii. simpl in H0.
            destruct blk as [blk b]. simpl.
            destruct b; auto. destruct o'; auto.
            eapply ctarget_exists in H0. clarify.
        - econs. }
      econs; eauto.
  - inv TGT; clarify. esplits; econs.
  - inv TGT; clarify.
    esplits.
    + econs.
    + eapply match_cfgs_ext_br_true2; eauto.
      red. split.
      * ii. des. rewrite t_update_neq; eauto.
      * rewrite t_update_eq. simpl. ss.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      assert (exists blk, nth_error p l = Some (blk, false)).
      { inv WFP. rewrite Forall_forall in H0.
        destruct pc as [b o].
        simpl in BR. des_ifs_safe. destruct p0 as [blk' b'].
        simpl in BR. eapply nth_error_In in Heq.
        eapply H0 in Heq. red in Heq. des. simpl in Heq1.
        rewrite Forall_forall in Heq1. eapply nth_error_In in BR.
        eapply Heq1 in BR. simpl in BR. des.
        red in BR0. des_ifs. eauto. }
      des. unfold pc_sync. simpl. rewrite H.
      destruct blk as [|i blk].
      { inv WFP. rewrite Forall_forall in H1.
        eapply nth_error_In in H. eapply H1 in H. inv H.
        red in H2. ss; lia. }
      simpl. auto.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      * exploit tgt_inv; try eapply FROM; eauto. i. des.
        inv x1; [inv MATCH|]. clarify.
        destruct pc as [b o]. destruct pc' as [b' o'].
        exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
        simpl. unfold pc_sync in *. ss. des_ifs_safe.
        rewrite add_1_r.
        erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
        rewrite <- add_1_r. rewrite add_assoc. auto.
      * split; ii.
        { des. rewrite t_update_neq; eauto. }
        { rewrite t_update_eq. eauto. }
Qed.

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
  inv TGT. eapply wf_ds_app in WFDS. des.
  exploit ultimate_slh_bcc_single; try eapply H0; eauto.
  i. des.
  exploit IHn; try eapply H5; eauto.
  i. des. esplits; eauto.
  eapply multi_ideal_inst_trans2; eauto.
Qed.

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
  0 < Datatypes.length m.

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

Definition wf_stk (p: prog) (stk: list cptr) : Prop :=
  forall l o, In (l, o) stk -> exists e, p[[(l, o - 1)]] = Some <{{ call e }}> /\ o > 0.


Lemma wf_stk_preserve_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  wf_stk p stk'.
Proof.
  inv STEP; eauto.
  { red. ii. simpl in H. des; eauto.
    destruct pc. simpl in H. clarify.
    replace ((add n0 1) - 1) with n0 by lia. esplits; eauto. lia. }
  red. i. eapply WFSTK. simpl. auto.
Qed.

Lemma nonempty_mem_preserve_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  Datatypes.length m = Datatypes.length m'.
Proof.
  inv STEP; eauto. rewrite upd_length. eauto.
Qed.

Require Import Stdlib.Program.Equality.

Lemma wf_stk_preserve_multi_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  wf_stk p stk'.
Proof.
  dependent induction STEP; auto.
  destruct ic2. 2-4: inv STEP; inv H0.
  destruct a as [ [ [ [pc'' r''] m''] stk''] ms''].
  eapply wf_stk_preserve_ideal in H; eauto.
Qed.

Lemma ideal_res_pc_exists
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (* (WFDS: wf_ds' (uslh_prog p) ds) *)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  exists i, p[[pc']] = Some i.
Proof.
  inv STEP.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
    intros (i'' & PC').
    destruct pc as [b o]. ss. des_ifs_safe. destruct p0 as [blk ct].
    destruct b'.
    { inv WFP. rewrite Forall_forall in H0.
      eapply nth_error_In in Heq, H11. eapply H0 in Heq.
      red in Heq. des. rewrite Forall_forall in Heq1. eapply Heq1 in H11.
      simpl in H11. des. red in H1. des_ifs_safe. simpl.
      rewrite Heq2. destruct l0; simpl; eauto.
      eapply nth_error_In in Heq2. eapply H0 in Heq2. red in Heq2. des.
      red in Heq2. ss; lia. }
    ss. des_ifs; ss; eauto.
  - destruct pc as [b o]. ss. des_ifs_safe. destruct p0 as [blk ct].
    inv WFP. rewrite Forall_forall in H0.
    eapply nth_error_In in Heq, H11. eapply H0 in Heq. red in Heq. des.
    rewrite Forall_forall in Heq1. eapply Heq1 in H11.
    simpl in H11. des. red in H11. des_ifs_safe. simpl.
    destruct l0; simpl; eauto.
    eapply nth_error_In in Heq2. eapply H0 in Heq2. red in Heq2. des.
    red in Heq2. ss; lia.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - destruct pc', blk. ss. subst. rewrite H14. ss. destruct l0; eauto.
    inv WFP. rewrite Forall_forall in H0.
    eapply nth_error_In in H14. eapply H0 in H14. red in H14. des.
    red in H14. ss.
  - destruct pc' as [b' o']. specialize (WFSTK b' o').
    exploit WFSTK; [simpl; auto|]. i. des.
    exploit block_always_terminator_prog; try eapply x0; eauto.
    unfold inc. replace (add (o' - 1) 1) with o' by lia.
    i. eauto.
Qed.

Lemma multi_ideal_res_pc_exists_aux :
  forall p ic1 ic2 ds os,
    p |- <(( ic1 ))>  -->i*_ ds ^^ os <(( ic2 ))> ->
    forall pc r m stk ms pc' r' m' stk' ms',
      ic1 = S_Running (pc, r, m, stk, ms) ->
      ic2 = S_Running (pc', r', m', stk', ms') ->
      wf_stk p stk -> wf_prog p -> p[[pc]] <> None -> exists i, p[[pc']] = Some i.
Proof.
  induction 1; subst; i.
  - subst. clarify. destruct (p[[pc']]); eauto. clarify.
  - destruct ic2. 2-4: inv H0; inv H7; inv H6.
    destruct a as [ [ [ [pc'' r''] m''] stk''] ms'']. subst.
    exploit IHmulti_ideal_inst.
    { eauto. }
    { eauto. }
    { eapply wf_stk_preserve_ideal in H; eauto. }
    { eauto. }
    { eapply ideal_res_pc_exists in H; eauto. des. ii. clarify. }
    eauto.
Qed.

Lemma multi_ideal_res_pc_exists
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (PC: p[[pc]] <> None)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  exists i, p[[pc']] = Some i.
Proof.
  eapply multi_ideal_res_pc_exists_aux; eauto.
Qed.

Lemma nonempty_mem_preserve_multi_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  Datatypes.length m = Datatypes.length m'.
Proof.
  dependent induction STEP; eauto.
  destruct ic2. 2-4: inv STEP; inv H0.
  destruct a as [ [ [ [pc'' r''] m''] stk''] ms'']. subst.
  eapply nonempty_mem_preserve_ideal in H.
  rewrite H. eapply IHSTEP; eauto.
Qed.

Lemma seq_ideal_safety_preservation
  p c pc r m stk
  (CFG: c = (pc, r, m, stk))
  (MEM: nonempty_mem m)
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (SEQ: seq_exec_safe p c) :
  ideal_exec_safe p (c, false).
Proof.
  red. ii. destruct ict as [c' ms]. subst.
  (* destruct c as [cl stk]. destruct cl as [cl m]. destruct cl as [pc r]. *)
  destruct c' as [cl' stk']. destruct cl' as [cl' m']. destruct cl' as [pc' r'].
  destruct ms; cycle 1.
  { red in SEQ.
    exploit multi_ideal_nonspec_seq; eauto. i.
    eapply SEQ in x0. des. eapply seq_ideal_nonspec in x0.
    des. eauto. }
  destruct (p[[pc']]) eqn:PC'; cycle 1.
  { eapply multi_ideal_res_pc_exists in H; eauto; des; clarify.
    ii. red in SEQ. exploit SEQ; [econs|]. i. des. inv x0; clarify. }
  destruct i.
  - esplits. econs; eauto.
  - esplits. econs 2. eauto.
  - esplits. econs 3; eauto.
  - esplits. econs 4; eauto.
  - assert (MEM': nonempty_mem m').
    { eapply nonempty_mem_preserve_multi_ideal in H.
      unfold nonempty_mem in *. lia. }
    assert (exists v, nth_error m' 0 = Some v).
    { red in MEM'. erewrite <- nth_error_Some in MEM'.
      destruct (nth_error m' 0); eauto. clarify. }
    des. esplits. econs 5; ss; eauto.
  - esplits. econs 6; ss; eauto.
  - exists [DCall (0, 0)], [OCall 0].
    red in WFP. des. red in WFP.
    assert (exists blk b, nth_error p 0 = Some (blk, b)).
    { erewrite <- nth_error_Some in WFP. destruct (nth_error p 0); clarify.
      destruct p0. eauto. }
    des. destruct b.
    + esplits. econs; eauto.
    + esplits. eapply ISMI_Call_F; eauto. ii. ss. clarify.
      left. ss.
  - exfalso. eapply no_ct_prog_src; eauto.
  - destruct stk'.
    + esplits. eapply ISMI_Term. eauto.
    + esplits. eapply ISMI_Ret. eauto.
      Unshelve. all: repeat (econs).
Qed.

Lemma seq_spec_safety_preservation
  p b c c' pc r m stk
  (CFG: c = (pc, r, m, stk))
  (MEM: nonempty_mem m)
  (WFSTK: wf_stk p stk)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p c)
  (MATCH: match_cfgs_ext p (S_Running (c, false)) (S_Running (c', b, false))) :
  spec_exec_safe (uslh_prog p) (c', b, false).
Proof.
  ii. eapply seq_ideal_safety_preservation in SEQ; eauto.

  red in SEQ.
  exploit ultimate_slh_bcc'; eauto.
  i. des. destruct ic2.
  - exploit SEQ; eauto. i. des.
    (* match -> source progress -> target progress *)
    inv x1.
    + inv MATCH0. inv x2.
      * exploit src_inv; eauto. i. des. inv x2. inv MATCH0.
        esplits. econs; eauto.
      * exploit src_inv; eauto. i. des. inv x1. inv MATCH0.
        esplits. econs 2; eauto.
      * exploit src_inv; eauto. i. des. inv x2; [ss|].
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto.

        assert (to_nat (eval r' <{{ (msf = 1) ? 0 : e }}>) = Some n').
        { ss. inv REG. rewrite H1. destruct ms; ss; eauto.
          rewrite <- H9. erewrite <- eval_regs_eq; eauto. }
        esplits. econs 3; eauto.
      * exploit src_inv; eauto. i. des. inv x2. inv MATCH0.
        esplits. econs 4; eauto.
      * exploit src_inv; eauto. i. des. inv x1. inv MATCH0.
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto. ss. des.

        esplits. econs 5; eauto. rewrite <- H10.
        inv REG. simpl. rewrite H1. destruct ms; ss.
        erewrite <- eval_regs_eq; eauto.
      * exploit src_inv; eauto. i. des. inv x2. inv MATCH0.
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto. ss. des.

        esplits. econs 6; eauto. erewrite <- H10.
        inv REG. simpl. rewrite H1. destruct ms; ss.
        erewrite <- eval_regs_eq; eauto.
      * exploit src_inv; eauto. i. des. inv x2; [ss|].
        esplits. econs 2; eauto.
      * exploit src_inv; eauto. i. des. inv x2; [ss|].
        esplits. econs 2; eauto.
      * destruct stk'.
        { ss. des_ifs. }
        exploit src_inv; eauto. i. des. inv x2. inv MATCH0.
        esplits. econs 9; eauto.
      * destruct stk'; [|ss].
        exploit src_inv; eauto. i. des. inv x2. inv MATCH0.
        esplits. econs 10; eauto.
    + esplits. econs. eauto.
    + esplits. econs 2; eauto.
    + inv REG.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto.

      destruct (to_fp (eval r' <{{ (msf = 1) ? & 0 : fp }}>)) eqn:FP.
      2:{ ss. rewrite H1 in FP. ss. destruct ms; ss.
          assert (exists l, to_fp (eval r0 fp) = Some l).
          { inv x2; clarify; eauto. }
          des. erewrite eval_regs_eq with (r := r0) (r' := r') in H2; try eapply H0; eauto.
          clarify. }
      esplits. eapply SpecSMI_Call; eauto.
    + esplits. econs 2; eauto.
    + esplits. eapply SpecSMI_Jump; eauto.
    + esplits. econs 2; eauto.
  - clear - x0. exfalso. remember false. clear Heqb.
    dependent induction x0. destruct ic2. 3-4: inv x0; inv H0.
    2:{ inv H. }
    destruct a. eapply IHx0; eauto.
  - inv x1. exists [], [], S_Fault.
    eapply SpecSMI_Fault; eauto.
  - inv x1.
Unshelve. all: repeat econs.
Qed.

Lemma seq_spec_safety_preservation_init_aux
  p c c' r r' m
  (FST: first_blk_call p)
  (CFG1: c = ((0,0), r, m, @nil cptr))
  (CFG2: c' = ((0,0), r', m, @nil cptr))
  (CALLEE: r' ! callee = FP 0)
  (MEM: nonempty_mem m)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p c)
  (REG: Rsync r r' false) :
  spec_exec_safe (uslh_prog p) (c', true, false).
Proof.
  red. i.
  assert (CT: (uslh_prog p)[[(0, 0)]] = Some <{{ ctarget }}>).
  { red in FST. des_ifs. eapply ctarget_exists; eauto. }
  exploit head_call_target; eauto. i. des; clarify.
  replace ((0,0) + 1) with (0,1) in x2 by ss.
  destruct n.
  { inv H. esplits. econs. eauto. }
  destruct n.
  { inv H. inv H6. inv H1. esplits. econs 2. eauto. }
  inv H. inv H1; clarify. inv H6. inv H0; clarify.
  replace ((0,1) + 1) with (0,2) in H5 by ss.
  eapply seq_spec_safety_preservation in SEQ; eauto.
  { ii. ss. }
  econs. econs.
  { red in FST. des_ifs. unfold pc_sync. ss. des_ifs_safe.
    simpl in Heq1. subst. red in WFP. des. rewrite Forall_forall in WFP0.
    ss. exploit WFP0; eauto. i. red in x0. des. red in x0. ss. }
  { red. inv REG. split.
    - i. des. rewrite t_update_neq; eauto.
    - ss. rewrite CALLEE. ss. }
  { ss. }
Qed.

Lemma seq_spec_safety_preservation_init
  p r r' m
  (FST: first_blk_call p)
  (CALLEE: r' ! callee = FP 0)
  (MEM: nonempty_mem m)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p ((0,0), r, m, @nil cptr))
  (REG: Rsync r r' false) :
  spec_exec_safe (uslh_prog p) (((0,0), r', m, @nil cptr), true, false).
Proof.
  eapply seq_spec_safety_preservation_init_aux; eauto.
Qed.
