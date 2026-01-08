(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import TestingLib.
From SECF Require Import Utils.
From SECF Require Import MiniCET MiniCET_Index Linear.
From SECF Require Import Safe.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import ExtLib.Data.Monads.OptionMonad.
From SECF Require Import Maps MapsFunctor.

Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(** Statement related with Linearized machine level semantics
    for giving guidelines for testing. *)

Module LCC := LinearCommon(TotalMap).
Import LCC.

(** Sequential small-step semantics for Machine *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  state cfg -> state cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      nth_error p pc = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (add pc 1, rs, m, stk) ))>
  | SSMI_Ctarget : forall pc rs m stk,
      nth_error p pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (add pc 1, rs, m, stk) ))>

  | SSMI_Asgn : forall pc r m sk e x,
      nth_error p pc = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (add pc 1, (x !-> (eval r e); r), m, sk) ))>

  | SSMI_Branch : forall pc pc' r m sk e n l,
      nth_error p pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then l else add pc 1) ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m, sk) ))>

  | SSMI_Jump : forall l pc r m sk,
      nth_error p pc = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (l, r, m, sk) ))>

  | SSMI_Load : forall pc r m sk x e n v',
      nth_error p pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OLoad n] <(( S_Running (add pc 1, (x !-> v'; r), m, sk) ))>

  | SSMI_Store : forall pc r m sk e e' n,
      nth_error p pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OStore n] <(( S_Running (add pc 1, r, upd n m (eval r e'), sk) ))>

  | SSMI_Call : forall pc r m sk e l,
      nth_error p pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OCall l] <(( S_Running (l, r, m, ((add pc 1)::sk)) ))>

  | SSMI_Ret : forall pc r m sk pc',
      nth_error p pc = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, pc'::sk) ))> -->^[] <(( S_Running (pc', r, m, sk) ))>

  | SSMI_Term : forall pc r m,
      nth_error p pc = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, []) ))> -->^[] <(( S_Term ))>

  where "p |- <(( c ))> -->^ os <(( ct ))>" :=
      (seq_eval_small_step_inst p c ct os).

(** Sequential multi-step relation *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->*^' os '<((' ct '))>'"
      (at level 40, c constr, ct constr).

Inductive multi_seq_inst (p : prog) (c : @state cfg) : @state cfg -> obs -> Prop :=
  | multi_seq_inst_refl : p |- <(( c ))> -->*^[] <(( c ))>
  | multi_seq_inst_trans (c' c'' : @state cfg) (os1 os2 : obs) :
      p |- <(( c ))> -->^os1 <(( c' ))> ->
      p |- <(( c' ))> -->*^os2 <(( c'' ))> ->
      p |- <(( c ))> -->*^(os1 ++ os2) <(( c'' ))>

  where "p |- <(( c ))> -->*^ os <(( ct ))>" :=
      (multi_seq_inst p c ct os).

(** Speculative small-step semantics for Machine *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->m_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive spec_eval_small_step (p:prog):
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      nth_error p pc = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      nth_error p pc = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      nth_error p pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then l else (add pc 1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      nth_error p pc = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((l, r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      nth_error p pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[OLoad n] <(( S_Running ((add pc 1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      nth_error p pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[OStore n] <(( S_Running ((add pc 1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      nth_error p pc = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      ms' = ms || negb ((pc' =? l) (* && (snd pc' =? 0) *)) (* YH: (snd pc' =? 0) ??? *) ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (add pc 1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ms,
      nth_error p pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m, sk), false, ms) ))>
  | SpecSMI_CTarget_F : forall pc r m sk ms,
      nth_error p pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Fault ))>
  | SpecSMI_Ret : forall pc r m sk pc' ms,
      nth_error p pc = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((pc', r, m, sk), false, ms) ))>
  | SpecSMI_Term : forall pc r m ms,
      nth_error p pc = Some <{{ ret }}> -> 
      p |- <(( S_Running ((pc, r, m, []), false, ms) ))> -->m_[]^^[] <(( S_Term ))>
  | SpecSMI_Fault : forall pc r m sk ms i,
      i <> <{{ ctarget }}> ->
      nth_error p pc = Some i ->
      p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->m_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->m_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

(** Speculative multi-step relation *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->m*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> nat -> Prop :=
  |multi_spec_inst_refl sc : p |- <(( sc ))> -->m*_[]^^[]^^0 <(( sc ))>
  |multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->m_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->m*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->m*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>

  where "p |- <(( sc ))> -->m*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

From SECF Require Import sflib.

Definition match_reg (p: MiniCET.prog) (r: MCC.reg) (r': reg) : Prop :=
  forall x, val_inject p (r ! x) (r' ! x).

Definition match_reg_src (p: MiniCET.prog) (r: MCC.reg) (r': reg) (ms: bool) : Prop :=
  (forall x, x <> msf /\ x <> callee -> val_inject p (r ! x) (r' ! x))
/\ r' ! msf = N (if ms then 1 else 0).

Definition match_mem (p: MiniCET.prog) (m m': mem) : Prop :=
  forall i, match nth_error m i, nth_error m' i with
       | None, _ => True
       | Some v, Some v' => val_inject p v v'
       | Some v, None => False
       end.

Variant match_states (p: MiniCET.prog) : state MCC.spec_cfg -> state spec_cfg -> Prop :=
| match_states_intro pc r m stk ct ms pc' r' m' stk'
  (PC: pc_inj p pc = Some pc')
  (REG: match_reg p r r')
  (MEM: match_mem p m m')
  (STK: map_opt (pc_inj p) stk = Some stk') :
  match_states p (S_Running (pc, r, m, stk, ct, ms)) (S_Running (pc', r', m', stk', ct, ms))
| match_states_term :
  match_states p S_Term S_Term
| match_states_fault :
  match_states p S_Fault S_Fault.

Definition match_dir (p: MiniCET.prog) (d: MiniCET.direction) (d': direction) : Prop :=
  match d, d' with
  | MiniCET.DCall pc, DCall l => pc_inj p pc = Some l
  | MiniCET.DBranch b, DBranch b' => b = b'
  | _, _ => False
  end.

Definition match_dirs (p: MiniCET.prog) (ds: MiniCET.dirs) (ds': dirs) : Prop :=
  Forall2 (match_dir p) ds ds'.

Definition match_ob (p: MiniCET.prog) (o: MiniCET.observation) (o': observation) : Prop :=
  match o, o' with
  | MiniCET.OBranch b, OBranch b' => b = b'
  | MiniCET.OLoad n, OLoad n' => n = n'
  | MiniCET.OStore n, OStore n' => n = n'
  | MiniCET.OCall l, OCall l' => pc_inj p (l, 0) = Some l'
  | _, _ => False
  end.

Definition match_obs (p: MiniCET.prog) (ds: MiniCET.obs) (ds': obs) : Prop :=
  Forall2 (match_ob p) ds ds'.

(* wf *)

Definition wf_dir (p: prog) (d: direction) : Prop :=
  match d with
  | DCall pc' => is_some (nth_error p pc') = true
  | _ => True
  end.

Definition wf_ds (p: prog) (ds: dirs) : Prop :=
  Forall (wf_dir p) ds.

Lemma pc_inj_iff p pc l :
  pc_inj p pc = Some l <-> pc_inj_inv p l = Some pc.
Proof.
  unfold pc_inj, pc_inj_inv. destruct pc. split.
  - eapply coord_flat_inverse.
  - eapply flat_coord_inverse.
Qed.

Lemma src_inv
  (p: MiniCET.prog) (tp: prog) pc l i
  (TRANSL: machine_prog p = Some tp)
  (SRC: p[[pc]] = Some i)
  (INJ: pc_inj p pc = Some l) :
  nth_error tp l = Some i.
Proof.
Admitted.

Lemma tgt_inv
  (p: MiniCET.prog) (tp: prog) pc l i
  (TRANSL: machine_prog p = Some tp)
  (TGT: nth_error tp l = Some i)
  (INJ: pc_inj p pc = Some l) :
  p[[pc]] = Some i.
Proof.
Admitted.

Lemma wf_dir_inj
  (p: MiniCET.prog) (tp: prog) d td
  (TRANSL: machine_prog p = Some tp)
  (WFT: wf_dir tp td)
  (MATCH: match_dir p d td):
  wf_dir' p d.
Proof.
  destruct td; ss; des_ifs_safe.
  { red in MATCH. des_ifs. }
  red in MATCH. des_ifs.
  admit.
Admitted.

Lemma wf_ds_inj
  (p: MiniCET.prog) (tp: prog) ds tds
  (TRANSL: machine_prog p = Some tp)
  (WFT: wf_ds tp tds)
  (MATCH: match_dirs p ds tds):
  wf_ds' p ds.
Proof.
Admitted.

Lemma minicet_linear_bcc_single
  (p: MiniCET.prog) (tp: prog) sc tc tct tds tos
  (TRANSL: machine_prog p = Some tp)
  (SAFE: exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>)
  (MATCH: match_states p (S_Running sc) (S_Running tc))
  (TGT: tp |- <(( S_Running tc ))> -->m_ tds ^^ tos  <(( tct ))>) :
  exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>
             /\ match_states p sct tct
             /\ match_dirs p ds tds /\ match_obs p os tos.
Proof.
Admitted.

Lemma minicet_linear_bcc
  (p: MiniCET.prog) (tp: prog) sc tc tct tds tos n
  (TRANSL: machine_prog p = Some tp)
  (SAFE: spec_exec_safe p sc)
  (MATCH: match_states p (S_Running sc) (S_Running tc))
  (TGT: tp |- <(( S_Running tc ))> -->m*_ tds ^^ tos ^^ n  <(( tct ))>) :
  exists ds os sct, p |- <(( S_Running sc ))> -->*_ ds ^^ os ^^ n  <(( sct ))>
             /\ match_states p sct tct
             /\ match_dirs p ds tds /\ match_obs p os tos.
Proof.
Admitted.

Definition spec_same_obs_machine p pc r1 r2 m1 m2 stk b : Prop :=
  forall ds n os1 os2 c1 c2 (WFDS: wf_ds p ds),
  p |- <(( S_Running (pc, r1, m1, stk, b, false) ))> -->m*_ds^^os1^^n <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b, false) ))> -->m*_ds^^ os2^^n <(( c2 ))> -> (* YH: Yan said this can be generalized different numbers of steps. *)
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition relative_secure_machine (p:MiniCET.prog) (tp: prog) (trans : MiniCET.prog -> option prog)
  (r1 r2 r1' r2' : reg) (m1 m2 m1' m2' : mem) : Prop :=
  seq_same_obs p (0,0) r1 r2 m1 m2 [] ->
  match_reg_src p r1 r1' false -> match_reg_src p r2 r2' false ->
  match_mem p m1 m1' -> match_mem p m2 m2' ->
  trans p = Some tp ->
  spec_same_obs_machine tp 0 r1' r2' m1' m2' [] true.

Lemma spec_eval_relative_secure_machine
  p r1 r2 r1' r2' m1 m2 m1' m2' tp
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (NEM1: nonempty_mem m1)
  (NEM2: nonempty_mem m2)
  (CALLEE1: r1' ! callee = N 0)
  (CALLEE2: r2' ! callee = N 0)
  (SAFE1: seq_exec_safe p ((0,0), r1, m1, []))
  (SAFE2: seq_exec_safe p ((0,0), r2, m2, []))
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p) :
  relative_secure_machine p tp (fun p => machine_prog (uslh_prog p)) r1 r2 r1' r2' m1 m2 m1' m2'.
Proof.
  red. i.
  set (ir1 := (msf !-> N 0; callee !-> (FP 0); r1)).
  set (ir2 := (msf !-> N 0; callee !-> (FP 0); r2)).

  hexploit (spec_eval_relative_secure p r1 r2 ir1 ir2 m1 m2); eauto.
  intros REL. red in REL.

  assert (IREG1: Rsync r1 ir1 false).
  { split; subst ir1; ss. ii. des.
    do 2 (rewrite MiniCET_Index.t_update_neq; eauto). }

  assert (IREG2: Rsync r2 ir2 false).
  { split; subst ir2; ss. ii. des.
    do 2 (rewrite MiniCET_Index.t_update_neq; eauto). }

  hexploit REL; eauto.
  intros SPEC.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE1; eauto.
  { subst ir1. rewrite MiniCET_Index.t_update_neq; eauto. ii; clarify. }
  intros ISAFE1.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE2; eauto.
  { subst ir2. rewrite MiniCET_Index.t_update_neq; eauto. ii; clarify. }
  intros ISAFE2.

  red. i.
  hexploit minicet_linear_bcc; [|eapply ISAFE1| |eapply H5|]; eauto.
  { econs; ss.
    - unfold pc_inj. admit. (* nonempty *)
    - red. i. red in H0.
      destruct (string_dec x callee).
      { subst. subst ir1. rewrite CALLEE1. ss.
        admit. }
      destruct (string_dec x msf).
      { des. subst. subst ir1. rewrite H7. ss. }
      des. exploit H0; eauto. i. des. eauto.
      inv IREG1. rewrite <- H8; eauto.
      unfold val_inject in *. des_ifs_safe.
      admit.
    - red. i. specialize (H2 i). des_ifs_safe.
      unfold val_inject in *. des_ifs_safe. admit. }
  i. des.
  hexploit minicet_linear_bcc; [|eapply ISAFE2| |eapply H6|]; eauto.
  { admit. (* see above *) }
  i. des.

  assert (UNIQ: ds0 = ds1).
  { admit. }
  subst.
  red in SPEC. hexploit SPEC; cycle 1.
  { eapply H7. }
  { eapply H11. }
  2:{ eapply wf_ds_inj; eauto. }
  i. admit. (* H15 H14 H10 *)
Admitted.
