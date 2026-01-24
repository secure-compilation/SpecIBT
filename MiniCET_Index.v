(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
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

Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

Module MCC := MiniCETCommon(TotalMap).
Import MCC.
Import FunctionalExtensionality.

Notation t_update_eq := TotalMap.t_update_eq.
Notation t_update_neq := TotalMap.t_update_neq.

(* %s/\s\+$//e to strip trailing whitespace *)

(** Sequential small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  @state cfg -> @state cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (pc+1, rs, m, stk) ))>
  | SSMI_Asgn : forall pc r m sk e x,
     p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (pc+1, (x !-> (eval r e); r), m, sk) ))>
  | SSMI_Branch : forall pc pc' r m sk e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then (l,0) else pc+1) ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Jump : forall l pc r m sk,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running ((l,0), r, m, sk) ))>
  | SSMI_Load : forall pc r m sk x e n v',
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OLoad n] <(( S_Running (pc+1, (x !-> v'; r), m, sk) ))>
  | SSMI_Store : forall pc r m sk e e' n,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OStore n] <(( S_Running (pc+1, r, upd n m (eval r e'), sk) ))>
  | SSMI_Call : forall pc r m sk e l,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OCall l] <(( S_Running ((l,0), r, m, ((pc+1)::sk)) ))>
  | SSMI_Ret : forall pc r m sk pc',
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, pc'::sk) ))> -->^[] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Term : forall pc r m,
      p[[pc]] = Some <{{ ret}}> ->
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

(** Speculative small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive spec_eval_small_step (p:prog):
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then (l, 0) else (pc+1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running (((l,0), r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore n] <(( S_Running ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) (* YH: (snd pc' =? 0) ??? *) ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ct ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ct, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m, sk), false, ms) ))>
  (* | SpecSMI_CTarget_F : forall pc r m sk ms, *)
  (*     p[[pc]] = Some <{{ ctarget }}> -> *)
  (*     p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Fault ))> *)
  | SpecSMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc', r, m, sk), false, ms) ))>
  | SpecSMI_Term : forall pc r m ms,
      p[[pc]] = Some <{{ ret }}> -> 
      p |- <(( S_Running ((pc, r, m, []), false, ms) ))> -->_[]^^[] <(( S_Term ))>
  | SpecSMI_Fault : forall pc r m sk ms i,
      i <> <{{ ctarget }}> ->
      p[[pc]] = Some i ->
      p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

(** Speculative multi-step relation *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> nat -> Prop :=
  |multi_spec_inst_refl sc : p |- <(( sc ))> -->*_[]^^[]^^0 <(( sc ))>
  |multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>

  where "p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

(** Ideal small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive ideal_eval_small_step_inst (p:prog) :
  @state ideal_cfg -> @state ideal_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, r, m, sk), ms) ))>
  | ISMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m, sk), ms) ))>
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      (if ms then Some 0 else to_nat (eval r e)) = Some n' ->
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) ->
      ms' = (ms || (negb (Bool.eqb b b'))) ->
      (* uslh imposes that if we're already speculating the branch condition is always false *)
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running (((l,0), r, m, sk), ms) ))>
  | ISMI_Load : forall pc r m sk x e n me v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      me = (if ms then (ANum 0) else e) ->
      to_nat (eval r me) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m, sk), ms) ))>
  | ISMI_Store : forall pc r m sk e e' me n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      me = (if ms then (ANum 0) else e) ->
      to_nat (eval r me) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OStore n] <(( S_Running ((pc+1, r, upd n m (eval r e'), sk), ms) ))>
  (* no fault if program goes to the beginning of some procedure block, whether or not it's the intended one *)
  | ISMI_Call : forall pc pc' r m sk e l (ms ms' : bool) blk,
      p[[pc]] = Some <{{ call e }}> ->
      (if ms then Some 0 else to_fp (eval r e)) = Some l ->
      (*l' = (if ms then 0 else l) -> (* uslh masking *)*)
      ms' = ms || negb (fst pc' =? l) ->
      nth_error p (fst pc') = Some blk -> (* always established by well-formed directive *)
      snd blk = true ->
      snd pc' = 0 ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (pc+1)::sk), ms') ))>
  (* fault if attacker pc goes to non-proc block or into the middle of any block *)
  (* directives are always "well-formed": nth_error p (fst pc') = Some blk /\ nth_error blk (snd pc') = Some i always established. *)
  | ISMI_Call_F : forall pc pc' r m sk e l (ms : bool),
      p[[pc]] = Some <{{ call e }}> ->
      (if ms then Some 0 else to_fp (eval r e)) = Some l ->
      (* l' = (if ms then 0 else l) -> (* uslh masking *) *)
      (forall blk, nth_error p (fst pc') = Some blk -> snd blk = false \/ snd pc' <> 0) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l] <(( S_Fault ))>
  | ISMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), ms) ))> -->i_[]^^[] <(( S_Running ((pc', r, m, sk), ms) ))>
  | ISMI_Term : forall pc r m ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, []), ms) ))> -->i_[]^^[] <(( S_Term ))>

  where "p |- <(( ic ))> -->i_ ds ^^ os  <(( ict ))>" :=
    (ideal_eval_small_step_inst p ic ict ds os).

(** Ideal multi-step relation *)

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive multi_ideal_inst (p:prog) :
  @state ideal_cfg -> @state ideal_cfg -> dirs -> obs -> Prop :=
  | multi_ideal_inst_refl ic : p |- <(( ic ))> -->i*_[]^^[] <(( ic ))>
  | multi_ideal_inst_trans ic1 ic2 ic3 ds1 ds2 os1 os2 :
      p |- <(( ic1 ))> -->i_ds1^^os1 <(( ic2 ))> ->
      p |- <(( ic2 ))> -->i*_ds2^^os2 <(( ic3 ))> ->
      p |- <(( ic1 ))> -->i*_(ds1++ds2)^^(os1++os2) <(( ic3 ))>
  where "p |- <(( ic ))> -->i*_ ds ^^ os <(( ict ))>" :=
    (multi_ideal_inst p ic ict ds os).

(** * Backwards Compiler Correctness of Ultimate Speculative Load Hardening *)

(* Synchronization Relation *)

Definition msf_lookup_sc (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  r ! msf.

Definition msf_lookup_ic (ic: ideal_cfg) : val :=
let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  r ! msf.

Definition callee_lookup_sc (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  r ! callee.

Definition callee_lookup_ic (ic: ideal_cfg) : val :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  r ! callee.

Definition ms_true_sc (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in ms.

Definition ms_true_ic (ic: ideal_cfg) : bool :=
  let '(c, ms) := ic in ms.

(* Section BCC. *)

Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

(* given src pc and program, obtain tgt pc *)
Definition pc_sync (p: prog) (pc: cptr) : option cptr :=
  match nth_error p (fst pc) with
  | Some blk => match nth_error (fst blk) (snd pc) with
               | Some i =>
                   let acc1 := if (Bool.eqb (snd blk) true) then 2 else 0 in
                   let insts_before_pc := (firstn (snd pc) (fst blk)) in
                   let acc2 := fold_left (fun acc (i: inst) => if (is_br_or_call i)
                                                            then (add acc 1)
                                                            else acc)
                                 insts_before_pc acc1
                   in Some ((fst pc), add (snd pc) acc2)
               | _ => None
               end
  | _ => None
  end.

(* sync src and tgt registers *)
Definition r_sync (r: reg) (ms: bool) : reg :=
   msf !-> N (if ms then 1 else 0); r.

(* 
   eval (r_sync r ms) e = eval r e 
   eval (msf !-> N (if ms then 1 else 0); r) e = eval r e
   This can only be the case if msf isn't used in e. 
   We know that this is the case (unused_p_msf).
   eval comes down to looking up strings in the register state.
   so as long as msf isn't used in the expression, then a new mapping 
   in the register state will not affect the evaluation of the expression.

Previously:
forall (X : string) (st : total_map nat) (ae : aexp) (n : nat),
       a_unused X ae -> aeval (X !-> n; st) ae = aeval st ae

Lemma aeval_beval_unused_update : forall X st n,
  (forall ae, a_unused X ae ->
    aeval (X !-> n; st) ae = aeval st ae) /\
  (forall be, b_unused X be ->
    beval (X !-> n; st) be = beval st be).
intros X st n. apply aexp_bexp_mutind; intros;
  simpl in *; try reflexivity;
  try (
    rewrite H; [| tauto]; rewrite H0; [| tauto]; reflexivity
  ).
  - rewrite t_update_neq; eauto.
  - rewrite H; [| tauto]. rewrite H0; [| tauto]. rewrite H1; [| tauto].
    reflexivity.
  - rewrite H; auto.

*)

Lemma eval_unused_update : forall (x : string) (r: reg) (e: exp) (v: val),
  e_unused x e -> eval (x !-> v; r) e = eval r e.
Proof.
  intros until v. induction e; intros; simpl in *; try reflexivity.
  - eapply t_update_neq; auto.
  - destruct H. specialize (IHe1 H). specialize (IHe2 H0).
    rewrite IHe1, IHe2. auto.
  - destruct H, H0. specialize (IHe1 H). specialize (IHe2 H0).
    specialize (IHe3 H1). rewrite IHe1, IHe2, IHe3.
    destruct (to_nat (eval r e1)) eqn:Heval1; auto.
Qed.

Fixpoint map_opt {S T} (f: S -> option T) l : option (list T):=
  match l with
  | [] => Some []
  | a :: l' => match f a with
             | Some a' =>
                 match map_opt f l' with
                 | Some l'' => Some (a' :: l'')
                 | _ => None
                 end
             | _ => None
             end
  end.

(* given src state and program, obtain tgt state *)
Definition spec_cfg_sync (p: prog) (ic: ideal_cfg): option spec_cfg :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  match pc_sync p pc, map_opt (pc_sync p) stk with
  | Some pc', Some stk' => Some (pc', r_sync r ms, m, stk', false, ms)
  | _, _ => None
  end.

Definition Rsync (sr tr: reg) (ms: bool) : Prop :=
   (forall x, x <> msf /\ x <> callee -> sr ! x = tr ! x) /\ 
   (tr ! msf = N (if ms then 1 else 0)).

Variant match_cfgs (p: prog) : ideal_cfg -> spec_cfg -> Prop :=
| match_cfgs_intro pc r m stk ms pc' r' stk'
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync r r' ms)
  (STK: map_opt (pc_sync p) stk = Some stk') :
  match_cfgs p ((pc, r, m, stk), ms) ((pc', r', m, stk'), false, ms)
.

Definition steps_to_sync_point' (p: prog) (ic: ideal_cfg) (ds: dirs) : option nat :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  (* check pc is well-formed *)
  match p[[pc]] with
  | Some i => match i with
             | IBranch e l => match ds with
                             | DBranch b :: ds' => Some (if b then 3 else 2)
                             | _ => None
                             end
             | ICall e => match ds with
                         | DCall pc' :: ds' => Some 4
                         | _ => None
                         end
             | _ => Some 1
             end
  | _ => None
  end.

Definition get_reg_sc (sc: spec_cfg) : reg :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  r.

Definition get_reg_ic (ic: ideal_cfg) : reg :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  r.

Definition get_pc_sc (sc: spec_cfg) : cptr :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  pc.

Definition get_pc_ic (ic: ideal_cfg) : cptr :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  pc.

(* (* Termination *) *)

(* Inductive result : Type := *)
(* | R_Normal *)
(* | R_Fault *)
(* | R_UB. *)

(* (* target *) *)

(* Definition is_fault_tgt (tp:prog) (res_t: spec_cfg) : option bool := *)
(*   let '(c, ct, ms) := res_t in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   i <- tp[[pc]];; *)
(*   match i with *)
(*   | <{{ ctarget }}> => Some (if ct then false else true) *)
(*   | _ => Some (if ct then true else false) *)
(*   end. *)

(* Definition is_normal_termination_tgt (tp:prog) (res_t: spec_cfg) : option bool := *)
(*   let '(c, ct, ms) := res_t in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   i <- tp[[pc]];; *)
(*   match i with *)
(*   | <{{ ret }}> => Some (if seq.nilp sk then true else false) *)
(*   | _ => Some false *)
(*   end. *)

(* Definition is_stuck_tgt (tp: prog) (res_t: spec_cfg) : option bool := *)
(*   let '(c, ct, ms) := res_t in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   _ <- tp[[pc]];; *)
(*   match (is_fault_tgt tp res_t, is_normal_termination_tgt tp res_t) with *)
(*   | (Some false, Some false) => Some true *)
(*   | _ => Some false *)
(*   end. *)

(* Definition classify_res_tgt (tp: prog) (res_t: spec_cfg) : result := *)
(*   if (is_fault_tgt tp res_t) then R_Fault else *)
(*   if (is_normal_termination_tgt tp res_t) then R_Normal else R_UB. *)

(* (* source *) *)

(* Definition is_fault_src (p: prog) (res_s: ideal_cfg) : option bool := *)
(*   let '(c, ms) := res_s in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   i <- p[[pc]];; *)
(*   Some true. *)

(* (* Normal termination: ret + empty stack *) *)
(* Definition is_normal_termination_src (p: prog) (res_s: ideal_cfg) : option bool := *)
(*   let '(c, ms) := res_s in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   i <- p[[pc]];; *)
(*   match i with *)
(*   | <{{ ret }}> => Some (if seq.nilp sk then true else false) *)
(*   | _ => Some false *)
(*   end. *)

(* (* any other final state means the program got stuck because of UB *) *)
(* Definition is_stuck_src (p: prog) (res_s: ideal_cfg) : option bool := *)
(*   let '(c, ms) := res_s in *)
(*   let '(pc, rs, m, sk) := c in *)
(*   _ <- p[[pc]];; *)
(*   match (is_fault_src p res_s, is_normal_termination_src p res_s) with *)
(*   | (Some false, Some false) => Some true *)
(*   | _ => Some false *)
(*   end. *)

(* Definition classify_term_src (p: prog) (res_s: ideal_cfg) : result := *)
(*   if (is_fault_src p res_s) then R_Fault else *)
(*   if (is_normal_termination_src p res_s) then R_Normal else R_UB. *)

(* Definition same_result_type (p tp: prog) (sc: spec_cfg) (ic: ideal_cfg) : bool := *)
(*   let '(c, ct, ms) := sc in *)
(*   let '(pc, r, m, sk) := c in *)
(*   let '(c', ms') := ic in *)
(*   let '(pc', r', m', sk') := c' in *)
(*   match (tp[[pc]], p[[pc']]) with *)
(*   | (Some i, Some i') => *)
(*       let ub_t := is_stuck_tgt tp sc in *)
(*       let ub_s := is_stuck_src p ic in *)
(*       let normal_t := is_normal_termination_tgt tp sc in *)
(*       let normal_s := is_normal_termination_src p ic in *)
(*       let fault_t := is_fault_tgt tp sc in *)
(*       let fault_s := is_fault_src p ic in *)
(*       let ub_match := *)
(*         match (ub_t, ub_s) with *)
(*         | (Some b1, Some b2) => b1 && b2 *)
(*         | _ => false *)
(*         end in *)
(*       let normal_match := *)
(*         match (normal_t, normal_s) with *)
(*         | (Some b1', Some b2') => b1' && b2' *)
(*         | _ => false *)
(*         end in *)
(*       let fault_match := *)
(*         match (fault_t, fault_s) with *)
(*         | (Some b1'', Some b2'') => b1'' && b2'' *)
(*         | _ => false *)
(*         end in *)
(*           ub_match || normal_match || fault_match *)
(*   | _ => false *)
(*    end. *)

(* Well-formedness properties *)

Definition wf_dir (p: prog) (pc: cptr) (d: direction) : Prop :=
  match d, p[[pc]] with
  | DBranch b, Some (IBranch e l) => is_some p[[(l, 0)]] = true (* YH: this should be checked in program's well-formness. *)
  | DCall pc', Some (ICall e) => is_some p[[pc']] = true
  | _, _ => False
  end.

Definition wf_ds (p: prog) (pc: cptr) (ds: dirs) : Prop :=
  Forall (wf_dir p pc) ds.

Definition wf_dir' (p: prog) (d: direction) : Prop :=
  match d with
  | DCall pc' => is_some p[[pc']] = true
  | _ => True
  end.

Definition wf_ds' (p: prog) (ds: dirs) : Prop :=
  Forall (wf_dir' p) ds.

Definition nonempty_block (blk : (list inst * bool)) : Prop :=
  0 < Datatypes.length (fst blk).

Definition is_terminator (i: inst) : Prop :=
  match i with
  | <{{ ret }}> | <{{ jump _}}> => True
  | _ => False
  end.

Definition last_inst_terminator (blk: (list inst * bool)) : Prop :=
  match (rev (fst blk)) with
  | [] => False (* unreachable *)
  | h::t => is_terminator h
  end.

(* we need a wf property saying that if we look up an expression in a register or  
   get it from memory, and it evaluates to a label, then that label is well-formed 
   (currently we only have this for constants that occur in expressions that occur 
   as the argument of the call instruction)
*)

Definition wf_lbl (p: prog) (is_proc: bool) (l: nat) : Prop :=
  match nth_error p l with
  | Some (_, b) => is_proc = b
  | None => False
  end.

Fixpoint wf_expr (p: prog) (e: exp) : Prop :=
  match e with
  | ANum _ | AId _ => True
  | ABin _ e1 e2  | <{_ ? e1 : e2}> => wf_expr p e1 /\ wf_expr p e2
  | <{&l}> => wf_lbl p true l
  end.

Definition wf_instr (p: prog) (i: inst) : Prop :=
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> => True
  | <{{_:=e}}> | ILoad _ e | <{{call e}}> => wf_expr p e
  | <{{store[e]<-e'}}> => wf_expr p e /\ wf_expr p e'
  | <{{branch e to l}}> => wf_expr p e /\ wf_lbl p false l
  | <{{jump l}}> => wf_lbl p false l
  end.

Definition wf_block (p: prog) (blk : (list inst * bool)) : Prop :=
   nonempty_block blk /\ last_inst_terminator blk /\ Forall (wf_instr p) (fst blk).

Definition nonempty_program (p: prog) : Prop :=
  0 < Datatypes.length p.

Definition wf_prog (p: prog) : Prop :=
  nonempty_program p /\ Forall (wf_block p) p.

From SECF Require Import sflib.

Definition wf_reg (p: prog) (r: reg) : Prop :=
  forall x l, r ! x = (FP l) -> nth_error p l <> None.

Definition wf_mem (p: prog) (m: mem) : Prop :=
  forall i l, nth_error m i = Some (FP l) -> nth_error p l <> None.

Definition wf_ic (p: prog) (ic: ideal_cfg) : Prop :=
  let '(pc, r, m, stk, ms) := ic in
  wf_reg p r /\ wf_mem p m.

(* Lemma wf_ic_preserved p ic ds os ict *)
(*     (WF: wf_ic p ic) *)
(*     (STEP: p |- <(( S_Running ic ))> -->i_ ds ^^ os  <(( S_Running ict ))>): *)
(*   wf_ic p ict. *)
(* Proof. *)

(* Aux Lemmas *)

Lemma wf_ds_app p ds1 ds2
    (WF: wf_ds' p (ds1 ++ ds2)) :
  wf_ds' p ds1 /\ wf_ds' p ds2.
Proof. eapply Forall_app. eauto. Qed.

Lemma multi_spec_splitting p sc ds os n sct m
    (LEN: n >= m)
    (STEPS: p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>) :
  exists scm ds1 ds2 os1 os2,
    p |- <(( sc ))> -->*_ ds1 ^^ os1 ^^ m <(( scm ))>
  /\ p |- <(( scm ))> -->*_ ds2 ^^ os2 ^^ (n - m) <(( sct ))>
  /\ ds = ds1 ++ ds2 /\ os = os1 ++ os2.
Proof.
  ginduction m; ii.
  - esplits; try econs. rewrite sub_0_r. auto.
  - destruct n as [|n]; try lia. inv STEPS.
    exploit IHm; try eapply H5; eauto; [lia|]. i. des.
    replace (S n - S m) with (n - m) by lia.
    esplits; eauto.
    { econs; eauto. }
    { subst. rewrite app_assoc. auto. }
    { subst. rewrite app_assoc. auto. }
Qed.

(* Lemma wf_uslh : forall (p: prog),    *)
(*   wf_prog p -> wf_prog (uslh_prog p). *)
(* Proof. *)

(* Lemma multi_spec_msf_lookup_preserved p sc1 ds os n sc1' *)
(* one more condition is needed : n steps of spec exec should be matched with single ideal steps *)
(*     (LK: msf_lookup_sc sc1 = N (if ms_true_sc sc1 then 1 else 0)) *)
(*     (STEPS: p |- <(( S_Running sc1 ))> -->*_ ds ^^ os ^^ n <(( S_Running sc1' ))>) : *)
(*   msf_lookup_sc sc1' = N (if ms_true_sc sc1' then 1 else 0). *)
(* Proof. *)

(* Tactics *)

(* using this *)
Lemma rev_fetch : forall (p: prog) (pc: cptr) (blk: list inst * bool) (i: inst),
  nth_error p (fst pc) = Some blk ->
  nth_error (fst blk) (snd pc) = Some i ->
  p[[pc]] = Some i.
Proof.
  intros. destruct pc as (l & o) eqn:Hpc.
  destruct (nth_error p (fst pc)) eqn:Hblk.
  - unfold fetch. ss. des_ifs.
  - rewrite Hpc in *. ss. des_ifs.
Qed.

(* using this *)
Lemma blk_not_empty_list : forall (blk: list inst * bool),
  nonempty_block blk -> (fst blk) <> [].
Proof.
  intros. unfold nonempty_block in H. unfold not; intros. rewrite H0 in H.
  simpl in H. apply nlt_0_r in H. destruct H.
Qed.

Lemma prog_not_empty_list (p: prog) : nonempty_program p -> p <> [].
Proof.
  intros. unfold nonempty_program in H. unfold not; intros. rewrite H0 in H.
  simpl in H. apply nlt_0_r in H. destruct H.
Qed.

Lemma cons_app : forall {A} (l: list A) (a: A),
  a :: l = [a] ++ l.
Proof.
  intros. destruct l; [rewrite app_nil_r|]; reflexivity.
Qed.

Lemma rev_cons : forall {A} (l: list A) (a: A),
  rev (a :: l) = rev l ++ [a].
Proof.
  intros. simpl. reflexivity.
Qed.

(* equivalence of Utils rev and Lists rev *)


Lemma utils_rev_append_and_rev : forall {X : Type} (l1 l2 : list X),
  Utils.rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X. induction l1 as [|h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite <- IHl1. apply functional_extensionality in IHl1.
    rewrite IHl1. intros l2. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma revs : forall {A}, @Utils.rev A = @rev A.
Proof.
  intros. apply functional_extensionality. intros.
  rename x into l. induction l as [|h t IHl]; auto.
  unfold Utils.rev in *. simpl. rewrite <- IHl.
  rewrite utils_rev_append_and_rev. rewrite IHl. reflexivity.
Qed.

Lemma p_le_tp : forall (p: prog),
  Datatypes.length p <= Datatypes.length (uslh_prog p).
Proof.
  intros. unfold uslh_prog.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn: Huslh.
  enough (Datatypes.length p' = Datatypes.length p).
  { rewrite length_app. lia. }
  eapply mapM_perserve_len in Huslh.
  rewrite <- Huslh. clear.
  ginduction p; ss.
  rewrite length_combine.
  rewrite length_seq, min_id. auto.
Qed.

Lemma block_always_terminator p b o i
    (WFB: wf_block p b)
    (INST: nth_error (fst b) o = Some i)
    (NT: ~ is_terminator i) :
  exists i', nth_error (fst b) (add o 1) = Some i'.
Proof.
  destruct WFB. destruct H0.
  red in H0. des_ifs.
  destruct (le_dec o (Datatypes.length (fst b) - 1)).
  (* o <= Datatypes.length (fst b) - 1: this is the in-bounds case *)
  { assert (i <> i0).
    { unfold not; intros. unfold is_terminator in *.
      destruct i eqn:Hi; destruct i0 eqn:Hi0; clarify. }
  destruct (eq_dec o (Datatypes.length (fst b) - 1)).
    (* o = Datatypes.length (fst b) - 1: not possible bc i ≠ i0 and i0 is last element *)
    { assert (rev (i0 :: l) = rev l ++ [i0]). { simpl. auto. }
      assert (rev (rev (fst b)) = rev (i0 :: l)). { rewrite Heq. simpl. auto. }
      rewrite rev_involutive in H4. simpl in H4.
      assert (nth_error (fst b) o = Some i0).
      { rewrite H4, e. simpl. rewrite H4. simpl. rewrite nth_error_app.
        assert ((Datatypes.length (rev l ++ [i0]) - 1 <? Datatypes.length (rev l))%nat = false).
        { induction l as [|h t]; clarify. simpl in *.
          assert (add 1 (Datatypes.length (rev t ++ [h])) = Datatypes.length ((rev t ++ [h]) ++ [i0])).
          { repeat rewrite length_app. assert (Datatypes.length [i0] = 1). { auto. } rewrite H5. rewrite add_comm. auto. }
          rewrite <- H5. simpl. rewrite sub_0_r. apply ltb_irrefl.
        }
        rewrite H5.
        assert (forall (n: nat), ((add n 1) - 1) - n = 0). { lia. }
        specialize (H6 (Datatypes.length (rev l))).
        rewrite length_app. assert (Datatypes.length [i0] = 1). { simpl. auto. }
        rewrite H7.
        assert (((add 1 (Datatypes.length (rev l))) - 1) = Datatypes.length (rev l)). { simpl. rewrite sub_0_r. auto. }
        rewrite add_comm. rewrite H8. simpl.
        assert ( ((Datatypes.length (rev l)) - (Datatypes.length (rev l))) = 0 ). { lia. }
        rewrite H9. simpl. auto.
      }
      rewrite INST in H5. injection H5; intros. clarify.
    }
    (* this is the correct case, where o points to some non-last instruction in the block *)
    assert (rev (i0 :: l) = rev l ++ [i0]). { simpl. auto. }
    assert (rev (rev (fst b)) = rev (i0 :: l)). { rewrite Heq. simpl. auto. }
    rewrite rev_involutive in H4. simpl in H4. rewrite H4 in INST, l0, n. rewrite H4.
    assert (o <= Datatypes.length (rev l ++ [i0]) - 1
            -> o <> Datatypes.length (rev l ++ [i0]) - 1
            -> o < Datatypes.length (rev l ++ [i0]) - 1 ).
    { lia. }
    specialize (H5 l0 n); intros.
    assert ((add o 1) <= (Datatypes.length (rev l ++ [i0]) - 1)). { lia. }
    assert ((add o 1) < (Datatypes.length (rev l ++ [i0]))). { lia. }
    rewrite <- nth_error_Some in H7.
    destruct (nth_error (rev l ++ [i0]) (add o 1)); clarify. exists i1. auto.
  }
  (* o OOB *)
  exfalso. clear - n INST. eapply not_le in n.
  assert (nth_error (fst b) o <> None).
  { ii. clarify. }
  rewrite nth_error_Some in H. lia.
Qed.

Lemma block_always_terminator_prog p pc i
    (WF: wf_prog p)
    (INST: p[[pc]] = Some i)
    (NT: ~ is_terminator i) :
  exists i', p[[pc+1]] = Some i'.
Proof.
  inv WF. destruct pc as [l o]. ss. des_ifs_safe.
  exploit block_always_terminator; eauto.
  rewrite Forall_forall in H0. eapply H0.
  eapply nth_error_In; eauto.
Qed.

Import MonadNotation.
Open Scope monad_scope.

Definition simple_inst (i: inst) : Prop :=
  match i with
  | ISkip | IJump _ | ILoad _ _ | IStore _ _ | IAsgn _ _ | IRet => True
  | _ => False
  end.

Variant match_simple_inst_uslh : inst -> inst -> Prop :=
| uslh_skip :
  match_simple_inst_uslh ISkip ISkip
| uslh_jump l:
  match_simple_inst_uslh (IJump l) (IJump l)
| uslh_load x e e'
  (IDX: e' = <{{ (msf = 1) ? 0 : e }}>) :
  match_simple_inst_uslh (ILoad x e) (ILoad x e')
| uslh_store e e' e1
  (IDX: e' = <{{ (msf = 1) ? 0 : e }}>) :
  match_simple_inst_uslh (IStore e e1) (IStore e' e1)
| uslh_asgn x e:
  match_simple_inst_uslh (IAsgn x e) (IAsgn x e)
| uslh_ret :
  match_simple_inst_uslh IRet IRet
.

(* Move to other file *)
Definition _branch_in_block (blk: list inst) : nat :=
  fold_left (fun acc i => add acc (match i with
                                | IBranch _ _ => 1
                                | _ => 0
                                end)) blk 0.

Definition branch_in_block (bb: list inst * bool) : nat :=
  _branch_in_block (fst bb).

Definition branch_in_prog (p: prog) : nat :=
  fold_left (fun acc b => add acc (branch_in_block b)) p 0.

Definition branch_in_prog_before (p: prog) (l: nat) : nat :=
  branch_in_prog (firstn l p).

Definition _offset_branch_before (blk: list inst) (ofs: nat) : nat :=
  _branch_in_block (firstn ofs blk).

Definition offset_branch_before (blk: list inst * bool) (ofs: nat) : nat :=
  _offset_branch_before (fst blk) ofs.

(* pc: branch's pc *)
Definition match_branch_target (p: prog) (pc: nat * nat) : option nat :=
  let '(l, o) := pc in
  match nth_error p l with
  | Some blk => Some (Datatypes.length p + branch_in_prog_before p l + offset_branch_before blk o)
  | _ => None
  end.

Variant match_inst_uslh (p: prog) (pc: cptr) : inst -> inst -> Prop :=
| uslh_simple i i'
  (SIMPL: simple_inst i)
  (MATCH: match_simple_inst_uslh i i') :
  match_inst_uslh p pc i i'
| uslh_branch e e' l l' tpc
  (COND: e' = <{{ (msf = 1) ? 0 : e }}>)
  (LB: match_branch_target p pc = Some l')
  (IN: nth_error (uslh_prog p) l' =
         Some ([<{{ msf := (~ e') ? 1 : msf }}>; <{{ jump l }}>], false))
  (SYNC: pc_sync p pc = Some tpc)
  (NXT: (uslh_prog p)[[tpc + 1]] = Some <{{ msf := e' ? 1 : msf }}>) :
  match_inst_uslh p pc (IBranch e l) (IBranch e' l')
| uslh_call e e' tpc
  (CALL: e' = <{{ (msf = 1) ? & 0 : e }}>)
  (SYNC: pc_sync p pc = Some tpc)
  (IN: (uslh_prog p)[[ tpc + 1 ]] = Some (ICall e')) :
  match_inst_uslh p pc (ICall e) (IAsgn callee e')
.

Lemma uslh_inst_simple i c iss np
    (SIMP: simple_inst i)
    (USLH: uslh_inst i c = (iss, np)) :
  exists i', iss = [i'] /\ match_simple_inst_uslh i i' /\ np = [].
Proof.
  ii. unfold uslh_inst in USLH. ss.
  des_ifs; ss; unfold MiniCET.uslh_ret in *;  clarify; esplits; econs; eauto.
Qed.

(* Move to other file *)
Lemma mapM_nth_error {A B} (f: A -> M B) l c l' np o blk
    (MM: mapM f l c = (l', np))
    (SRC: nth_error l o = Some blk) :
  exists blk' c' np', nth_error l' o = Some blk' /\ f blk c' = (blk', np').
Proof.
  ginduction l; ss; ii.
  { rewrite nth_error_nil in SRC. clarify. }
  rewrite unfold_mapM in MM.
  destruct o as [|o].
  { ss; clarify. unfold uslh_bind in MM.
    destruct (f blk c) eqn:F.
    destruct (mapM f l (c + Datatypes.length p)) eqn:MF.
    ss. clarify. esplits; eauto. }
  ss. unfold uslh_bind in MM. 
  destruct (f a c) eqn:F.
  destruct (mapM f l (c + Datatypes.length p)) eqn:MF. ss. clarify.
  exploit IHl; eauto.
Qed.

Definition len_before {A B} (f: A -> M B) (l: list A) (o c: nat) : nat :=
  let '(_, np) := mapM f (firstn o l) c in
  Datatypes.length np.

Lemma mapM_nth_error_strong {A B} (f: A -> M B) l c l' np o blk
    (MM: mapM f l c = (l', np))
    (SRC: nth_error l o = Some blk) :
  exists blk' c' np',
    nth_error l' o = Some blk'
 /\ f blk c' = (blk', np')
 /\ c' = c + len_before f l o c.
Proof.
  ginduction l; ss; ii.
  { rewrite nth_error_nil in SRC. clarify. }
  rewrite unfold_mapM in MM.
  destruct o as [|o].
  { ss; clarify. unfold uslh_bind in MM.
    destruct (f blk c) eqn:F.
    destruct (mapM f l (c + Datatypes.length p)) eqn:MF.
    ss. clarify. esplits; eauto.
    unfold len_before, mapM. des_ifs. ss.
    unfold MiniCET.uslh_ret in Heq. clarify. ss. lia. }
  ss. unfold uslh_bind in MM. 
  destruct (f a c) eqn:F.
  destruct (mapM f l (c + Datatypes.length p)) eqn:MF. ss. clarify.
  exploit IHl; eauto. i. des.
  esplits; eauto.
  unfold len_before. ss. des_ifs.
  rewrite unfold_mapM in Heq. eapply bind_inv in Heq. des. subst.
  eapply bind_inv in Heq0. des. subst.
  unfold len_before. rewrite Heq in F. clarify. rewrite Heq0.
  ss. unfold MiniCET.uslh_ret in Heq1. clarify.
  do 2 rewrite length_app. ss. lia.
Qed.

Definition blk_offset (blk: list inst * bool) (o: nat) :=
  fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o (fst blk))
    (if Bool.eqb (snd blk) true then 2 else 0).

Definition prefix_offset {A} (ll: list (list A)) (i: nat) (base: nat) :=
  fold_left (fun acc l => acc + (Datatypes.length l)) (firstn i ll) base.

Definition fold_left_add_init {A} (f: A -> nat) (l: list A) (n k: nat) :
  fold_left (fun acc x => acc + f x) l (n + k) = (fold_left (fun acc x => acc + f x) l n) + k.
Proof.
  ginduction l; ss; ii.
  replace (n + k + f a) with ((n + f a) + k) by lia. eauto.
Qed.

Definition fold_left_init_0 {A} (f: A -> nat) (l: list A) (n: nat) :
  fold_left (fun acc x => acc + f x) l n = (fold_left (fun acc x => acc + f x) l 0) + n.
Proof.
  replace n with (0 + n) by lia.
  rewrite fold_left_add_init. lia.
Qed.

Lemma concat_nth_error {A} (ll: list (list A)) l i j ii
    (LL: nth_error ll i = Some l)
    (L: nth_error l j = Some ii) :
  nth_error (List.concat ll) ((prefix_offset ll i 0) + j)%nat = Some ii.
Proof.
  ginduction ll; ss; ii.
  { rewrite nth_error_nil in LL. clarify. }
  destruct i; ss.
  { clarify. rewrite nth_error_app1; auto.
    rewrite <- nth_error_Some. ii; clarify. }

  exploit IHll; eauto. i.
  replace (prefix_offset (a :: ll) (S i) 0) with ((Datatypes.length a) + (prefix_offset ll i 0)).
  2:{ unfold prefix_offset. ss. rewrite add_comm. rewrite <- fold_left_add_init.
      rewrite add_0_l. auto. }
  rewrite nth_error_app2.
  2:{ lia. }
  replace (Datatypes.length a + prefix_offset ll i 0 + j - Datatypes.length a) with
    (prefix_offset ll i 0 + j) by lia.
  auto.
Qed.

Lemma offset_eq_aux blk c' l0 p1 n o
    (BLK: mapM uslh_inst blk c' = (l0, p1))
    (BDD: o <= Datatypes.length blk) :
  prefix_offset l0 o n =
  o + fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk) n.
Proof.
  ginduction o; ii.
  { ss. }
  unfold prefix_offset.

  exploit mapM_perserve_len; eauto. intros LEN.
  destruct blk.
  { ss. des_ifs. lia. }
  destruct l0.
  { ss. }
  do 2 rewrite firstn_cons.
  rewrite unfold_mapM in BLK.
  exploit bind_inv; eauto. i. des. subst. ss.
  unfold uslh_bind in x1.
  destruct (mapM uslh_inst blk (c' + Datatypes.length pm)) eqn:X. ss. clarify.
  exploit IHo.
  { eauto. }
  { lia. }
  i. rewrite <- x1.

  unfold prefix_offset.
  replace (n + Datatypes.length l) with
    (add (if is_br_or_call i then add n 1 else n) 1); auto.
  2:{ destruct i; ss; unfold MiniCET.uslh_ret in *; ss; clarify; ss.
      - unfold uslh_bind in x0. ss. clarify. ss. lia.
      - lia. }
  rewrite fold_left_add_init. lia.
Qed.

Lemma length_add_index {A} (p: list A) :
  Datatypes.length (add_index p) = Datatypes.length p.
Proof.
  unfold add_index.
  rewrite length_combine, length_seq, min_id. auto.
Qed.

Lemma nth_error_add_index {A} (p: list A) l i
    (NTH: nth_error p l = Some i) :
  nth_error (add_index p) l = Some (l, i).
Proof.
  erewrite nth_error_nth'.
  2:{ rewrite length_add_index. rewrite <- nth_error_Some. ii. clarify. }
  instantiate (1:=(l, i)).
  f_equal. unfold add_index.
  rewrite combine_nth.
  2:{ eapply length_seq. }
  rewrite seq_nth.
  2:{ rewrite <- nth_error_Some. ii. clarify. }
  ss. f_equal. eapply nth_error_nth. auto.
Qed.

Lemma src_skip_inv p tp pc tpc
    (TRP: uslh_prog p = tp)
    (PS: pc_sync p pc = Some tpc)
    (INST: p[[pc]] = Some <{{ skip }}>) :
  tp[[tpc]] = Some <{{ skip }}>.
Proof.
  destruct pc as [l o].
  destruct tpc as [l' o'].
  assert (l' = l).
  { clear -PS. unfold pc_sync in *. des_ifs. }
  subst. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.
  unfold uslh_prog.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn:Huslh.
  exploit mapM_perserve_len; eauto. intros LEN.
  replace (nth_error (p' ++ newp) l) with (nth_error p' l); cycle 1.
  { symmetry. eapply nth_error_app1. rewrite <- LEN.
    unfold add_index. rewrite length_combine, length_seq, min_id.
    erewrite <- nth_error_Some. ii. clarify. }
  exploit mapM_nth_error; eauto.
  { instantiate (2:= l). instantiate (1:= (l, (blk, is_proc))).
    eapply nth_error_add_index. auto. }
  i. des. rewrite x0. destruct blk' as [blk' is_proc'].
  simpl.
  ss. unfold uslh_bind in x1. ss.
  destruct (concatM (mapM uslh_inst blk) c') eqn:X.
  unfold pc_sync in *. ss. des_ifs_safe.
  replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.

  unfold concatM in X. exploit bind_inv; eauto. i. des; subst.
  exploit mapM_nth_error; try eapply x1; eauto. i. des.
  ss. unfold MiniCET.uslh_ret in *. ss. clarify.

  replace (o + blk_offset (blk, is_proc) o) with (prefix_offset a o 0 + (if Bool.eqb is_proc true then 2 else 0)); auto.
  2:{ destruct is_proc; ss.
      - unfold blk_offset. ss. unfold prefix_offset.
        erewrite <- fold_left_add_init. rewrite add_0_l.
        eapply offset_eq_aux; eauto.
        exploit mapM_perserve_len; eauto. i. rewrite x2.
        eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify.
      - rewrite add_0_r.
        unfold blk_offset. ss. eapply offset_eq_aux; eauto.
        exploit mapM_perserve_len; eauto. i. rewrite x2.
        eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
  des_ifs.
  - rewrite add_comm.
    replace (2 + prefix_offset a o 0) with (S (S (prefix_offset a o 0))) by lia.
    do 2 rewrite nth_error_cons_succ.
    replace (prefix_offset a o 0) with (prefix_offset a o 0 + 0) by lia.
    exploit concat_nth_error; eauto. ss.
  - exploit concat_nth_error; eauto. ss.
Qed.

Lemma src_simple_inv p tp pc tpc i
    (SIMP: simple_inst i)
    (TRP: uslh_prog p = tp)
    (PS: pc_sync p pc = Some tpc)
    (INST: p[[pc]] = Some <{{ i }}>) :
  exists i', tp[[tpc]] = Some <{{ i' }}> /\ match_simple_inst_uslh i i'.
Proof.
  destruct pc as [l o].
  destruct tpc as [l' o'].
  assert (l' = l).
  { clear -PS. unfold pc_sync in *. des_ifs. }
  subst. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.
  unfold uslh_prog.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn:Huslh.
  exploit mapM_perserve_len; eauto. intros LEN.
  replace (nth_error (p' ++ newp) l) with (nth_error p' l); cycle 1.
  { symmetry. eapply nth_error_app1. rewrite <- LEN.
    unfold add_index. rewrite length_combine, length_seq, min_id.
    erewrite <- nth_error_Some. ii. clarify. }
  exploit mapM_nth_error; eauto.
  { instantiate (2:= l). instantiate (1:= (l, (blk, is_proc))).
    eapply nth_error_add_index. auto. }
  i. des. rewrite x0. destruct blk' as [blk' is_proc'].
  simpl.
  ss. unfold uslh_bind in x1. ss.
  destruct (concatM (mapM uslh_inst blk) c') eqn:X.
  unfold pc_sync in *. ss. des_ifs_safe.
  replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.

  unfold concatM in X. exploit bind_inv; eauto. i. des; subst.
  exploit mapM_nth_error; try eapply x1; eauto. i. des.
  ss. unfold MiniCET.uslh_ret in *. ss. clarify.

  replace (o + blk_offset (blk, is_proc) o) with (prefix_offset a o 0 + (if Bool.eqb is_proc true then 2 else 0)); auto.
  2:{ destruct is_proc; ss.
      - unfold blk_offset. ss. unfold prefix_offset.
        erewrite <- fold_left_add_init. rewrite add_0_l.
        eapply offset_eq_aux; eauto.
        exploit mapM_perserve_len; eauto. i. rewrite x2.
        eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify.
      - rewrite add_0_r.
        unfold blk_offset. ss. eapply offset_eq_aux; eauto.
        exploit mapM_perserve_len; eauto. i. rewrite x2.
        eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
  des_ifs.
  - rewrite add_comm.
    replace (2 + prefix_offset a o 0) with (S (S (prefix_offset a o 0))) by lia.
    do 2 rewrite nth_error_cons_succ.
    replace (prefix_offset a o 0) with (prefix_offset a o 0 + 0) by lia.
    destruct i0; ss; unfold MiniCET.uslh_ret in *; clarify.
    + exists ISkip; split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + exists (IAsgn x e); split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + exists (IJump l0); split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto.
      exploit concat_nth_error; ss; eauto. ss.
    + exists IRet; split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
  - destruct i0; ss; unfold MiniCET.uslh_ret in *; clarify.
    + exists ISkip; split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + exists (IAsgn x e); split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + exists (IJump l0); split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto.
      exploit concat_nth_error; ss; eauto. ss.
    + exists IRet; split; [|econs]. exploit concat_nth_error; ss; eauto. ss.
Qed.

(* Move to other file *)

Lemma uslh_inst_np_length_aux
    i c is' np
    (USLH: uslh_inst i c = (is', np)):
  Datatypes.length np = match i with
                        | <{{ branch _ to _ }}> => 1
                        | _ => 0
                        end.
Proof.
  destruct i; ss; unfold MiniCET.uslh_ret in *; clarify.
  eapply bind_inv in USLH. des. subst.
  unfold add_block_M, add_block in USLH. ss. clarify.
Qed.
Lemma uslh_blk_np_length_aux1
    blk n blk' np
    (USLH: mapM uslh_inst blk n = (blk', np)):
  Datatypes.length np = _branch_in_block blk.
Proof.
  ginduction blk; ss; ii.
  { unfold mapM in *. ss. unfold MiniCET.uslh_ret in *; ss. clarify. }
  exploit mapM_cons_inv; eauto. i. des. subst.
  exploit IHblk; eauto. i. rewrite length_app.
  rewrite x2. unfold _branch_in_block at 2. ss.
  rewrite fold_left_init_0.
  clear -x0. eapply uslh_inst_np_length_aux in x0.
  rewrite x0. unfold _branch_in_block. lia.
Qed.

Lemma uslh_blk_np_length_aux2
    n blk c res_hd np_hd
    (USLH: uslh_blk (n, blk) c = (res_hd, np_hd)):
  branch_in_block blk = Datatypes.length np_hd.
Proof.
  destruct blk. unfold uslh_blk in USLH.
  eapply bind_inv in USLH. des. subst.
  unfold branch_in_block. ss.
  assert (concatM (mapM uslh_inst l) c = (a, pm) ->
          Datatypes.length pm = _branch_in_block l).
  { clear. ii. unfold concatM in *. eapply bind_inv in H. des.
    ss. unfold MiniCET.uslh_ret in H0. clarify.
    rewrite app_nil_r. eapply uslh_blk_np_length_aux1; eauto. }
  rewrite app_length. rewrite <- H; eauto.
  des_ifs; unfold MiniCET.uslh_ret in *; clarify; ss; lia.
Qed.

Lemma mapM_nil {A B} (f: A -> M B) (l:list A) c l' np
  (NIL: l = [])
  (MM: mapM f l c = (l', np)) :
  l' = [] /\ np = [].
Proof.
  subst. unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
Qed.

Lemma uslh_blk_np_length_aux p c p' np
    (USLH: mapM uslh_blk (add_index p) c = (p', np)) :
  branch_in_prog p = Datatypes.length np.
Proof.
  unfold add_index in *. remember 0. clear Heqn.
  ginduction p; ss; ii.
  - eapply mapM_nil in USLH; eauto. des; subst; ss.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    unfold branch_in_prog. simpl. rewrite fold_left_init_0.
    rewrite app_length.
    eapply uslh_blk_np_length_aux2 in x0.
    rewrite x0, <- x2. unfold branch_in_prog. lia.
Qed.

Lemma firstn_add_index_comm {A} (p: list A) n:
  firstn n (add_index p) = add_index (firstn n p).
Proof.
  unfold add_index. remember 0. clear Heqn0.
  ginduction p; ss; ii.
  { destruct n; ss. }
  destruct n; [ss|].
  do 2 rewrite firstn_cons. erewrite IHp. ss.
Qed.

Lemma uslh_blk_np_length p l:
  branch_in_prog_before p l = len_before uslh_blk (add_index p) l (Datatypes.length p).
Proof.
  unfold branch_in_prog_before, len_before.
  des_ifs. rewrite firstn_add_index_comm in Heq.
  eapply uslh_blk_np_length_aux in Heq. auto.
Qed.

Lemma uslh_inst_np_length blk is_proc o c :
  offset_branch_before (blk, is_proc) o = len_before uslh_inst blk o c.
Proof.
  unfold offset_branch_before. ss.
  ginduction blk; ss; ii.
  { unfold _offset_branch_before, len_before. destruct o; ss. }
  destruct o; ss.
  unfold _offset_branch_before, len_before. ss. des_ifs.
  eapply mapM_cons_inv in Heq. des. subst.
  exploit IHblk; eauto. unfold _offset_branch_before.
  instantiate (2:=o). instantiate (1:= (c + Datatypes.length np_hd)).
  unfold len_before. des_ifs. i.
  unfold _branch_in_block. ss. rewrite fold_left_init_0.
  rewrite length_app. unfold _branch_in_block in x0.
  rewrite x0. clear - Heq.
  eapply uslh_inst_np_length_aux in Heq. rewrite Heq. lia.
Qed.

Lemma src_inv_branch_blk
    blk o e l c blk' np
    (INST: nth_error blk o = Some <{{ branch e to l }}>)
    (USLH: mapM uslh_inst blk c = (blk', np)) :
  nth_error np (_offset_branch_before blk o) =
    Some ([<{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>; <{{ jump l }}>], false).
Proof.
  ginduction blk; ii.
  { rewrite nth_error_nil in INST. clarify. }
  destruct o; ss; clarify.
  - eapply mapM_cons_inv in USLH. des. subst.
    ss. eapply bind_inv in USLH. des. subst.
    unfold add_block_M, add_block in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    unfold _offset_branch_before. rewrite firstn_cons.
    unfold _branch_in_block. ss. rewrite fold_left_init_0.
    rewrite add_comm. exploit uslh_inst_np_length_aux; eauto. i.
    rewrite nth_error_app2; try lia.
    rewrite add_comm, x2, add_sub. eapply IHblk; eauto.
Qed.

Lemma src_inv_branch_prog p tp pc tpc e l e' l'
    (TRP: uslh_prog p = tp)
    (PS: pc_sync p pc = Some tpc)
    (INST: p[[pc]] = Some <{{ branch e to l }}>)
    (NTH: match_branch_target p pc = Some l')
    (COND: e' = <{{ (msf = 1) ? 0 : e }}>) :
  nth_error tp l' = Some ([<{{ msf := (~ e') ? 1 : msf }}>; <{{ jump l }}>], false).
Proof.
  destruct pc as [b o]. ss. des_ifs.
  destruct p0 as [blk is_proc]. ss.
  unfold uslh_prog. des_ifs.

  assert(LENP: Datatypes.length p = Datatypes.length l0).
  { eapply mapM_perserve_len in Heq0. rewrite <- Heq0. symmetry. eapply length_add_index. }

  rewrite LENP.
  rewrite nth_error_app. des_ifs.
  { rewrite ltb_lt in Heq1. lia. }
  rewrite <- add_assoc, add_comm. rewrite add_sub.

  exploit nth_error_add_index; try eapply Heq. i.
  exploit firstn_skipn_middle; eauto. i.
  rewrite <- x1 in Heq0.
  exploit mapM_app_inv; eauto. i. des; subst.
  exploit mapM_cons_inv; eauto. i. des; subst.

  rewrite firstn_add_index_comm in x2.
  exploit uslh_blk_np_length_aux; try eapply x2. i.
  unfold branch_in_prog_before. rewrite x6.

  rewrite nth_error_app2; try lia. rewrite add_comm, add_sub.
  rewrite nth_error_app1.
  2:{ erewrite uslh_inst_np_length.
      instantiate (1:=(Datatypes.length p + Datatypes.length np1)).
      erewrite <- uslh_inst_np_length. instantiate (1:= is_proc).
      eapply uslh_blk_np_length_aux2 in x4. rewrite <- x4.
      unfold offset_branch_before, branch_in_block. simpl.
      clear - INST. ginduction blk; ss; ii.
      - rewrite nth_error_nil in INST. clarify.
      - destruct o; ss; clarify.
        + unfold _offset_branch_before, _branch_in_block. ss.
          rewrite fold_left_init_0. lia.
        + unfold _branch_in_block. ss. rewrite fold_left_init_0.
          unfold _offset_branch_before, _branch_in_block. ss.
          rewrite fold_left_init_0. exploit IHblk; eauto. i.
          unfold _offset_branch_before, _branch_in_block in x0. lia. }
  unfold uslh_blk in x4. exploit bind_inv; try eapply x4. i. des; subst.
  assert (pf = []).
  { des_ifs; ss; unfold MiniCET.uslh_ret in *; clarify. }
  subst. rewrite app_nil_r.

  eapply bind_inv in x7. des. subst.
  assert (pf = []).
  { ss; unfold MiniCET.uslh_ret in *; clarify. }
  subst. rewrite app_nil_r. eapply src_inv_branch_blk; eauto.
Qed.

Lemma no_ct_prog_src p pc
    (NCT: no_ct_prog p)
    (INST: p[[pc]] = Some <{{ ctarget }}>) :
  False.
Proof.
  unfold no_ct_prog in NCT.
  destruct (split p) as (bs & bools) eqn:Hsplitp.
  rewrite Forall_forall in NCT. destruct pc; ss. des_ifs.
  exploit nth_error_In; try eapply Heq. i.
  eapply in_split_l in x0. rewrite Hsplitp in x0. ss.
  apply NCT in x0. unfold no_ct_blk in x0. rewrite Forall_forall in x0.
  exploit nth_error_In; eauto. i. eapply x0 in x1. ss.
Qed.

Lemma src_inv p tp pc tpc i
    (NCT: no_ct_prog p)
    (TRP: uslh_prog p = tp)
    (PS: pc_sync p pc = Some tpc)
    (INST: p[[pc]] = Some <{{ i }}>) :
  exists i', tp[[tpc]] = Some <{{ i' }}> /\ match_inst_uslh p pc i i'.
Proof.
  assert (SDEC: simple_inst i \/ ~ (simple_inst i)).
  { destruct i; ss; auto. }
  destruct SDEC as [SIMP | SIMP].
  { exploit src_simple_inv; eauto. i. des. esplits; eauto.
    econs; eauto. }

  unfold uslh_prog in TRP.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn:Huslh.
  exploit mapM_perserve_len; eauto. intros LEN.

  (* destruct pc_sync *)
  destruct pc as [l o]. dup PS.
  unfold pc_sync in PS. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.
  replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.

  (* find corresponding target block *)
  exploit mapM_nth_error_strong; eauto.
  { instantiate (2:= l). instantiate (1:= (l, (blk, is_proc))).
    eapply nth_error_add_index. auto. }
  i. des.

  rewrite nth_error_app1.
  2:{ rewrite <- nth_error_Some. ii. clarify. }
  rewrite x0. ss. unfold uslh_bind in x1. ss.
  destruct (concatM (mapM uslh_inst blk) c') eqn: CONCAT.
  unfold concatM in CONCAT. ss. exploit bind_inv; eauto. i. des; subst.
  exploit mapM_nth_error_strong; try eapply x3; eauto. i. des.
  unfold MiniCET.uslh_ret in x4. clarify.

  destruct i; ss.
  (* branch *)
  - unfold uslh_bind in x5. ss. clarify.
    remember (Datatypes.length p + len_before uslh_blk (add_index p) l (Datatypes.length p) +
                len_before uslh_inst blk o (Datatypes.length p + len_before uslh_blk (add_index p) l (Datatypes.length p))) as c'.
    exists <{{ branch (msf = 1) ? 0 : e to c' }}>.
    split.
    + destruct blk' as [blk' is_proc']. ss.
      exploit concat_nth_error; i.
      { eapply x2. }
      { instantiate (2:= 0). ss. }
      des_ifs.
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 + 2 = o + blk_offset (blk, true) o).
        { unfold blk_offset. ss. unfold prefix_offset.
          rewrite <- fold_left_add_init. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. rewrite add_comm.
        replace (2 + prefix_offset a o 0) with (S (S (prefix_offset a o 0))) by lia.
        rewrite add_0_r in x4. auto. }
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 + 0 = o + blk_offset (blk, false) o).
        { rewrite add_0_r.
          unfold blk_offset. ss. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. auto. }
    + econs 2; ss.
      2:{ eapply src_inv_branch_prog; eauto; cycle 1.
          { ss. rewrite Heq. subst. f_equal.
            erewrite <- uslh_blk_np_length, <- uslh_inst_np_length; eauto. }
          ss. des_ifs. }
      * des_ifs_safe. f_equal.
        do 2 rewrite <- add_assoc. rewrite add_cancel_l.

        (* The number of branches in previous blocks and
         the number of new blocks created during `uslh_blk` are equal. *)
        assert (branch_in_prog_before p l = len_before uslh_blk (add_index p) l (Datatypes.length p)).
        { eapply uslh_blk_np_length. }
        i. rewrite <- H.

        (* The number of branches before the current offset and
         the number of blocks created when `uslh` is applied
         to the current block up to the current offset are equal. *)
        assert (offset_branch_before (blk, is_proc) o =
                  len_before uslh_inst blk o (Datatypes.length p + branch_in_prog_before p l)).
        { eapply uslh_inst_np_length. }
        lia.
      * eauto.
      (* TODO: lemma? #2 *)
      * ss. unfold uslh_prog. rewrite Huslh.
        rewrite nth_error_app1.
        2:{ rewrite <- nth_error_Some. ii. clarify. }
        rewrite x0.
        replace (fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then add acc 1 else acc) (firstn o blk)
                   (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.

        destruct blk' as [blk' is_proc']. ss.
        exploit concat_nth_error; i.
        { eapply x2. }
        { instantiate (2:= 1). ss. }
        des_ifs.
        { unfold MiniCET.uslh_ret in Heq1. clarify.
          assert (prefix_offset a o 0 + 2 = o + blk_offset (blk, true) o).
          { unfold blk_offset. ss. unfold prefix_offset.
            rewrite <- fold_left_add_init. eapply offset_eq_aux; eauto.
            exploit mapM_perserve_len; eauto. i. rewrite x1.
            eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
          rewrite <- H. rewrite <- add_assoc. rewrite add_comm.
          replace ((add 2 1) + prefix_offset a o 0)%nat with (S (S (add (prefix_offset a o 0) 1))) by lia.
          do 2 rewrite nth_error_cons_succ. auto. }
        { unfold MiniCET.uslh_ret in Heq1. clarify.
          assert (prefix_offset a o 0 = o + blk_offset (blk, false) o).
          { unfold blk_offset. ss. eapply offset_eq_aux; eauto.
            exploit mapM_perserve_len; eauto. i. rewrite x1.
            eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
          rewrite <- H. auto. }
  (* call *)
  (* TODO: existential case also could be a lemma *)
  - unfold MiniCET.uslh_ret in x5. clarify.
    exists <{{ callee := (msf = 1) ? & 0 : fp }}>.
    split.
    + destruct blk' as [blk' is_proc']. ss.
      exploit concat_nth_error; i.
      { eapply x2. }
      { instantiate (2:= 0). ss. }
      des_ifs.
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 + 2 = o + blk_offset (blk, true) o).
        { unfold blk_offset. ss. unfold prefix_offset.
          rewrite <- fold_left_add_init. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. rewrite add_comm.
        replace (2 + prefix_offset a o 0) with (S (S (prefix_offset a o 0))) by lia.
        rewrite add_0_r in x4. auto. }
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 + 0 = o + blk_offset (blk, false) o).
        { rewrite add_0_r.
          unfold blk_offset. ss. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. auto. }
    (* TODO: lemma? #2 *)
    + econs 3; eauto. ss. unfold uslh_prog. rewrite Huslh.
      rewrite nth_error_app1.
      2:{ rewrite <- nth_error_Some. ii. clarify. }
      rewrite x0.
      replace (fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.

      destruct blk' as [blk' is_proc']. ss.
      exploit concat_nth_error; i.
      { eapply x2. }
      { instantiate (2:= 1). ss. }
      des_ifs.
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 + 2 = o + blk_offset (blk, true) o).
        { unfold blk_offset. ss. unfold prefix_offset.
          rewrite <- fold_left_add_init. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. rewrite <- add_assoc. rewrite add_comm.
        replace ((add 2 1) + prefix_offset a o 0)%nat with (S (S (add (prefix_offset a o 0) 1))) by lia.
        do 2 rewrite nth_error_cons_succ. auto. }
      { unfold MiniCET.uslh_ret in Heq1. clarify.
        assert (prefix_offset a o 0 = o + blk_offset (blk, false) o).
        { unfold blk_offset. ss. eapply offset_eq_aux; eauto.
          exploit mapM_perserve_len; eauto. i. rewrite x1.
          eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. }
        rewrite <- H. auto. }
  (* ctarget *)
  - exists <{{ ctarget }}>. exfalso. eapply (no_ct_prog_src p (l, o)); eauto.
    ss. des_ifs.
Qed.

Lemma firstnth_error : forall (l: list inst) (n: nat) (i: inst),
  nth_error l n = Some i ->
  firstn (S n) l = firstn n l ++ [i].
Proof.
  induction l as [|h t IHl]; intros.
  - rewrite nth_error_nil in H; discriminate.
  - rewrite firstn_cons. replace (h :: t) with ([h] ++ t) by auto.
    replace (h :: firstn n t) with ([h] ++ (firstn n t)) by auto.
    rewrite firstn_app. simpl.
    rewrite nth_error_cons in H. destruct n as [|n']; clarify.
    specialize IHl with (n:=n') (i:=i). specialize (IHl H).
    rewrite IHl. simpl. rewrite firstn_nil. simpl. rewrite sub_0_r. auto.
Qed.

Lemma eval_regs_eq : forall (r r': reg) (e: exp),
   e_unused msf e ->
   e_unused callee e ->
   (forall x : string, x <> msf /\ x <> callee -> r x = r' x) ->
   eval r e = eval r' e.
Proof.
  intros. ginduction e; ss; ii.
  - simpl in H, H0.
    assert (x <> msf /\ x <> callee) by (split; auto).
    apply H1 in H2. simpl. eauto.
  - simpl in *. destruct H, H0. f_equal.
    { apply IHe1; clarify. }
    { apply IHe2; clarify. }
  - ss. destruct H, H0, H2, H3.
    exploit IHe1; eauto. exploit IHe2; eauto. exploit IHe3; eauto. i.
    rewrite x0, x1, x2. eauto.
Qed.

Lemma wf_prog_lookup p pc i
    (WF: wf_prog p)
    (INST: p [[pc]] = Some i) :
  wf_instr p i.
Proof.
  destruct pc; ss. des_ifs_safe. inv WF.
  rewrite Forall_forall in H0. eapply nth_error_In in Heq.
  eapply H0 in Heq. unfold wf_block in Heq. des.
  rewrite Forall_forall in Heq1. eapply nth_error_In in INST. eauto.
Qed.

Lemma unused_prog_lookup x p pc i
    (UNUSED: unused_prog x p)
    (INST: p [[pc]] = Some i) :
  i_unused x i.
Proof.
  unfold unused_prog in *. destruct pc; ss. des_ifs_safe.
  rewrite Forall_forall in UNUSED. eapply nth_error_In in Heq.
  exploit in_split_l; eauto. i. rewrite Heq0 in x1. ss.
  exploit UNUSED; eauto. i. unfold b_unused in x2.
  rewrite Forall_forall in x2. eapply nth_error_In in INST. eauto.
Qed.

Lemma no_ct_prog_cons b p
    (NCT: no_ct_prog (b::p)) :
  no_ct_blk (fst b) /\ no_ct_prog p.
Proof.
  destruct b. ss. unfold no_ct_prog in *. des_ifs.
  assert (l2 = l::l0 /\ l3 = b::l1).
  { clear -Heq0 Heq. ginduction p; ss; ii; clarify.
    des_ifs. }
  des; subst. inv NCT. eauto.
Qed.

Lemma no_ct_prog_In blk is_ct p
    (IN: In (blk, is_ct) p)
    (NCT: no_ct_prog p) :
  no_ct_blk blk.
Proof.
  ginduction p; ss; ii. eapply no_ct_prog_cons in NCT.
  des; subst; eauto.
Qed.

Lemma split_app
    {A B} (l1 l2: list (A * B))
    sl sl' sl1 sl1' sl2 sl2'
    (SP1: split (l1 ++ l2) = (sl, sl'))
    (SP2: split l1 = (sl1, sl1'))
    (SP3: split l2 = (sl2, sl2')) :
  sl = sl1 ++ sl2 /\ sl' = sl1' ++ sl2'.
Proof.
  ginduction l1; ii.
  { ss. clarify. rewrite SP1 in SP3. clarify. }
  destruct a as [a b]. ss. des_ifs_safe.
  exploit IHl1; eauto. i. des. subst; auto.
Qed.

Lemma no_ct_prog_app l1 l2:
  no_ct_prog (l1 ++ l2) <-> (no_ct_prog l1 /\ no_ct_prog l2).
Proof.
  unfold no_ct_prog. des_ifs.
  exploit split_app; try eapply Heq; eauto. i. des; subst.
  rewrite Forall_app. auto.
Qed.

Lemma new_prog_no_ct_blk blk n c res np
    (USLH: uslh_blk (n, blk) c = (res, np)):
  no_ct_prog np.
Proof.
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (no_ct_prog pm0).
  { clear -USLH. ginduction l; ss; ii.
    - unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
    - eapply mapM_cons_inv in USLH. des. subst.
      exploit IHl; eauto. i. destruct a; ss; unfold MiniCET.uslh_ret in *; clarify. ss.
      eapply bind_inv in USLH. des. ss. subst. clarify.
      unfold add_block_M, add_block in USLH.
      rewrite app_nil_r. rewrite no_ct_prog_app. split; auto. clarify.
      red. des_ifs. ss. clarify. econs; eauto. repeat econs. }
  rewrite app_nil_r. rewrite no_ct_prog_app. split; auto. des_ifs; ss.
Qed.

Lemma new_prog_no_ct p c p' np
    (USLH: mapM uslh_blk (add_index p) c = (p', np)):
  no_ct_prog np.
Proof.
  unfold add_index in USLH. remember 0. clear Heqn.
  ginduction p; ss; ii.
  - unfold mapM in *. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    assert (no_ct_prog np_hd).
    { eapply new_prog_no_ct_blk; eauto. }
    rewrite no_ct_prog_app. auto.
Qed.

Lemma new_prog_ct_cut p c p' np l o
    (USLH: mapM uslh_blk (add_index p) c = (p', np))
    (INST: (p' ++ np) [[(l, o)]] = Some <{{ ctarget }}>)
    (NCT: no_ct_prog np):
  p'[[(l, o)]] = Some <{{ ctarget }}>.
Proof.
  ss. des_ifs_safe.
  assert (l < Datatypes.length p' \/ Datatypes.length p' <= l) by lia.
  des.
  - rewrite nth_error_app1 in Heq; eauto. rewrite Heq; auto.
  - exfalso. rewrite nth_error_app2 in Heq; auto.
    eapply nth_error_In in Heq, INST. red in NCT. des_ifs.
    eapply in_split_l in Heq. rewrite Heq0 in Heq. ss.
    rewrite Forall_forall in NCT. eapply NCT in Heq. red in Heq.
    rewrite Forall_forall in Heq. eapply Heq in INST. ss.
Qed.

Lemma no_ctarget_exists_blk blk l c blk' np'
    (NCT: no_ct_blk blk)
    (USLH: uslh_blk (l, (blk, false)) c = (blk', np')) :
  no_ct_blk (fst blk') /\ snd blk' = false.
Proof.
  unfold uslh_blk in USLH. eapply bind_inv in USLH. des. subst.
  ss. unfold MiniCET.uslh_ret in USLH0. clarify. simpl. split; auto.
  unfold concatM in USLH. eapply bind_inv in USLH. des. ss.
  unfold MiniCET.uslh_ret in *. clarify.
  red. rewrite Forall_concat. ginduction blk; ii.
  - unfold mapM in USLH. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des; subst.
    inv NCT. eapply IHblk in H2; try eapply x1; eauto.
    econs; eauto. clear - x0 H1.
    destruct a; ss; unfold MiniCET.uslh_ret in *; clarify; repeat econs.
    eapply bind_inv in x0. des. clarify. repeat econs.
Qed.

Lemma no_ctarget_exists p l blk
    (NCT : no_ct_prog p)
    (LTH: nth_error p l = Some (blk, false)) :
  forall o, (uslh_prog p)[[(l, o)]] <> Some <{{ ctarget }}>.
Proof.
  unfold uslh_prog. des_ifs. ii.
  (* unfold uslh_prog, add_index in CT. des_ifs. *)
  assert (NCT0: no_ct_prog p0).
  { eapply new_prog_no_ct; eauto. }
  eapply new_prog_ct_cut in H; eauto.
  des. exploit mapM_nth_error_strong; eauto.
  { eapply nth_error_add_index; eauto. }
  i. des.
  assert (no_ct_blk (fst blk') /\ snd blk' = false).
  { eapply no_ctarget_exists_blk; eauto. eapply no_ct_prog_In in NCT; eauto.
    eapply nth_error_In; eauto. }
  des. ss. des_ifs. eapply nth_error_In in H.
  red in H0. rewrite Forall_forall in H0. eapply H0 in H. ss.
Qed.

Lemma head_call_target p pc
    (UNUSED: unused_prog callee p)
    (NCT: no_ct_prog p)
    (INST: (uslh_prog p)[[pc]] = Some <{{ ctarget }}>) :
  exists l blk, pc = (l, 0)
  /\ nth_error (uslh_prog p) l = Some (blk, true)
  /\ (uslh_prog p)[[pc+1]] = Some <{{ msf := (callee = (& (fst pc))) ? msf : 1 }}>.
Proof.
  destruct pc as [l o]. exists l.
  unfold uslh_prog in *. des_ifs_safe.
  assert (no_ct_prog p0).
  { eapply new_prog_no_ct; eauto. }
  assert (INST': l0[[(l, o)]] = Some <{{ ctarget }}>).
  { eapply new_prog_ct_cut; eauto. }
  clear INST.
  destruct (nth_error p l) eqn:LTH; cycle 1.
  { exfalso. exploit mapM_perserve_len; eauto. i.
    rewrite length_add_index in x0. ss. des_ifs_safe.
    rewrite nth_error_None, x0, <- nth_error_None in LTH. clarify. }
  destruct p1 as [blk is_proc].
  exploit nth_error_add_index; eauto. i.
  exploit mapM_nth_error_strong; eauto. i. des.
  destruct is_proc; cycle 1.
  { exfalso. hexploit no_ctarget_exists; try eapply NCT; eauto.
    instantiate (1:=o). ii. unfold uslh_prog in H0. des_ifs_safe.
    assert (nth_error (l0 ++ p0) l = Some blk').
    { erewrite nth_error_app1; eauto.
      rewrite <- nth_error_Some. ii; clarify. }
    ss. des_ifs. }
  unfold uslh_blk in x2.
  eapply bind_inv in x2. des. subst.
  assert (NCTS: no_ct_blk blk).
  { eapply nth_error_In in LTH. eapply no_ct_prog_In; eauto. }
  (* YH: TODO: make lemma *)
  assert (no_ct_blk a).
  { clear - x2 NCTS. unfold concatM in x2. eapply bind_inv in x2. des; subst.
    ss. unfold MiniCET.uslh_ret in x0. clarify.
    remember (Datatypes.length p + len_before uslh_blk (add_index p) l (Datatypes.length p)).
    clear Heqn. clear -x2 NCTS.
    ginduction blk; ss; ii.
    - unfold mapM in x2. ss. unfold MiniCET.uslh_ret in x2. clarify.
    - inv NCTS. eapply mapM_cons_inv in x2. des; subst.
      exploit IHblk; try eapply x0; eauto. i.
      unfold no_ct_blk in *. rewrite Forall_concat in *. econs; eauto.
      clear - H1 x2.
      destruct a; ss; unfold MiniCET.uslh_ret in *; clarify; try econs; ss.
      + eapply bind_inv in x2. des. clarify. econs; eauto.
      + econs; eauto. }
  ss. unfold MiniCET.uslh_ret in x4. clarify.
  exists (<{{ ctarget }}> :: <{{ msf := (callee = (& l)) ? msf : 1 }}> :: a).
  rewrite nth_error_app1.
  2:{ rewrite <- nth_error_Some. ii; clarify. }
  destruct (eq_decidable o 0); subst; auto; cycle 1.
  { des_ifs_safe. ss.
    clear - H0 H INST'. destruct o; ss. destruct o; ss.
    eapply nth_error_In in INST'. eapply Forall_forall in H0; eauto. ss. }
  des_ifs.
Qed.

Lemma ctarget_exists p l blk
  (LTH: nth_error p l = Some (blk, true)) :
  (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>.
Proof.
  unfold uslh_prog. des_ifs_safe.
  exploit mapM_nth_error_strong; eauto.
  { eapply nth_error_add_index; eauto. }
  i. des.
  eapply bind_inv in x1. des. clarify. subst.
  ss. erewrite nth_error_app1.
  2:{ rewrite <- nth_error_Some. ii. clarify. }
  rewrite x0. unfold MiniCET.uslh_ret in x3. clarify.
Qed.

(* Lemma src_tgt_length : forall p tp pc (bk bk': list inst * bool) e l (i: inst), *)
(*   nth_error p (fst pc) = Some bk -> *)
(*   nth_error (fst bk) (snd pc) = Some i -> *)
(*   i <> <{{ branch e to l }}> -> *)
(*   tp = uslh_prog p -> *)
(*   nth_error tp (fst pc) = Some bk'. *)
(* Proof. *)
(*   i. rewrite H2 in *. unfold uslh_prog.  *)
(*   destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as (p', newp) eqn:Htp. *)

Lemma ultimate_slh_bcc_single_cycle_refactor (p: prog) : forall ic1 sc1 sc2 n ds os,
  no_ct_prog p ->
  wf_prog p ->
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0) ->
  steps_to_sync_point' p ic1 ds = Some n ->
  match_cfgs p ic1 sc1 ->
  uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( S_Running sc2 ))> ->
      exists ic2, p |- <(( S_Running ic1 ))> -->i_ ds ^^ os <(( S_Running ic2 ))> 
                  /\ match_cfgs p ic2 sc2.
Proof.
  intros until os. intros nct wfp unused_p_msf unused_p_callee ms_msf n_steps cfg_sync tgt_steps.
  destruct ic1 as (c & ms). destruct c as (c & sk). destruct c as (c & m). destruct c as (ipc & r).
  (* assert (wftp: wf_prog (uslh_prog p)). { apply wf_uslh. assumption. } *)

  dup wfp. unfold wf_prog in wfp. destruct wfp. unfold nonempty_program in H.
  (* unfold wf_ds' in wfds. *)
  destruct ipc as (l & o).

  destruct (p[[(l, o)]]) eqn: ISRC; cycle 1.
  (* source instruction lookup failed: n_steps gives this. *)
  { ss. des_ifs. }
  inv cfg_sync. exploit src_inv; try eapply ISRC; eauto. i. des.
  destruct i.
  (* skip *)
  - assert (n = 1) by (ss; des_ifs). subst.
    (* generate step *)
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps. esplits; econs; eauto.
    (* restore match *)
    exploit block_always_terminator_prog; try eapply ISRC; eauto. i. des.
    unfold pc_sync in *. ss. des_ifs_safe. replace (add o 1) with (S o) by lia.
    erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
    rewrite add_1_r. auto.
  (* asgn *)
  - assert (n = 1) by (ss; des_ifs). subst.
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps.

    exists (l, (add o 1), x2 !-> (eval r e0); r, m, sk, ms).
    split; econs; eauto.
    + exploit block_always_terminator_prog; try eapply ISRC; eauto. i. des.
      unfold pc_sync in *. ss. des_ifs_safe. replace (add o 1) with (S o) by lia.
      erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
      rewrite add_1_r. auto.
    + eapply unused_prog_lookup in unused_p_msf; eauto.
      eapply unused_prog_lookup in unused_p_callee; eauto. ss; des.
      inv REG. econs.
      * i. destruct (string_dec x x2); subst.
        { do 2 rewrite t_update_eq. apply eval_regs_eq; eauto. }
        { rewrite t_update_neq; auto. rewrite t_update_neq; auto. }
      * erewrite t_update_neq; eauto.
  (* branch *)
  - inv x1; try simpl in SIMPL; clarify.
    unfold steps_to_sync_point' in n_steps. rewrite ISRC in n_steps.
    des_ifs_safe. inv tgt_steps.
    (* first step *)
    inv H5; clarify. simpl in H1. clarify. rename H10 into ITGT1.

    destruct b'; clarify.
    (* true branch: 2 more steps *)
    + assert (ITGT2: (uslh_prog p)[[(l', 0)]] =
                Some <{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>).
      { clear - IN. ss. rewrite IN. ss. }
      inv H7. inv H2; clarify. inv H8.
      assert (ITGT3: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l0 }}>).
      { clear - IN. ss. rewrite IN. ss. }
      inv H7. inv H2; clarify.

      unfold to_nat in H14. des_ifs_safe. simpl in Heq. des_ifs_safe.
      rewrite Heq. simpl in ms_msf. simpl. rewrite ms_msf in *. ss.

      destruct ms eqn:Hms.
      { (* already speculating *)
        unfold not_zero in *. rewrite Nat.eqb_refl in *.
        simpl in Heq0. injection Heq0; i; subst. clear Heq0.
        simpl in Heq. injection Heq; i; subst. clear Heq.
        simpl.

        assert (exists i', p[[(l0, 0)]] = Some i').
        { assert (wf_instr p <{{ branch e to l0 }}>) by (eapply wf_prog_lookup with (pc:=(l, o)); eauto).
          dup H1.
          unfold wf_instr in H2. des. unfold wf_lbl in H3. unfold fetch. cbn.
          destruct (nth_error p l0) as [l0blk|] eqn:Hl0; clarify.
          specialize (nth_error_In p l0 Hl0); i. 
          unfold wf_block in H0. rewrite Forall_forall in H0.
          apply H0 in H4. des. apply blk_not_empty_list in H4. destruct (fst l0blk); clarify.
          exists i. auto.
        }

        exists (l0, 0, r, m, sk, true).
        split.
        { econs; eauto. }
        { econs; eauto.
          { unfold pc_sync. simpl. des. 
            unfold fetch in H1. simpl in H1. 
            destruct (nth_error p l0) eqn:Hl0; clarify. destruct (fst p0); clarify.
            assert (wf_instr p <{{ branch e to l0 }}>) by (eapply wf_prog_lookup with (pc:=(l, o)); eauto).
            unfold wf_instr in H1. des. unfold wf_lbl in H2. unfold fetch. cbn.  
            rewrite Hl0 in H2. destruct p0. rewrite <- H2. simpl. auto.
          }
          { econs; eauto; i. inv REG. unfold TotalMap.t_apply, TotalMap.t_update, t_update.
            des. rewrite <- String.eqb_neq, String.eqb_sym in H2. rewrite H2.
            apply H3. rewrite String.eqb_sym, String.eqb_neq in H2. 
            split; auto.
          }
        }
      }
      { (* not yet speculating *)
        unfold not_zero in *. rewrite Nat.eqb_refl in *.
        simpl in Heq0. injection Heq0; i; subst. clear Heq0.
        simpl in Heq. simpl. rewrite negb_involutive. 
        des_ifs.
        { (* initiate speculation *)
          destruct (Nat.eqb n0 0) eqn:Hn0; clarify. simpl in *. clear Heq0.

          assert (exists i', p[[(l0, 0)]] = Some i').
          { assert (wf_instr p <{{ branch e to l0 }}>). 
            { eapply wf_prog_lookup with (pc:=(l, o)); eauto.
              unfold fetch. cbn. des_ifs.
            }
            dup H1.
            unfold wf_instr in H2. des. unfold wf_lbl in H3. unfold fetch. cbn.
            destruct (nth_error p l0) as [l0blk|] eqn:Hl0; clarify.
            specialize (nth_error_In p l0 Hl0); i. 
            unfold wf_block in H0. rewrite Forall_forall in H0.
            apply H0 in H4. des. apply blk_not_empty_list in H4. destruct (fst l0blk); clarify.
            exists i. auto.
          }

          des.
          exists (l0, 0, r, m, sk, true).
          split.
          { econs; eauto. 
            - unfold fetch. cbn. destruct (nth_error p l); clarify.
              destruct (nth_error (fst p0) o); clarify.
            - assert (to_nat (eval r' e) = Some n0) by (rewrite Heq; auto).
              erewrite <- H2. f_equal.
              specialize (rev_fetch p (l, o) p0 <{{ branch e to l0 }}> Heq3 ISRC); i.
              apply eval_regs_eq.
              + eapply unused_prog_lookup with (x:=msf) in H3; eauto.
              + eapply unused_prog_lookup with (x:=callee) in H3; eauto.
              + inv REG. unfold TotalMap.t_apply in H4.
                assumption.
            - destruct n0; clarify.
          }
          { econs; eauto.
            - unfold pc_sync. cbn. dup H1. unfold fetch in H2. cbn in H2.
              destruct (nth_error p l) eqn:Hfst; clarify.
              rename p0 into iblk. 
              specialize (nth_error_In p l Hfst); i.
              rewrite Forall_forall in H0. apply H0 in H3. unfold wf_block in H3. des.
              rewrite Forall_forall in H5.
              specialize (nth_error_In (fst iblk) o ISRC); i.
              apply H5 in H6. unfold wf_instr in H6. des.
              unfold wf_lbl in H7.
              destruct (nth_error p l0) eqn:Hl0; clarify.
              destruct p0. rewrite <- H7. cbn. destruct l1; clarify.
            - econs; eauto. i. inv REG.
              unfold TotalMap.t_apply, TotalMap.t_update, t_update.
              des. rewrite <- String.eqb_neq, String.eqb_sym in H2. rewrite H2.
              apply H3. rewrite String.eqb_sym, String.eqb_neq in H2. 
              split; auto.
          }
        }
        { (* don't initiate speculation *)
          destruct (Nat.eqb n0 0) eqn:Hn0; clarify. simpl in *. clear Heq0.

          assert (exists i', p[[(l0, 0)]] = Some i').
          { assert (wf_instr p <{{ branch e to l0 }}>). 
            { eapply wf_prog_lookup with (pc:=(l, o)); eauto.
              unfold fetch. cbn. des_ifs.
            }
            dup H1.
            unfold wf_instr in H2. des. unfold wf_lbl in H3. unfold fetch. cbn.
            destruct (nth_error p l0) as [l0blk|] eqn:Hl0; clarify.
            specialize (nth_error_In p l0 Hl0); i. 
            unfold wf_block in H0. rewrite Forall_forall in H0.
            apply H0 in H4. des. apply blk_not_empty_list in H4. destruct (fst l0blk); clarify.
            exists i. auto.
          }

          des.
          exists (l0, 0, r, m, sk, false).
          split.
          { econs; eauto. 
            - unfold fetch. cbn. destruct (nth_error p l); clarify.
              destruct (nth_error (fst p0) o); clarify.
            - assert (to_nat (eval r' e) = Some n0) by (rewrite Heq; auto).
              erewrite <- H2. f_equal.
              specialize (rev_fetch p (l, o) p0 <{{ branch e to l0 }}> Heq3 ISRC); i.
              apply eval_regs_eq.
              + eapply unused_prog_lookup with (x:=msf) in H3; eauto.
              + eapply unused_prog_lookup with (x:=callee) in H3; eauto.
              + inv REG. unfold TotalMap.t_apply in H4.
                assumption.
            - destruct n0; clarify.
          }
          { econs; eauto.
            - unfold pc_sync. cbn. dup H1. unfold fetch in H2. cbn in H2.
              destruct (nth_error p l) eqn:Hfst; clarify.
              rename p0 into iblk. 
              specialize (nth_error_In p l Hfst); i.
              rewrite Forall_forall in H0. apply H0 in H3. unfold wf_block in H3. des.
              rewrite Forall_forall in H5.
              specialize (nth_error_In (fst iblk) o ISRC); i.
              apply H5 in H6. unfold wf_instr in H6. des.
              unfold wf_lbl in H7.
              destruct (nth_error p l0) eqn:Hl0; clarify.
              destruct p0. rewrite <- H7. cbn. destruct l1; clarify.
            - econs; eauto. i. inv REG.
              unfold TotalMap.t_apply, TotalMap.t_update, t_update.
              des. rewrite <- String.eqb_neq, String.eqb_sym in H2. rewrite H2.
              apply H3. rewrite String.eqb_sym, String.eqb_neq in H2. 
              split; auto.
          }
        }
      }
    (* false branch 1 more steps *)
    + inv H7. inv H8. inv H2; clarify. simpl.
      
      unfold to_nat in H14. des_ifs_safe. simpl in Heq. des_ifs_safe.
      rewrite Heq. simpl in ms_msf. simpl. rewrite ms_msf in *. ss.

      destruct ms eqn:Hms; ss.
      { (* speculating *)
        injection Heq0; i; subst; ss. injection Heq; i; subst.
        clear Heq0. clear Heq. unfold not_zero. rewrite Nat.eqb_refl. ss.

        exists (l, (add o 1), r, m, sk, true).
        split.
        { econs; eauto. }
        { econs; eauto.
          { unfold pc_sync in *. ss. 
            destruct (nth_error p l) as [iblk|] eqn:Hfst; clarify.
            destruct (nth_error (fst iblk) o) eqn:Hsnd; clarify.
            specialize (rev_fetch p (l, o) iblk <{{ branch e to l0 }}> Hfst Hsnd); i.
            assert (~ (is_terminator <{{ branch e to l0 }}>)).
            { unfold not, is_terminator; i. destruct H2. }
            specialize (block_always_terminator_prog p (l, o) <{{ branch e to l0 }}> wfp0 H1 H2); i.
            des. unfold fetch in H3. cbn in H3. rewrite Hfst in H3.
            rewrite H3. rewrite add_1_r. 
            specialize (firstnth_error (fst iblk) o <{{ branch e to l0 }}> Hsnd); i.
            rewrite H4. rewrite fold_left_app. cbn. 
            unfold cptr. assert (forall n, (add n 1) = S n). { lia. }
            rewrite <- H5. rewrite add_assoc. auto.
          }
          { econs; eauto; i. unfold TotalMap.t_apply, TotalMap.t_update, t_update.
            dup H1. destruct H2. rewrite <- String.eqb_neq, String.eqb_sym in H2. rewrite H2. 
            inv REG. apply H4 in H1. unfold TotalMap.t_apply, TotalMap.t_update, t_update in H1.
            assumption.
          }
        }
      }
      { (* not speculating *)
        unfold not_zero in *. injection Heq0; i; subst. clear Heq0.
        rewrite Nat.eqb_refl in *. ss.
        des_ifs.
        { (* initiate speculation *)
          simpl. exists (l, (add o 1), r, m, sk, true).
          split.
          { econs; eauto.
            { unfold fetch. cbn. rewrite Heq1. eassumption. }
            { assert (to_nat (eval r' e) = Some n0).
              { unfold to_nat. rewrite Heq. auto. }
              rewrite <- H1. f_equal.
              specialize (rev_fetch p (l, o) p0 <{{ branch e to l0 }}> Heq1 ISRC); i.
              apply eval_regs_eq.
              - eapply unused_prog_lookup with (i:=<{{ branch e to l0 }}>) (x:=msf) in unused_p_msf; eauto.
              - eapply unused_prog_lookup with (i:=<{{ branch e to l0 }}>) (x:=callee) in unused_p_callee; eauto.
              - inv REG. i. eauto.
            }
          }
          { econs; eauto.
            { unfold pc_sync in *. ss. 
              destruct (nth_error p l) as [iblk|] eqn:Hfst; clarify.
              rename p0 into iblk.
              destruct (nth_error (fst iblk) o) eqn:Hsnd; clarify.
              specialize (rev_fetch p (l, o) iblk <{{ branch e to l0 }}> Hfst Hsnd); i.
              assert (~ (is_terminator <{{ branch e to l0 }}>)).
              { unfold not, is_terminator; i. destruct H2. }
              specialize (block_always_terminator_prog p (l, o) <{{ branch e to l0 }}> wfp0 H1 H2); i.
              des. unfold fetch in H3. cbn in H3. rewrite Hfst in H3.
              rewrite H3. rewrite add_1_r. 
              specialize (firstnth_error (fst iblk) o <{{ branch e to l0 }}> Hsnd); i.
              rewrite H4. rewrite fold_left_app. cbn. 
              unfold cptr. assert (forall n, (add n 1) = S n). { lia. }
              rewrite <- H5. rewrite add_assoc. auto.
            }
            { econs; eauto.
              { inv REG. i. unfold TotalMap.t_apply, TotalMap.t_update, t_update.
                dup H3. destruct H4. rewrite <- String.eqb_neq, String.eqb_sym in H4. rewrite H4.
                eauto.
              }
            }
          }
        }
        { (* don't initiate speculation *) 
          simpl. exists (l, (add o 1), r, m, sk, false).
          specialize (rev_fetch p (l, o) p0 <{{ branch e to l0 }}> Heq1 ISRC); i.
          split.
          { econs; eauto.
            { assert (to_nat (eval r' e) = Some n0).
              { unfold to_nat. rewrite Heq. auto. }
              rewrite <- H2. f_equal.
              specialize (rev_fetch p (l, o) p0 <{{ branch e to l0 }}> Heq1 ISRC); i.
              apply eval_regs_eq.
              - eapply unused_prog_lookup with (i:=<{{ branch e to l0 }}>) (x:=msf) in unused_p_msf; eauto.
              - eapply unused_prog_lookup with (i:=<{{ branch e to l0 }}>) (x:=callee) in unused_p_callee; eauto.
              - inv REG. i. eauto.
            }
          }
          { econs; eauto.
            { unfold pc_sync in *. ss. 
              destruct (nth_error p l) as [iblk|] eqn:Hfst; clarify.
              rename p0 into iblk.
              destruct (nth_error (fst iblk) o) eqn:Hsnd; clarify.
              specialize (rev_fetch p (l, o) iblk <{{ branch e to l0 }}> Hfst Hsnd); i.
              assert (~ (is_terminator <{{ branch e to l0 }}>)).
              { unfold not, is_terminator; i. destruct H2. }
              specialize (block_always_terminator_prog p (l, o) <{{ branch e to l0 }}> wfp0 H1 H2); i.
              des. unfold fetch in H3. cbn in H3. rewrite Hfst in H3.
              rewrite H3. rewrite add_1_r. 
              specialize (firstnth_error (fst iblk) o <{{ branch e to l0 }}> Hsnd); i.
              rewrite H4. rewrite fold_left_app. cbn. 
              unfold cptr. assert (forall n, (add n 1) = S n). { lia. }
              rewrite <- H5. rewrite add_assoc. auto.
            }
            { econs; eauto.
              { inv REG. i. unfold TotalMap.t_apply, TotalMap.t_update, t_update.
                dup H4. destruct H5. rewrite <- String.eqb_neq, String.eqb_sym in H5. rewrite H5.
                eauto.
              }
            }
          }
        }
      }
  (* jump *)
  - assert (n = 1) by (ss; des_ifs). subst.
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps.

    exists (l1, 0, r, m, sk, ms). split; econs; eauto.

    exploit wf_prog_lookup; try eapply ISRC; eauto. i.
    ss. unfold pc_sync, wf_lbl in *. ss. des_ifs_safe. ss.
    subst. inv wfp0. rewrite Forall_forall in H2.
    eapply nth_error_In in Heq. eapply H2 in Heq.
    red in Heq. des. ss.
  (* load *)
  - assert (n = 1) by (ss; des_ifs). subst.
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps.

    exists (((l, o) + 1), x2 !-> v'; r, m, sk, ms).

    eapply unused_prog_lookup in unused_p_msf; eauto.
    eapply unused_prog_lookup in unused_p_callee; eauto.

    split; econs; eauto.
    + clear - H11 REG unused_p_msf unused_p_callee.
      inv REG. ss. rewrite H0 in H11. ss. des.
      des_ifs. rewrite <- H11. f_equal. eapply eval_regs_eq; eauto.
    + exploit block_always_terminator_prog; try eapply ISRC; eauto. i. des.
      unfold pc_sync in *. ss. des_ifs_safe. replace (add o 1) with (S o) by lia.
      erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
      rewrite add_1_r. auto.
    + red. splits; i.
      * destruct (string_dec x x2); subst.
        { do 2 rewrite t_update_eq; eauto. }
        { rewrite t_update_neq; eauto. rewrite t_update_neq; eauto.
          inv REG. eauto. }
      * ss. des. rewrite t_update_neq; eauto.
  (* store *)
  - assert (n = 1) by (ss; des_ifs). subst.
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps.

    eapply unused_prog_lookup in unused_p_msf; eauto.
    eapply unused_prog_lookup in unused_p_callee; eauto.

    exists (((l, o) + 1), r, (upd n m (eval r e')), sk, ms).
    simpl. split.
    + eapply ISMI_Store; eauto.
      clear - H11 REG unused_p_msf unused_p_callee.
      inv REG. ss. rewrite H0 in H11. ss. des.
      des_ifs. rewrite <- H11. f_equal. eapply eval_regs_eq; eauto.
    + simpl in unused_p_callee, unused_p_msf. des. dup REG. inv REG.
      erewrite <- eval_regs_eq with (r := r) (r' := r'); eauto.
      econs; eauto.
      exploit block_always_terminator_prog; try eapply ISRC; eauto. i. des.
      unfold pc_sync in *. ss. des_ifs_safe. replace (add o 1) with (S o) by lia.
      erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
      rewrite add_1_r. auto.
  (* call *)
  - inv x1; try simpl in SIMPL; clarify.
    unfold steps_to_sync_point' in n_steps. rewrite ISRC in n_steps.
    des_ifs_safe. inv tgt_steps.

    inv H5; clarify. simpl in H1.
    inv H7. inv H3; clarify. simpl in H6. clarify.
    inv H9. inv H2; clarify.
    2:{ inv H7. inv H2. }

    assert (ITGT: (uslh_prog p)[[lo + 1]] = Some <{{ msf := (callee = (& (fst lo))) ? msf : 1 }}>).
    { exploit head_call_target; try eapply H11; eauto. i. des. subst. eauto. }

    inv H7. inv H8. inv H2; clarify.
    dup H15. destruct lo as [l' o']. simpl in H1. des_ifs_safe.

    assert (DLEN: l' < Datatypes.length p \/ Datatypes.length p <= l') by lia.

    destruct DLEN as [DLEN|DLEN]; cycle 1.
    { exfalso.
      unfold uslh_prog in H15. des_ifs_safe.
      exploit new_prog_ct_cut.
      { eapply Heq0. }
      { eapply H15. }
      { eapply new_prog_no_ct. eauto. }
      i. eapply mapM_perserve_len in Heq0. rewrite length_add_index in Heq0.
      ss. des_ifs_safe. clear -Heq1 DLEN Heq0.
      assert (nth_error l1 l' <> None) by (ii; clarify).
      rewrite nth_error_Some in H. lia. }

    assert (CESRC: exists b_src', nth_error p l' = Some b_src').
    { rewrite <- nth_error_Some in DLEN. destruct (nth_error p l'); eauto.
      exfalso. eauto. }
    des.
    assert (CTSRC: snd b_src' = true).
    { destruct b_src'. simpl. destruct b; auto.
      hexploit no_ctarget_exists; try eapply CESRC; eauto. }

    hexploit head_call_target; try eapply H11; eauto.
    intros (l1 & b_tgt' & PC & BLKTGT & ITGT'). clarify.

    esplits.
    + simpl. eapply ISMI_Call; try eapply ISRC.
      { inv REG. rewrite H3 in H14.
        exploit unused_prog_lookup; try eapply unused_p_msf; eauto.
        exploit unused_prog_lookup; try eapply unused_p_callee; eauto.
        intros UNUSE1 UNUSE2.

        ss. rewrite BLKTGT in *.
        ss. des_ifs_safe.
        rewrite t_update_neq in Heq; [|ii; clarify].
        rewrite H3 in Heq. ss. clarify. destruct ms; ss.
        unfold to_fp in H14. des_ifs. rewrite eval_unused_update in Heq; eauto.
        rewrite eval_regs_eq with (r' := r'); eauto.
        rewrite Heq. auto. }
      { eauto. }
      { simpl. eauto. }
      { eauto. }
      { simpl. auto. }
    + simpl. rewrite andb_true_r. econs.
      * simpl. unfold pc_sync. simpl.
        rewrite CESRC. destruct b_src' as [b_src' is_proc']. ss; clarify.
        rewrite eqb_reflx.
        destruct b_src' eqn:BSRC; auto.
        exfalso. clear - H0 CESRC.
        eapply nth_error_In in CESRC. eapply Forall_forall in H0; eauto.
        red in H0. des. ss.
      * exploit unused_prog_lookup; try eapply unused_p_callee; eauto.
        intros UNUSED. econs; ss; i.
        { des. rewrite ms_msf. rewrite t_update_eq.
          rewrite t_update_neq; eauto. rewrite t_update_neq; eauto.
          inv REG; eauto. }
        { des. rewrite ms_msf. repeat rewrite t_update_eq. ss.
          rewrite t_update_neq; [|ii;clarify]. rewrite ms_msf in *. ss.
          rewrite t_update_neq in H14; [|ii;clarify].
          rewrite ms_msf in H14. ss.
          rewrite eval_unused_update in H14; auto.
          clear - H14. destruct ms; ss; clarify.
          - des_ifs.
          - unfold to_fp in H14. des_ifs_safe. ss. clarify.
            destruct ((l0 =? l1)%nat) eqn: X; ss.
            + rewrite Nat.eqb_sym in X. rewrite X. ss.
            + rewrite Nat.eqb_sym in X. rewrite X. ss. }
      * simpl. rewrite STK.
        exploit block_always_terminator_prog; try eapply ISRC; eauto.
        intros (i' & ITGT'').
        unfold pc_sync in *. ss. des_ifs_safe. replace (add o 1) with (S o) by lia.
        erewrite firstnth_error; eauto. rewrite fold_left_app. cbn.
        rewrite add_1_r. f_equal. f_equal.
        rewrite pair_equal_spec. split; auto. lia.
  (* ctarget *)
  - exfalso. eapply no_ct_prog_src; eauto.
  (* ret *)
  - assert (n = 1) by (ss; des_ifs). subst.
    inv tgt_steps. inv H7. inv H2; clarify; inv x1; inv MATCH.
    clear n_steps.

    destruct sk ; [ss|].

    exists (c, r, m, sk, ms). simpl. split.
    + eapply ISMI_Ret; eauto.
    + econs; eauto; simpl in STK; des_ifs.
Qed.

Lemma ultimate_slh_bcc (p: prog) : forall n ic1 sc1 sc2 ds os,
  no_ct_prog p ->
  wf_prog p ->
  (* wf_ds' (uslh_prog p) ds -> *)
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0) ->
  match_cfgs p ic1 sc1 ->
  uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( sc2 ))> ->
  exists ic2, p |- <(( S_Running ic1 ))> -->i*_ ds ^^ os <(( ic2 ))>.
Proof.
  intros n. induction n using strong_induction_le; ii.
  - inv H5. esplits. econs.
  - destruct (steps_to_sync_point' p ic1 ds) eqn:SYNCPT; cycle 1.
    { inv H6. inv H5. destruct pc as [l o].
      unfold steps_to_sync_point' in SYNCPT.
      destruct (p[[(l, o)]]) eqn: ISRC; cycle 1.
      { (* by PC *) unfold pc_sync in PC. ss. des_ifs. }
      destruct i; clarify.
      - exploit src_inv; eauto. i. des. inv x1; ss; clarify.
        inv H8; clarify.
      - exploit src_inv; eauto. i. des. inv x1; ss; clarify.
        destruct n.
        + inv H13. inv H8; clarify. ss. esplits. econs.
        + inv H8; clarify. inv H13. inv H6; clarify. }
    assert (SZ: n0 > S n \/ n0 <= S n) by lia.
    destruct SZ as [SZ|SZ].
    + destruct ic1 as (c1 & ms). unfold steps_to_sync_point' in SYNCPT.
      des_ifs_safe. rename c into pc.
      inv H5. exploit src_inv; eauto. i. des.
      exploit unused_prog_lookup; try eapply H2; eauto. intros UNUSED1.
      exploit unused_prog_lookup; try eapply H3; eauto. intros UNUSED2.
      destruct i; ss; clarify; try lia.
      (* brnach *)
      * inv x1; try (sfby (simpl in SIMPL; clarify)).
        des_ifs_safe. inv H6; clarify. inv H10; clarify.
        ss. clarify.
        exploit (ISMI_Branch p pc _ r m l ms); try eapply Heq; eauto.
        { rewrite <- H17. rewrite H4. simpl. destruct ms; ss.
          erewrite eval_regs_eq; eauto. inv REG. eauto. }
        instantiate (1:= b'). i. rewrite cons_app. rewrite cons_app with (a:= OBranch (not_zero n0)).
        destruct b'.
        { destruct n.
          { inv H12. esplits. econs; eauto. econs. }
          destruct n; [|lia].
          inv H12. inv H11.
          assert ((uslh_prog p) [[(l', 0)]] = Some <{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>).
          { ss. rewrite IN. ss. }
          inv H6; clarify. esplits. econs; eauto. ss. econs. }
        destruct n; [|lia].
        inv H12. esplits. econs; eauto. econs.
      (* call *)
      * inv x1; try (sfby (simpl in SIMPL; clarify)). clarify.
        destruct n.
        { inv H6. inv H12. inv H7; clarify. }
        des_ifs_safe. inv H6; clarify. inv H10; clarify.
        ss. subst. inv H12. inv H9; clarify.
        destruct (nth_error p (fst pc'0)) eqn:BSRC.
        2:{ exploit (ISMI_Call_F p pc pc'0 r m); eauto.
            2:{ ii. clarify. }
            { instantiate (2:=ms).
              rewrite H4 in H18. rewrite <- H18. ss.
              rewrite t_update_neq; [|ii;clarify].
              rewrite H4. ss. destruct ms; ss.
              rewrite eval_unused_update; eauto.
              erewrite eval_regs_eq; eauto. inv REG; eauto. }
            instantiate (1:= l). i. ss. clarify. inv H11.
            { exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            destruct n0; cycle 1.
            { lia. }
            inv H6. inv H5; clarify.
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. } }
        destruct (snd p0) eqn:CT; cycle 1.
        { exploit (ISMI_Call_F p pc pc'0 r m); eauto.
          2:{ i. clarify. auto. }
            { instantiate (2:=ms).
              rewrite H4 in H18. rewrite <- H18. ss.
              rewrite t_update_neq; [|ii;clarify].
              rewrite H4. ss. destruct ms; ss.
              rewrite eval_unused_update; eauto.
              erewrite eval_regs_eq; eauto. inv REG; eauto. }
            instantiate (1:= l). i. ss. clarify. inv H11.
            { exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            destruct n0; cycle 1.
            { lia. }
            inv H6. inv H5; clarify.
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. } }
        destruct (eq_decidable (snd pc'0) 0); cycle 1.
        { exploit (ISMI_Call_F p pc pc'0 r m); eauto.
            { instantiate (2:=ms).
              rewrite H4 in H18. rewrite <- H18. ss.
              rewrite t_update_neq; [|ii;clarify].
              rewrite H4. ss. destruct ms; ss.
              rewrite eval_unused_update; eauto.
              erewrite eval_regs_eq; eauto. inv REG; eauto. }
            instantiate (1:= l). i. ss. clarify. inv H11.
            { exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            destruct n0; cycle 1.
            { lia. }
            inv H7. inv H5; clarify.
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. }
            { ss. exists S_Fault. rewrite <- app_nil_r with (l:=[OCall l0]).
              rewrite <- app_nil_r with (l:=[DCall lo]). econs; eauto. econs. } }
        exploit (ISMI_Call p pc pc'0 r m); eauto.
        { instantiate (2:=ms).
          rewrite H4 in H18. rewrite <- H18. ss.
          rewrite t_update_neq; [|ii;clarify].
          rewrite H4. ss. destruct ms; ss.
          rewrite eval_unused_update; eauto.
          erewrite eval_regs_eq; eauto. inv REG; eauto. }
        instantiate (1:= l). ii. ss. clarify. inv H11.
        { rewrite <- app_nil_r with (l:=[OCall l0]).
          rewrite <- app_nil_r with (l:=[DCall lo]). eexists. econs; eauto. econs. }
        destruct n0; cycle 1.
        { lia. }
        inv H7. inv H5; clarify.
        { ss. rewrite <- app_nil_r with (l:=[OCall l0]).
          rewrite <- app_nil_r with (l:=[DCall lo]). eexists. econs; eauto. econs. }
        { ss. rewrite <- app_nil_r with (l:=[OCall l0]).
          rewrite <- app_nil_r with (l:=[DCall lo]). eexists. econs; eauto. econs. }
    + assert (SZ': n0 > 0).
      { unfold steps_to_sync_point' in SYNCPT. des_ifs; lia. }
      destruct (eq_decidable (S n) n0).
      { destruct sc2.
        - rewrite H7 in H6.
          exploit ultimate_slh_bcc_single_cycle_refactor; try eapply H6; eauto.
          i. des; eauto. rewrite <- app_nil_r with (l:=ds). rewrite <- app_nil_r with (l:=os).
          eexists. econs 2; eauto. econs.
        - exfalso. clear - H6. ginduction n; ii.
          { inv H6. inv H5. inv H0. }
          { inv H6. destruct sc2; eauto; try sfby inv H0.
            - inv H5. inv H1.
            - inv H5. inv H1. }
        - destruct ic1 as (c1 & ms). unfold steps_to_sync_point' in SYNCPT.
          des_ifs_safe. rename c into pc.
          inv H5. exploit src_inv; eauto. i. des.
          destruct i; ss; clarify; inv x1; try inv MATCH; ss;
            try (sfby (inv H6; clarify; inv H12; inv H7; clarify; inv H12)).
          + des_ifs_safe. inv H6. inv H11; ss; clarify.
            destruct b'; clarify.
            * inv H13.
              assert ((uslh_prog p) [[(l', 0)]] = Some <{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>).
              { ss. rewrite IN. ss. }
              inv H6; clarify.
              inv H11; clarify. inv H12.
              assert ((uslh_prog p) [[(l', 1)]] = Some <{{ jump l0 }}>).
              { ss. rewrite IN. ss. }
              inv H6; clarify.
            * inv H13. inv H11. inv H6; clarify.
          + des_ifs_safe. inv H6. inv H10; clarify. inv H12.
            inv H7; clarify. inv H13. ss. clarify. inv H7.
            2:{ inv H12. inv H11. inv H6. }
            inv H12. inv H11. inv H6.
        - destruct ic1 as (c1 & ms). unfold steps_to_sync_point' in SYNCPT.
          des_ifs_safe. rename c into pc.
          inv H5. exploit src_inv; eauto.  i. des.
          destruct i; ss; clarify; inv x1; try inv MATCH; ss;
            try (sfby (inv H6; clarify; inv H12; inv H7; clarify; inv H12)).
          + des_ifs_safe. inv H6. inv H11; ss; clarify.
            destruct b'; clarify.
            * inv H13.
              assert ((uslh_prog p) [[(l', 0)]] = Some <{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>).
              { ss. rewrite IN. ss. }
              inv H6; clarify.
              inv H11; clarify. inv H12.
              assert ((uslh_prog p) [[(l', 1)]] = Some <{{ jump l0 }}>).
              { ss. rewrite IN. ss. }
              inv H6; clarify.
            * inv H13. inv H11. inv H6; clarify.
          + des_ifs_safe. inv H6. inv H10; clarify. inv H12.
            inv H7; clarify. inv H13. ss. clarify. inv H7.
            2:{ inv H12. inv H11. inv H6. }
            inv H12. inv H11. inv H6.
          (* ret. stack is empty *)
          + inv H6. inv H12. inv H7; clarify. esplits.
            econs 2; [|econs].
            assert (l = []).
            { clear -STK. destruct l; ss. des_ifs. }
            subst. eapply ISMI_Term. eauto. }
      assert (exists sc1' ds1 ds2 os1 os2,
               uslh_prog p |- <(( S_Running sc1 ))> -->*_ ds1 ^^ os1 ^^ n0 <(( S_Running sc1' ))>
             /\ uslh_prog p |- <(( S_Running sc1' ))> -->*_ ds2 ^^ os2 ^^ (S n - n0) <(( sc2 ))>
             /\ ds = ds1 ++ ds2 /\ os = os1 ++ os2).
      { exploit multi_spec_splitting; try eapply H6; eauto. i. des.
        assert (exists sc1', scm = S_Running sc1').
        { inv x1; [des_ifs; lia|inv H9; eauto]. }
        des. subst. esplits; eauto. }

      des. subst. (* eapply wf_ds_app in H1. des. *)
      assert (steps_to_sync_point' p ic1 ds1 = Some n0).
      { destruct ic1 as (c1 & ms). unfold steps_to_sync_point' in SYNCPT.
        des_ifs_safe. rename c into pc.
        dup H5. inv H5. exploit src_inv; eauto. intros (i' & ITGT1 & IMATCH).
        assert (SIMPL: simple_inst i \/ ~ simple_inst i) by (destruct i; ss; eauto).
        destruct SIMPL as [SIMPL | NSIMPL].
        - assert (n0 = 1) by des_ifs. subst.
          unfold steps_to_sync_point'. rewrite Heq. des_ifs.
        - destruct i; simpl in NSIMPL; clarify.
          3:{ exfalso. eapply no_ct_prog_src; eauto. }
          + inv IMATCH; [ss|]. destruct ds1.
            { ss. exfalso. inv H8; [lia|]. inv H11; clarify. }
            simpl in SYNCPT. des_ifs_safe. simpl. rewrite Heq. auto.
          + inv IMATCH; [ss|]. destruct ds1.
            { des_ifs_safe. exfalso. inv H8. inv H14; clarify.
              inv H16. inv H11; clarify. }
            simpl in SYNCPT. des_ifs_safe. simpl. rewrite Heq. auto. }
      exploit ultimate_slh_bcc_single_cycle_refactor; try eapply H8; eauto. i. des.
      exploit H; try eapply H9; eauto.
      { lia. }
      { inv x1. inv REG. ss. }
      i. des. exists ic0. econs; eauto.
Qed.

Definition first_blk_call (p: prog) : Prop :=
  match nth_error p 0 with
  | None => False (* unreachable *)
  | Some (blk, b) => if b then True else False
  end.

Lemma ultimate_slh_bcc_init
  (p: prog) n ir sc1 sr m sc2 ds os
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SC1: sc1 = ((0,0), sr, m, @nil cptr, true, false))
  (INIT1: Rsync ir sr false)
  (INIT2: sr ! callee = FP 0)
  (TGT: uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( sc2 ))>) :
  exists ic2, p |- <(( S_Running ((0,0), ir, m, [], false) ))> -->i*_ ds ^^ os <(( ic2 ))>.
Proof.
  destruct n.
  { inv TGT. esplits. econs. }
  assert (CT: (uslh_prog p)[[(0, 0)]] = Some <{{ ctarget }}>).
  { red in FST. des_ifs. eapply ctarget_exists; eauto. }
  destruct n.
  { inv TGT. inv H5. inv H0; clarify. ss. do 2 econs. }
  exploit head_call_target; eauto. i. des; clarify.
  replace ((0,0) + 1) with (0, 1) in x2 by ss.
  inv TGT. inv H0; clarify. inv H5. inv H0; clarify. simpl.
  exploit ultimate_slh_bcc; try eapply H6; eauto.
  { red in INIT1. des. simpl. rewrite INIT2. ss. }
  econs; try sfby ss.
  - unfold pc_sync. ss. clear -FST WFP.
    red in FST. des_ifs; ss; clarify.
    inv WFP. ss. subst. inv H0. inv H3.
    red in H0. ss. lia.
  - inv INIT1. split; ii.
    + des. rewrite t_update_neq; eauto.
    + rewrite t_update_eq. simpl. rewrite INIT2. ss.
Qed.

(** * Definition of Relative Secure *)

Definition seq_same_obs p pc r1 r2 m1 m2 stk : Prop :=
  forall os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->*^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->*^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition spec_same_obs p pc r1 r2 m1 m2 stk b : Prop :=
  forall ds n m os1 os2 c1 c2 (* (WFDS: wf_ds' p ds) *),
  p |- <(( S_Running (pc, r1, m1, stk, b, false) ))> -->*_ds^^os1^^n <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b, false) ))> -->*_ds^^ os2^^m <(( c2 ))> -> (* YH: Yan said this can be generalized different numbers of steps. *)
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition ideal_same_obs p pc r1 r2 m1 m2 stk : Prop :=
  forall ds os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ds^^os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ds^^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition relative_secure (p:prog) (trans1 : prog -> prog)
  (r1 r2 r1' r2' : reg) (m1 m2 : mem): Prop :=
  seq_same_obs p (0,0) r1 r2 m1 m2 [] ->
  Rsync r1 r1' false -> Rsync r2 r2' false ->
  spec_same_obs (trans1 p) (0,0) r1' r2' m1 m2 [] true.

(** * Ultimate Speculative Load Hardening *) 

Require Import Stdlib.Program.Equality.

Lemma multi_seq_app p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->*^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof.
  intro H. dependent induction H.
  - intro H. cbn. assumption.
  - intro Hlast. apply IHmulti_seq_inst in Hlast.
    rewrite <- app_assoc. econstructor; eassumption.
Qed.

Lemma multi_seq_rcons p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof.
  intros Hmulti Hstep.
  eapply multi_seq_inst_trans in Hstep. 2: constructor.
  rewrite app_nil_r in Hstep.
  eapply multi_seq_app; eassumption.
Qed.

Lemma ideal_step_one_or_no_directive p pc r m stk b ds os c:
  p |- <(( S_Running (pc, r, m, stk, b) ))> -->i_ ds ^^ os <(( c ))> ->
  ds = [] \/ exists d, ds = [d].
Proof.
  inversion 1; subst; try now left.
  all: right; eexists; reflexivity.
Qed.

Lemma ideal_pc_determines_dir_obs_count p pc r1 r2 m1 m2 stk b ds1 ds2 os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1, stk, b) ))> -->i_ ds1 ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b) ))> -->i_ ds2 ^^ os2 <(( c2 ))> ->
  Datatypes.length ds1 = Datatypes.length ds2 /\ Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion 1; inversion 1; subst; split; try reflexivity.
  all: try congruence.
Qed.

Lemma seq_pc_determines_obs_count p pc r1 r2 m1 m2 stk os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->^ os2 <(( c2 ))> ->
      Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion 1 ; inversion 1; try congruence. all: reflexivity.
Qed.

Lemma app_eq_len_tail_eq A (l1a l1b  l2a l2b: list A):
  l1a ++ l1b = l2a ++ l2b ->
  Datatypes.length l1a = Datatypes.length l2a ->
  l1b = l2b.
Proof.
  intros Heq Hlen.
  induction l1a in l2a, Heq, Hlen |- *; destruct l2a.
  - assumption.
  - cbn in *. congruence.
  - cbn in *. congruence.
  - cbn in Heq. inv Heq.
    eapply IHl1a. 1: eassumption.
    cbn in Hlen. now inv Hlen.
Qed.

Lemma seq_steps_preserves_seq_same_obs p pc r1 r2 m1 m2 stk os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->^ os1 <(( S_Running (pc', r1', m1', stk') ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->^ os2 <(( S_Running (pc', r2', m2', stk') ))> ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hseq_same_obs Hstep1 Hstep2.
  unfold seq_same_obs.
  intros os1' os2' c1 c2 Hmulti1 Hmulti2.
  eapply multi_seq_inst_trans in Hmulti1, Hmulti2. 2,3: eassumption.
  specialize (Hseq_same_obs _ _ _ _ Hmulti1 Hmulti2).
  destruct Hseq_same_obs as [ [or1 H] | [or2 H] ].
  - left. exists or1. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
  - right. exists or2. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
Qed.

Lemma ideal_nonspec_seq p pc r m stk ds os pc' r' m' stk':
  p |- <(( S_Running (pc, r, m, stk, false) ))> -->i_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  p |- <(( S_Running (pc, r, m, stk) ))> -->^ os <(( S_Running (pc', r', m', stk') ))>.
Proof.
  inversion 1; subst; try (econstructor; eassumption).
  - eapply SSMI_Branch. 1,2: eassumption.
    cbn in H16. apply (f_equal negb) in H16. cbn in H16.
    rewrite negb_involutive in H16.
    symmetry in H16. apply eqb_prop in H16 as ->. reflexivity.
  - cbn in H14. apply (f_equal negb) in H14. cbn in H14. rewrite negb_involutive in H14.
    symmetry in H14. rewrite Nat.eqb_eq in H14.
    destruct pc'; cbn in *; subst.
    econstructor; eassumption.
Qed.

Lemma multi_ideal_ms_monotonic {p pc r m stk ms ds os pc' r' m' stk'}:
  p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  ms = false.
Proof.
  intro Hmulti.
  dependent induction Hmulti.
  - reflexivity.
  - destruct ic2. 2-4: inv Hmulti; inv H0.
    destruct a as [ [ [ [pc'' r''] m''] stk''] ms''].
    erewrite IHHmulti with (ms := ms'') in H. 2, 3: reflexivity.
    inv H; try reflexivity.
    + symmetry in H16. now apply orb_false_elim in H16.
    + symmetry in H14. now apply orb_false_elim in H14.
Qed.

Lemma multi_ideal_nonspec_seq p pc r m stk ds os pc' r' m' stk':
  p |- <(( S_Running (pc, r, m, stk, false) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  p |- <(( S_Running (pc, r, m, stk) ))> -->*^ os <(( S_Running (pc', r', m', stk') ))>.
Proof.
  intro H. dependent induction H.
  - constructor.
  - assert (exists pc'' r'' m'' stk'', ic2 = S_Running (pc'', r'', m'', stk'', false)).
    {
      inv H0. 1: repeat eexists; reflexivity.
      inv H1; repeat eexists.
      all: try (rewrite (multi_ideal_ms_monotonic H2); reflexivity).
      3, 4: inv H2; inv H1. (* I think these two cases leave unresolved evars *)
      all: apply multi_ideal_ms_monotonic, orb_false_elim in H2 as [-> _].
      all: reflexivity.
      Unshelve.
      all: assumption.
    }
    destruct H1 as (pc'' & r'' & m'' & stk'' & ->).
    econstructor.
    + eapply ideal_nonspec_seq. eassumption.
    + eapply IHmulti_ideal_inst; reflexivity.
Qed.

Lemma ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 stk ds os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false ) ))> -->i_ ds ^^ os1 <(( S_Running (pc', r1', m1', stk', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false ) ))> -->i_ ds ^^ os2 <(( S_Running (pc', r2', m2', stk', false) ))> ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hsso Hst1 Hst2.
  eapply seq_steps_preserves_seq_same_obs. 1: eassumption.
  all: eapply ideal_nonspec_seq; eassumption.
Qed.

Lemma multi_ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 stk ds os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false ) ))> -->i*_ ds ^^ os1 <(( S_Running (pc', r1', m1', stk', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false ) ))> -->i*_ ds ^^ os2 <(( S_Running (pc', r2', m2', stk', false) ))> ->
  Datatypes.length os1 = Datatypes.length os2 ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hsso Hsteps1%multi_ideal_nonspec_seq Hsteps2%multi_ideal_nonspec_seq Hlen.
  intros os1' os2' c1' c2 Hsteps1' Hsteps2'.
  edestruct Hsso. 1, 2: eapply multi_seq_app; eassumption.
  - left.
    destruct H. exists x.
    rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. all: eassumption.
  - right.
    destruct H. exists x.
    rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    symmetry. assumption.
Qed.

Lemma ideal_multi_no_dirs_run_or_term p pc r m stk b os ic:
  p |- <(( S_Running (pc, r, m, stk, b) ))> -->i*_ [] ^^ os <(( ic ))> ->
  exists pc' r' m' stk', p |- <(( S_Running (pc, r, m, stk, b) ))> -->i*_ [] ^^ os <(( S_Running (pc', r', m', stk', b) ))>
                 /\  (ic = S_Running (pc', r', m', stk', b) \/ ic = S_Term /\ p |- <(( S_Running (pc', r', m', stk', b) ))> -->i_ [] ^^ [] <(( S_Term ))>).
Proof.
  intros H. dependent induction H.
  - repeat eexists. 2: left; reflexivity.
    constructor.
  - apply app_eq_nil in x as [-> ->].
    inv H.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      econstructor; try eassumption. reflexivity.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      econstructor; try eassumption. reflexivity.
    + edestruct IHmulti_ideal_inst as (pc'' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + inv H0. 2: inv H1.
      repeat eexists. 2: right; split.
      * cbn; constructor.
      * reflexivity.
      * now constructor.
Qed.

Lemma ideal_eval_multi_exec_split {p pc r1 r2 m1 m2 stk ds os1 os2 c1 c2}:
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  exists pc1' pc2' r1' r2' m1' m2' stk1' stk2' ds' os1' os2',
    p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ ds' ^^ os1' <(( S_Running (pc1', r1', m1', stk1', false) ))> /\
    p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ ds' ^^ os2' <(( S_Running (pc2', r2', m2', stk2', false) ))> /\
   (ds' = ds /\ os1' = os1 /\ os2' = os2
    /\ (c1 = S_Running (pc1', r1', m1', stk1', false) \/ c1 = S_Term /\ p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ [] ^^ [] <(( S_Term ))>)
    /\ (c2 = S_Running (pc2', r2', m2', stk2', false) \/ c2 = S_Term /\ p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ [] ^^ [] <(( S_Term))>)
    \/ exists ds'' os1'' os2'',
       ds = ds' ++ ds'' /\ os1 = os1' ++ os1'' /\ os2 = os2' ++ os2'' /\ pc1' = pc2' /\ stk1' = stk2' /\ Datatypes.length os1' = Datatypes.length os2' /\
       (
        c1 = S_Fault /\ c2 = S_Fault /\ p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ ds'' ^^ os1'' <(( S_Fault ))> /\ p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ ds'' ^^os2'' <(( S_Fault))>
        \/
        exists pc'' r1'' r2'' m1'' m2'' stk'' d ds''' o1 os1''' o2 os2''',
        ds'' = d :: ds''' /\ os1'' = o1 :: os1''' /\ os2'' = o2 :: os2''' /\
        p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ [d] ^^ [o1] <(( S_Running (pc'', r1'', m1'', stk'', true) ))> /\ p |- <(( S_Running (pc'', r1'', m1'', stk'', true) ))> -->i*_ ds''' ^^ os1''' <(( c1 ))> /\
        p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ [d] ^^ [o2] <(( S_Running (pc'', r2'', m2'', stk'', true) ))> /\ p |- <(( S_Running (pc'', r2'', m2'', stk'', true) ))> -->i*_ ds''' ^^ os2''' <(( c2 ))>
       )
   ).
Proof.
  intros Hseq_same Hexec1 Hexec2.
  dependent induction Hexec1 generalizing pc r1 r2 m1 m2 stk os2 Hseq_same; dependent destruction Hexec2.
  - repeat eexists. 1, 2: eapply multi_ideal_inst_refl.
    left. repeat split; try left; reflexivity.
  - apply app_eq_nil in x as [-> ->].
    eapply multi_ideal_inst_trans in Hexec2. 2: eassumption.
    apply ideal_multi_no_dirs_run_or_term in Hexec2 as (pc' & r' & m' & stk' & Hstp & Hrt).
    repeat eexists.
    1: eapply multi_ideal_inst_refl.
    2: left; repeat split.
    2: now left.
    all: eassumption.
  - symmetry in x. apply app_eq_nil in x as [-> ->].
    eapply multi_ideal_inst_trans in Hexec1. 2: eassumption.
    apply ideal_multi_no_dirs_run_or_term in Hexec1 as (pc' & r' & m' & stk' & Hstp & Hrt).
    repeat eexists.
    2: eapply multi_ideal_inst_refl.
    2: left; repeat split.
    3: now left.
    all: eassumption. 
  - inversion H; inversion H0; try congruence; subst; cbn in *; subst.
    (* 
       Decided that (at least for now) it would likely be easier to handle all cases directly, instead of performing a case distinction on the type of directive consumed.
    *)
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
    * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change os0 with ([] ++ os0).
      2: change os3 with ([] ++ os3).
      all: econstructor; eassumption.
    * repeat eexists. 3: right; eassumption.
      all: change x7 with ([] ++ x7).  (* TODO: this is very fragile. it would be much better to have a consistent name for these *)
      1: change x8 with ([] ++ x8).
      2: change x9 with ([] ++ x9).
      all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
    * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change os0 with ([] ++ os0).
      2: change os3 with ([] ++ os3).
      all: econstructor; eassumption.
    * repeat eexists. 3: right; eassumption.
      all: change x9 with ([] ++ x9). 
      1: change x10 with ([] ++ x10).
      2: change x11 with ([] ++ x11).
      all: econstructor; eassumption.
    + rewrite H6 in H19. inv H19. inv x.
      assert (not_zero n' = not_zero n'0).
      {
        clear Hexec1 IHHexec1 Hexec2.
        unfold seq_same_obs in Hseq_same.
        specialize (Hseq_same ([OBranch (not_zero n')]) ([OBranch (not_zero n'0)])).
        edestruct Hseq_same.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Branch. 1,2: eassumption. reflexivity.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Branch. 1,2: eassumption. reflexivity.
        - destruct H1 as [? H1]. now inv H1.
        - destruct H1 as [? H1]. now inv H1.
      }
      rewrite H1 in *. clear H1.
      destruct (Bool.eqb (not_zero n'0) b').
    * cbn in *. 
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      repeat eexists.
      1,2: change (DBranch b' :: ds2) with ([DBranch b'] ++ ds2). 
      1: change (OBranch (not_zero n'0) :: os0) with ([OBranch (not_zero n'0)] ++ os0).
      2: change (OBranch (not_zero n'0) :: os3) with ([OBranch (not_zero n'0)] ++ os3).
      1,2: econstructor 2; eassumption.
      destruct H3 as [H3 | H3].
      -- repeat destruct H3 as [-> H3]. left. repeat split; try reflexivity; apply H3.
      -- right. repeat destruct H3 as [? H3]. subst.
         repeat eexists. 2: exact H3.
         simpl. f_equal. assumption.
    * repeat eexists. 1, 2: econstructor.
      right. repeat eexists.
      right.
      repeat eexists. all: eassumption.
    + rewrite H9 in H18. inv H18.
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
    * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change os0 with ([] ++ os0).
      2: change os3 with ([] ++ os3).
      all: econstructor; eassumption.
    * repeat eexists. 3: right; eassumption.
      all: change x7 with ([] ++ x7). 
      1: change x8 with ([] ++ x8).
      2: change x9 with ([] ++ x9).
      all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change (OLoad n :: os0) with ([OLoad n] ++ os0).
      2: change (OLoad n0 :: os3) with ([OLoad n0] ++ os3).
      all: econstructor; eassumption.
    * repeat destruct H3 as [? H3]. subst. repeat eexists. 3: {
      right. do 3 eexists. repeat (match goal with | |- ?A /\ ?B => split end). 7: eassumption. 2, 3: rewrite app_comm_cons; reflexivity. all: try reflexivity. simpl. f_equal. assumption.
    }
      all: change x9 with ([] ++ x9). 
      1: change (OLoad n :: x10) with ([OLoad n] ++ x10).
      2: change (OLoad n0 :: x11) with ([OLoad n0] ++ x11).
      all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
    * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change (OStore n :: os0) with ([OStore n] ++ os0).
      2: change (OStore n0 :: os3) with ([OStore n0] ++ os3).
      all: econstructor; eassumption.
    * repeat destruct H3 as [? H3]. subst. repeat eexists. 3: {
      right. do 3 eexists. repeat (match goal with |- ?A /\ ?B => split end). 7: eassumption. 2, 3: rewrite app_comm_cons; reflexivity.
      all: try reflexivity.
      simpl. f_equal. assumption.
    }
      all: change x7 with ([] ++ x7). 
      1: change (OStore n :: x8) with ([OStore n] ++ x8).
      2: change (OStore n0 :: x9) with ([OStore n0] ++ x9).
      all: econstructor; eassumption.
    + (* Call case *)
      inv x. rewrite H20 in H6. inv H6.
      assert (l = l0).
      {
        clear Hexec1 IHHexec1 Hexec2.
        unfold seq_same_obs in Hseq_same.
        specialize (Hseq_same ([OCall l]) ([OCall l0])).
        edestruct Hseq_same.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Call. all: eassumption.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Call. all: eassumption.
        - destruct H1 as [? H1]. now inv H1.
        - destruct H1 as [? H1]. now inv H1.
      }
      rewrite <- H1 in *.
      destruct (fst pc' =? l)%nat.
    * cbn in *.
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      repeat eexists.
      1,2: change (DCall pc' :: ds2) with ([DCall pc'] ++ ds2). 
      1: change (OCall l :: os0) with ([OCall l] ++ os0).
      2: change (OCall l :: os3) with ([OCall l] ++ os3).
      1,2: econstructor 2. 2: exact H2. 1: exact H. 2: exact H3. 1: exact H0.
      destruct H4 as [H4 | H4].
      -- repeat destruct H4 as [-> H4]. left. repeat split ; try reflexivity;  apply H4.
      -- right. repeat destruct H4 as [? H4]. subst.
         repeat eexists. 2: exact H4.
         simpl. f_equal. assumption. 
    * repeat eexists. 1, 2: econstructor.
      right. repeat eexists. right.
      repeat eexists. all: eassumption.
    + (* Call case, only one fault *)
      inv x. apply H25 in H12 as [H12 | H12].
      all: congruence.
    + (* Call case, only one fault *)
      inv x. apply H11 in H23 as [H23 | H23].
      all: congruence.
    + (* Call case - both fault *)
      repeat eexists. 1, 2: constructor.
      right. repeat eexists.
      left.
      inv Hexec1. 2: inv H1.
      inv Hexec2. 2: inv H1.
      repeat split; try reflexivity. 1: assumption.
      inv x. assumption.
    + (* ret case (non-term) *)
      inv H14.
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
    * repeat destruct H3 as [-> H3].
      repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
      all: change ds2 with ([] ++ ds2). 
      1: change os0 with ([] ++ os0).
      2: change os3 with ([] ++ os3).
      all: econstructor; eassumption.
    * repeat eexists. 3: right; eassumption.
      all: change x7 with ([] ++ x7).  (* TODO: this is very fragile. it would be much better to have a consistent name for these *)
      1: change x8 with ([] ++ x8).
      2: change x9 with ([] ++ x9).
      all: econstructor; eassumption.
    + (* ret case (term) *)
      repeat eexists.
      1, 2: econstructor.
      left. inv Hexec1. 2: inv H1. (* S_Term can't step *)
      inv Hexec2. 2: inv H2.
      repeat split; try reflexivity. all: right; split; [reflexivity |].
      all: assumption.
Qed.

Lemma prefix_eq_length_eq {A} {os1 os2 : list A}:
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1 ->
  Datatypes.length os1 = Datatypes.length os2 ->
  os1 = os2.
Proof.
  intros [H | H].
  - intro Hlen. destruct H.
    apply (f_equal (@Datatypes.length _)) in H as H'.
    rewrite length_app in H'.
    assert (Datatypes.length x = 0) by lia.
    destruct x; [|cbn in H0; lia].
    now rewrite app_nil_r in H.
  - intro Hlen. destruct H.
    apply (f_equal (@Datatypes.length _)) in H as H'.
    rewrite length_app in H'.
    assert (Datatypes.length x = 0) by lia.
    destruct x; [|cbn in H0; lia].
    now rewrite app_nil_r in H.
Qed.

Lemma ideal_misspec_unwinding {p pc r1 r2 m1 m2 stk ds os1 os2 c1 c2}:
  p |- <(( S_Running (pc, r1, m1, stk, true) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, true) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1.
Proof.
  intros Hexec1 Hexec2.
  dependent induction Hexec1 generalizing pc r1 r2 m1 m2 stk os2; dependent destruction Hexec2.
  - left. exists []. reflexivity.
  - left. exists (os1 ++ os2). reflexivity.
  - right. exists (os1 ++ os0). reflexivity.
  - inv H; inv H0; try congruence; cbn in *; subst.
    + eapply IHHexec1; try eassumption. reflexivity.
    + eapply IHHexec1; try eassumption. reflexivity.
    + inv x. rewrite H6 in H5; inv H5. inv H10. inv  H11.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. destruct H. exists x. cbn. f_equal. assumption.  
      * right. destruct H. exists x. cbn. f_equal. assumption.  
    + eapply IHHexec1; try eassumption. rewrite H9 in H8. inv H8. reflexivity.
    + rewrite H9 in H8. inv H8. inv H11. inv H13.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. destruct H. exists x. cbn. f_equal. assumption.
      * right. destruct H. exists x. cbn. f_equal. assumption.
    + rewrite H9 in H8. inv H8. inv H11. inv H12.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. destruct H. exists x. cbn. f_equal. assumption.
      * right. destruct H. exists x. cbn. f_equal. assumption.
    + inv x. rewrite H6 in H5. inv H5. inv H7. inv H8.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. destruct H. exists x. cbn. f_equal. assumption.
      * right. destruct H. exists x. cbn. f_equal. assumption.
    + inv H7. inv H11. inv Hexec2.
      * right. exists os0. reflexivity.
      * inv H.
    + inv H6. inv H10. inv Hexec1.
      * left. exists os3. reflexivity.
      * inv H.
    + inv Hexec1. 2: inv H.
      inv Hexec2. 2: inv H.
      inv H12. inv H10.
      left. exists []. reflexivity.
    + eapply IHHexec1; try eassumption. reflexivity.
    + inv Hexec2. 2: inv H.
      right. exists os0. reflexivity.
Qed.

Lemma ideal_eval_relative_secure: forall p pc r1 r2 m1 m2 stk,
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  ideal_same_obs p pc r1 r2 m1 m2 stk.
Proof.
  unfold ideal_same_obs. intros p pc r1 r2 m1 m2 stk Hsso ds os1 os2 c1 c2 Hexec1 Hexec2.
  pose proof (ideal_eval_multi_exec_split Hsso Hexec1 Hexec2) as (pc1' & pc2' & r1' & r2' & m1' & m2' & stk1' & stk2' & ds' & os1' & os2' & Hns1 & Hns2 & Hsplit).
  clear Hexec1 Hexec2.
  destruct Hsplit.
  2: destruct H as (ds'' & os1'' & os2''& -> & -> & -> & -> & -> & Hobslen & H); destruct H.
  - repeat destruct H as [-> H].
    apply multi_ideal_nonspec_seq in Hns1, Hns2.
    eapply Hsso; eassumption.
  - destruct H as (-> & -> & Hf1 & Hf2).
    inv Hf1; inv Hf2. rewrite H6 in H9. inv H9.
    apply multi_ideal_nonspec_seq in Hns1, Hns2.
    eapply multi_seq_rcons in Hns1, Hns2.
    2, 3: econstructor; eassumption.
    eapply Hsso; eassumption.
  - destruct H as (pc'' & r1'' & r2'' & m1'' & m2'' & stk'' & d & ds''' & o1 & os1''' & o2 & os2''' & -> & -> & ->  & Hmp1 & Hspec1 & Hmp2 & Hspec2).
    apply prefix_eq_length_eq in Hobslen. 2: eapply Hsso; eapply multi_ideal_nonspec_seq; eassumption.
    subst.
    assert (o1 = o2) as ->.
    {
      eapply multi_ideal_nonspec_step_preserves_seq_same_obs in Hsso. 2-3: eassumption. 2: reflexivity.
      clear - Hsso Hmp1 Hmp2.
      inv Hmp1; inv Hmp2.
      - rewrite H5 in H6. inv H6.
        edestruct Hsso. 1, 2: econstructor 2; [|constructor].
        1, 2: eapply SSMI_Branch; try eassumption.
        1, 2: reflexivity.
        all: do 2 rewrite app_nil_r in H.
        all: destruct H.
        all: now inv H.
      - rewrite H7 in H6. inv H6.
        edestruct Hsso. 1, 2: econstructor 2; [|econstructor].
        1, 2: eapply SSMI_Call; try eassumption.
        all: do 2 rewrite app_nil_r in H.
        all: destruct H.
        all: now inv H.
    }
    edestruct (ideal_misspec_unwinding Hspec1 Hspec2).
    + left. destruct H. exists x. rewrite <- app_assoc. f_equal. cbn. f_equal. assumption.
    + right. destruct H. exists x. rewrite <- app_assoc. f_equal. cbn. f_equal. assumption.
Qed.

Lemma spec_eval_relative_secure_aux
  p pc r1 r2 m1 m2 stk ic1 ic2
  (ICFG1: ic1 = (pc, r1, m1, stk, false))
  (ICFG2: ic2 = (pc, r2, m2, stk, false))
  (SEQ: seq_same_obs p pc r1 r2 m1 m2 stk)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  pc' r1' r2' m1' m2' stk' sc1 sc2 b
  (SCFG1: sc1 = (pc', r1', m1', stk', b, false))
  (SCFG2: sc2 = (pc', r2', m2', stk', b, false))
  (LK1: msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0))
  (LK2: msf_lookup_sc sc2 = N (if (ms_true_sc sc2) then 1 else 0))
  (MATCH1: match_cfgs p ic1 sc1)
  (MATCH2: match_cfgs p ic2 sc2)
  ds os1 os2 n m c1 c2
  (* (WFDS: wf_ds' (uslh_prog p) ds) *)
  (SSTEP1: (uslh_prog p) |- <(( S_Running sc1 ))> -->*_ds^^os1^^n <(( c1 ))>)
  (SSTEP2: (uslh_prog p) |- <(( S_Running sc2 ))> -->*_ds^^ os2^^m <(( c2 ))>):
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).
Proof.
  eapply ultimate_slh_bcc in SSTEP1; eauto. des.
  eapply ultimate_slh_bcc in SSTEP2; eauto. des. subst.
  eapply ideal_eval_relative_secure; eauto.
Qed.

Lemma spec_eval_relative_secure_init_aux
  p r1 r2 m1 m2
  (FST: first_blk_call p)
  (* (ICFG1: c1 = ((0,0), r1, m1, @nil cptr)) *)
  (* (ICFG2: c2 = ((0,0), r2, m2, @nil cptr)) *)
  (SEQ: seq_same_obs p (0,0) r1 r2 m1 m2 [])
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  r1' r2' sc1 sc2
  (SCFG1: sc1 = ((0,0), r1', m1, [], true, false))
  (SCFG2: sc2 = ((0,0), r2', m2, [], true, false))
  (INIT1: r1' ! callee = FP 0)
  (INIT2: r2' ! callee = FP 0)
  (MATCH1: Rsync r1 r1' false)
  (MATCH2: Rsync r2 r2' false)
  ds os1 os2 n m sc1' sc2'
  (* (WFDS: wf_ds' (uslh_prog p) ds) *)
  (SSTEP1: (uslh_prog p) |- <(( S_Running sc1 ))> -->*_ds^^os1^^n <(( sc1' ))>)
  (SSTEP2: (uslh_prog p) |- <(( S_Running sc2 ))> -->*_ds^^ os2^^m <(( sc2' ))>):
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).
Proof.
  eapply ultimate_slh_bcc_init in SSTEP1; eauto. des.
  eapply ultimate_slh_bcc_init in SSTEP2; eauto. des. subst.
  eapply ideal_eval_relative_secure; eauto.
Qed.

Lemma spec_eval_relative_secure
  p r1 r2 r1' r2' m1 m2
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (CALLEE1: r1' ! callee = FP 0)
  (CALLEE2: r2' ! callee = FP 0)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p) : 
  relative_secure p (uslh_prog) r1 r2 r1' r2' m1 m2.
Proof.
  red. ii. eapply spec_eval_relative_secure_init_aux.
  11:{ eapply H0. }
  11:{ eapply H1. }
  all: eauto.
Qed.

