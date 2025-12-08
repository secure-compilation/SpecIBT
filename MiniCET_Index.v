(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
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
From SECF Require Import Maps MapsFunctor.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

Module MCC := MiniCETCommon(TotalMap).
Import MCC.
Import FunctionalExtensionality.


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
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
  p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_CTarget_F : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Fault ))>
  | SpecSMI_Ret : forall pc r m sk pc' ms,
  p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc', r, m, sk), false, ms) ))>
  | SpecSMI_Term : forall pc r m ms,
      p[[pc]] = Some <{{ ret }}> -> 
      p |- <(( S_Running ((pc, r, m, []), false, ms) ))> -->_[]^^[] <(( S_Term ))>

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
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      n' = (if ms then 0 else n) -> (* uslh masking *)
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
  | ISMI_Call : forall pc pc' r m sk e l l' (ms ms' : bool) blk,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      l' = (if ms then 0 else l) -> (* uslh masking *)
      ms' = ms || negb (fst pc' =? l) ->
      nth_error p (fst pc') = Some blk -> (* always established by well-formed directive *)
      snd blk = true ->
      snd pc' = 0 ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l'] <(( S_Running ((pc', r, m, (pc+1)::sk), ms') ))>
  (* fault if attacker pc goes to non-proc block or into the middle of any block *)
  (* directives are always "well-formed": nth_error p (fst pc') = Some blk /\ nth_error blk (snd pc') = Some i always established. *)
  | ISMI_Call_F : forall pc pc' r m sk e l l' (ms ms' : bool),
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      l' = (if ms then 0 else l) -> (* uslh masking *)
      (forall blk, nth_error p (fst pc') = Some blk -> snd blk = false \/ snd pc' <> 0) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l'] <(( S_Fault ))>
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
  - unfold TotalMap.t_apply, TotalMap.t_update, t_update. 
    rewrite <- String.eqb_neq, String.eqb_sym in H.
    rewrite H; auto.
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

(* How many steps does it take for target program to reach the program point the source reaches in one step? *)
Definition steps_to_sync_point (tp: prog) (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
  (* check pc is well-formed *)
  match nth_error tp (fst pc) with
  | Some blk => match nth_error (fst blk) (snd pc) with
               | Some i =>
                   match i with
                   | <{{x := _}}> => match (String.eqb x callee) with
                                    | true => match tp[[pc+1]] with
                                             | Some i => match i with
                                                        | <{{call _}}> => match ds with
                                                                         | [DCall lo] => (* decorated call with correct directive *)
                                                                             let '(l, o) := lo in
                                                                             (* check attacker pc is well-formed *)
                                                                             match nth_error tp l with
                                                                             | Some blk =>
                                                                                 match nth_error (fst blk) o with
                                                                                 | Some i =>
                                                                                     (* 4 steps if procedure block, fault otherwise *)
                                                                                     if (Bool.eqb (snd blk) true) && (o =? 0) then Some 4 else None
                                                                                 | _ => None
                                                                                 end
                                                                             | _ => None
                                                                             end
                                                                         | _ => None (* incorrect directive for call *)
                                                                         end
                                                        | _ => None (* callee assignment preceding any instruction other than call is ill-formed *)
                                                        end
                                             | None => None (* callee assignment as last instruction in block is ill-formed *)
                                             end
                                    | false => match (String.eqb x msf) with
                                              | true => None (* target starting pc is never going to point to msf assignment *)
                                              | false => Some 1 (* assignment statements that existed in src program *)
                                              end
                                    end
                   | <{{ branch _ to _ }}> => (* branch decorations all come after the instruction itself, so this is the sync point *)
                       match ds with
                       | [DBranch b] => Some (if b then 3 else 2)
                       | _ => None
                       end
                   | _ => Some 1 (* branch and call are the only instructions that add extra decorations *)
                   end
               | _ => None
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
  | DBranch b, Some (IBranch e l) => is_some p[[(l, 0)]] = true
  | DCall pc', Some (ICall e) => is_some p[[pc']] = true
  | _, _ => False
  end.

Definition wf_ds (p: prog) (pc: cptr) (ds: dirs) : Prop :=
  Forall (wf_dir p pc) ds.

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

Definition wf_uslh (p: prog) : Prop :=
  wf_prog p -> wf_prog (uslh_prog p).

(* Tactics *)

From SECF Require Import sflib.

(* using this *)
Lemma rev_fetch : forall (p: prog) (pc: cptr) (blk: list inst * bool) (i: inst),
  nth_error p (fst pc) = Some blk ->
  nth_error (fst blk) (snd pc) = Some i ->
  p[[pc]] = Some i.
Proof.
  intros. destruct pc as (l & o) eqn:Hpc.
  destruct (nth_error p (fst pc)) eqn:Hblk.
  - unfold fetch. simpl in H, H0. rewrite H. simpl in *. assumption.
  - rewrite Hpc in *. simpl in *. rewrite H in Hblk. discriminate.
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
  { assert (i <> i0). { unfold not; intros. unfold is_terminator in *. destruct i eqn:Hi; destruct i0 eqn:Hi0; clarify. }
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

Definition _branch_in_block (blk: list inst) : nat :=
  fold_left (fun acc i => match i with
                       | IBranch _ _ => add acc 1
                       | _ => acc
                       end) blk 0.

Definition branch_in_block (bb: list inst * bool) : nat :=
  _branch_in_block (fst bb).

Definition branch_in_prog_before (p: prog) (l: nat) : nat :=
  fold_left (fun acc b => add acc (branch_in_block b)) (firstn l p) 0.

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
| uslh_branch e e' l l'
  (COND: e' = <{{ (msf = 1) ? 0 : e }}>)
  (LB: match_branch_target p pc = Some l') :
  match_inst_uslh p pc (IBranch e l) (IBranch e' l')
| uslh_call e e'
  (CALL: e' = <{{ (msf = 1) ? & 0 : e }}>) :
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

Lemma bind_inv {A B} m (f: A -> M B) c res np
    (BIND: bind m f c = (res, np)) :
  exists a pm rf pf,
    m c = (a, pm)
  /\ f a (c + Datatypes.length pm) = (rf, pf)
  /\ res = rf
  /\ np = pm ++ pf.
Proof.
  unfold bind, monadUSLH, uslh_bind in BIND.
  destruct (m c) eqn:MC.
  destruct (f a (c + Datatypes.length p)) eqn:FAC. clarify. esplits; eauto.
  eapply tr_app_correct.
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

(* Lemma uslh_blk_branch_counter *)
(*     b blk is_proc o e l c blk' is_proc' np_blk' e' l' *)
(*     (SRC: nth_error blk o = Some (IBranch e l)) *)
(*     (TRB: uslh_blk (b, (blk, is_proc)) c = (blk', is_proc', np_blk')) *)
(*     (EE': e' = <{{ (msf = 1) ? 0 : e }}>) *)
(*     (TGT: nth_error blk' (o + blk_offset (blk, is_proc) o) = Some (IBranch e' l')) : *)
(*   l' = c + offset_branch_before (blk, is_proc) o. *)
(* Proof. *)
(*   unfold uslh_blk in TRB. *)
(*   exploit bind_inv; eauto. intros (blk'' & np_blk'' & rf & pf & TRIS & DECO). *)
(*   des. subst. *)
(*   unfold concatM in TRIS. *)
(*   exploit bind_inv; eauto. intros (blk''' & np_blk''' & flat_blk''' & pf' & TRIS' & DECO'). *)
(*   des; subst. simpl in DECO'. unfold MiniCET.uslh_ret in DECO'. clarify. *)

(*   exploit mapM_nth_error_strong; try eapply SRC; eauto. *)
(*   intros (brs & c' & np' & TGT' & TRIS'' & CNT'). *)

(*   rename l' into ll'. *)
(*   assert (TGT'': nth_error blk' (o + blk_offset (blk, is_proc) o) = Some <{{ branch ((msf = 1) ? 0 : e) to c'}}>). *)
(*   { eapply bind_inv in TRIS''. des. subst. *)
(*     simpl in TRIS''0. unfold MiniCET.uslh_ret in TRIS''0. clarify. *)
(*     clear - TGT TRIS' TGT'. *)
(*     exploit mapM_nth_error_strong; try eapply TRIS'; eauto. i. des. *)
(*     ss. unfold MiniCET.uslh_ret in *. ss. clarify. *)

(*   replace (o + blk_offset (blk, is_proc) o) with (prefix_offset a o 0 + (if Bool.eqb is_proc true then 2 else 0)); auto. *)
(*   2:{ destruct is_proc; ss. *)
(*       - unfold blk_offset. ss. unfold prefix_offset. *)
(*         erewrite <- fold_left_add_init. rewrite add_0_l. *)
(*         eapply offset_eq_aux; eauto. *)
(*         exploit mapM_perserve_len; eauto. i. rewrite x2. *)
(*         eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. *)
(*       - rewrite add_0_r. *)
(*         unfold blk_offset. ss. eapply offset_eq_aux; eauto. *)
(*         exploit mapM_perserve_len; eauto. i. rewrite x2. *)
(*         eapply lt_le_incl. rewrite <- nth_error_Some. ii. clarify. } *)

(*   unfold uslh_inst in TRIS''. exploit bind_inv; eauto. i. des; subst. *)
(*   simpl in x1. unfold MiniCET.uslh_ret in x1. clarify. *)
(*   eapp *)
  
(*   exploit bind_inv. *)
(*   { eapply TRIS''. } *)
(*   i. des. subst. simpl in x2. unfold MiniCET.uslh_ret in x2. clarify. *)
(*   ss. *)
(*   simpl in TRIS''. *)
(* Admitted. *)

Lemma branch_target_matches p tp pc tpc e e' l l'
    (TRP: uslh_prog p = tp)
    (PS: pc_sync p pc = Some tpc)
    (SRC: p[[pc]] = Some <{{ branch e to l }}>)
    (TGT: tp[[tpc]] = Some <{{ branch e' to l' }}>) :
  match_branch_target p pc = Some l'.
Proof.
  unfold uslh_prog in TRP.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn:Huslh.
  exploit mapM_perserve_len; eauto. intros LEN.

  destruct pc as [b o]. ss.
  unfold pc_sync in PS. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.
  replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss.
  des_ifs_safe.  destruct p0 as [blk' is_proc']. ss.
  replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk)
             (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) in TGT by ss.

  exploit mapM_nth_error_strong; eauto.
  { instantiate (2:= b). instantiate (1:= (b, (blk, is_proc))).
    eapply nth_error_add_index. auto. }
  intros (blk'' & c' & np_blk' & TNTH & TBLK & C').

  assert (is_proc = is_proc').
  { admit. }

  assert (blk'' = (blk', is_proc')).
  { admit. }

  assert (c' = Datatypes.length p + branch_in_prog_before p b).
  { subst. f_equal. unfold len_before, branch_in_prog_before. admit. }
  subst.

Admitted.

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
  destruct pc as [l o].
  unfold pc_sync in *. ss. des_ifs_safe.
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
    + econs 2; ss. des_ifs_safe. f_equal.
      do 2 rewrite <- add_assoc. rewrite add_cancel_l.

      assert (branch_in_prog_before p l = len_before uslh_blk (add_index p) l (Datatypes.length p)).
      { admit. }
      admit.

  (* call *)
  - admit.
  (* ctarget *)
  - exists <{{ ctarget }}>. split;
    destruct blk' as [blk' prc_bool]; unfold no_ct_prog in NCT;
      destruct (split p) as (bs & bools) eqn:Hsplitp;
      rewrite Forall_forall in NCT; unfold blk_offset; simpl;
      specialize (nth_error_In p l Heq); intros;
      eapply in_split_l in H; rewrite Hsplitp in H; simpl in H;
      apply NCT in H; unfold no_ct_blk in H; rewrite Forall_forall in H;
      specialize (nth_error_In blk o Heq0); intros; apply H in H0;
      destruct H0.
Admitted.

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

(* BCC lemma for one single instruction *)
Lemma ultimate_slh_bcc_single_cycle (p: prog) : forall ic1 sc1 sc2 n ds os,
  no_ct_prog p ->
  wf_prog p ->
  (* wf_ds p (get_pc_sc sc1) ds -> *)
  wf_ds p (get_pc_ic ic1) ds ->
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0) ->
  steps_to_sync_point (uslh_prog p) sc1 ds = Some n ->
  spec_cfg_sync p ic1 = Some sc1 ->
  uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( S_Running sc2 ))> ->
      exists ic2, p |- <(( S_Running ic1 ))> -->i_ ds ^^ os <(( S_Running ic2 ))> 
                  /\ match_cfgs p ic2 sc2.
Proof.
  intros until os. intros nct wfp wfds unused_p_msf unused_p_callee ms_msf n_steps cfg_sync tgt_steps.
  destruct ic1 as (c & ms). destruct c as (c & sk). destruct c as (c & m). destruct c as (ipc & r).
  unfold wf_prog in wfp. destruct wfp. unfold nonempty_program in H.
  unfold wf_ds in wfds. simpl in ms_msf.
  destruct ipc as (l & o) eqn:Hipc.
  destruct (nth_error p l) as [iblk|] eqn:Hfst.
  - (* Some blk *)
    destruct (nth_error (fst iblk) o) as [i|] eqn:Hsnd.
    + (* Some i *)
      (* get fetch back into ctx, since it's premise for ideal step *)
      replace l with (fst ipc) in Hfst by (rewrite Hipc; auto).
      replace o with (snd ipc) in Hsnd by (rewrite Hipc; auto).
      specialize (rev_fetch p ipc iblk i Hfst Hsnd); intros. simpl in *.
      
      (* find starting spec cfg, it's used in calculating number of spec steps *)
      destruct (pc_sync p (l, o)) as [spc|] eqn:Hpcsync; try discriminate.
      destruct (map_opt (pc_sync p) sk) as [ssk|] eqn:Hsk; try discriminate.
      injection cfg_sync; intros. rewrite <- H2 in n_steps.

      (* determine spec pc in-bounds, get all relevant premises in ctx *)
      destruct spc as (sl, so) eqn:Hspc. simpl in n_steps.
      destruct (nth_error (uslh_prog p) sl) eqn:Hsfst; try discriminate. rename p0 into sblk.
      destruct (nth_error (fst sblk) so) eqn:Hssnd; try discriminate. rename i0 into si.
      replace sl with (fst spc) in Hsfst by (rewrite Hspc; auto).
      replace so with (snd spc) in Hssnd by (rewrite Hspc; auto).
      specialize (rev_fetch (uslh_prog p) spc sblk si Hsfst Hssnd); intros.

      (* relate the two pcs (we know labels are the same in all cases except branch; 
         will also depend on proc block and whether offset is 0) *)
      (*unfold pc_sync in Hpcsync. simpl in Hpcsync.
         rewrite Hipc in Hfst, Hsnd. simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in *.*)

      (* put program in form where we can access block 0 and rest *)
      destruct p as [|b bs] eqn:Hp. { simpl in *. inv H. } (*simpl in *.*) 
      destruct i.
      { (* skip *) 
        apply src_skip_inv with (tp:=(uslh_prog p)) (tpc:=spc) in H1; clarify.
        clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inv tgt_steps. exists (l, (add o 1), r, m, sk, ms). 
        assert (ds = [] /\ os = []).
        { inv H8. inv H7; clarify. ss. rewrite app_nil_r in H1, H2. auto. }
        des; subst. simpl in H1, H2. eapply app_eq_nil in H1, H2. des; subst.
        split.
        - econs. unfold fetch. cbn. replace (fst (l, o)) with l in Hfst by auto.
          rewrite Hfst. assumption.
        - inv H8. inv H7; clarify.
          econs; eauto.
          { unfold pc_sync. cbn. replace (fst (l, o)) with l in Hfst by auto. rewrite Hfst. 
            assert (exists i', (nth_error (fst iblk) (add o 1)) = Some i').
            { apply block_always_terminator with (p:=(b :: bs)) (i:=<{{ skip }}>); clarify.
              rewrite Forall_forall in H0. specialize (H0 iblk). 
              specialize (nth_error_In (b :: bs) l Hfst); intros.
              apply H0 in H1. assumption.
            }
            destruct H1 as (i' & H1). rewrite H1.
            assert (forall n, (add n 1) = S n). { lia. }
            specialize (H4 o). rewrite H4. replace (snd (l, o)) with o in Hsnd by auto.
            specialize (firstnth_error (fst iblk) o <{{ skip }}> Hsnd) as ->.
            rewrite fold_left_app. cbn. 
            unfold pc_sync in Hpcsync. replace (fst (l, o)) with l in Hpcsync by auto. rewrite Hfst in Hpcsync.
            replace (snd (l, o)) with o in Hpcsync by auto. rewrite Hsnd in Hpcsync. injection Hpcsync; intros.
            rewrite H6. unfold cptr. repeat f_equal. rewrite H5. 
            lia.
          }
          { econs; eauto. intros. destruct H2. unfold TotalMap.t_apply, r_sync. rewrite t_update_neq; auto.
            destruct H1. rewrite <- String.eqb_neq in H1. rewrite String.eqb_sym in H1. rewrite String.eqb_neq in H1.
            assumption.
          }
      }
      { (* x := e *) 
        apply src_simple_inv with (tp:=(uslh_prog p)) (tpc:=spc) in H1; clarify.
        clear cfg_sync.
        destruct si;
        try (destruct H1 as (i' & H1); destruct H1 as (Hsome & Hmatch);
        rewrite H3 in Hsome; injection Hsome; intros; rewrite <- H1 in *; inv Hmatch).
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.

        unfold unused_prog in unused_p_callee. destruct (split (b :: bs)) as (blks, bools) eqn:Hsplit.
        rewrite Forall_forall in unused_p_callee. replace (fst (l, o)) with l in Hfst by auto. 
        specialize (nth_error_In (b :: bs) l Hfst); intros. 
        apply in_split_l in H1. rewrite Hsplit in H1. simpl in H1. apply unused_p_callee in H1.
        unfold b_unused in H1. rewrite Forall_forall in H1.
        replace (snd (l, o)) with o in Hsnd by auto.
        specialize (nth_error_In (fst iblk) o Hsnd); intros.
        apply H1 in H2. simpl in H2. destruct H2.
        rewrite <- String.eqb_neq in H2. 
        assert (callee = "callee"). { auto. }
        rewrite <- H5 in H2. rewrite H2 in n_steps.
        
        unfold unused_prog in unused_p_msf. rewrite Hsplit in unused_p_msf. 
        rewrite Forall_forall in unused_p_msf. 
        specialize (nth_error_In (b :: bs) l Hfst); intros.
        apply in_split_l in H6. rewrite Hsplit in H6. simpl in H6. apply unused_p_msf in H6.
        unfold b_unused in H6. rewrite Forall_forall in H6.
        specialize (nth_error_In (fst iblk) o Hsnd); intros.
        apply H6 in H7. simpl in H7. destruct H7. 
        rewrite <- String.eqb_neq in H7.
        assert (msf = "msf"). { auto. }
        rewrite <- H9 in H7. rewrite H7 in n_steps. 
        
        injection n_steps; intros. rewrite <- H10 in *.
        inv tgt_steps. exists (l, (add o 1), x0 !-> (eval r e0); r, m, sk, ms).
        assert (ds = [] /\ os = []).
        { inv H17. inv H16; clarify. ss. rewrite app_nil_r in H11, H12. auto. }
        des; subst. simpl in H11, H12. eapply app_eq_nil in H11, H12. des; subst.
        split.
        - econs. unfold fetch. cbn. rewrite Hfst. assumption.
        - inv H17. inv H16; clarify. 
          econs; eauto.
          + unfold pc_sync. cbn. replace (fst (l, o)) with l in Hfst by auto. rewrite Hfst. 
            assert (exists i', (nth_error (fst iblk) (add o 1)) = Some i').
            { apply block_always_terminator with (p:=(b :: bs)) (i:=<{{ x0 := e0 }}>); clarify.
              rewrite Forall_forall in H0. specialize (nth_error_In (b :: bs) l Hfst); intros.
              apply H0 in H3. assumption.
            }
            destruct H3 as (i' & H3). rewrite H3.
            assert (forall n, (add n 1) = S n). { lia. }
            specialize (H10 o). rewrite H10. replace (snd (l, o)) with o in Hsnd by auto.
            specialize (firstnth_error (fst iblk) o <{{ x0 := e0 }}> Hsnd) as ->.
            rewrite fold_left_app. cbn. 
            unfold pc_sync in Hpcsync. replace (fst (l, o)) with l in Hpcsync by auto. rewrite Hfst in Hpcsync.
            replace (snd (l, o)) with o in Hpcsync by auto. rewrite Hsnd in Hpcsync. injection Hpcsync; intros.
            rewrite H13. unfold cptr. repeat f_equal. rewrite H12. 
            lia.
          + econs.
            { intros. destruct H3. unfold TotalMap.t_apply, TotalMap.t_update, t_update, r_sync.
              rewrite <- H9 in H8. apply eval_unused_update with (r:=r) (v:=(N (if ms then 1 else 0))) in H8.
              rewrite H8. des_ifs; rewrite t_update_neq; auto.
            }
            { unfold TotalMap.t_apply, TotalMap.t_update, t_update. rewrite H7. 
              unfold r_sync, TotalMap.t_update, t_update. auto.
            }
      }
      { (* branch *)
        unfold pc_sync in Hpcsync. simpl in Hpcsync. rewrite Hipc in *.
        simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in Hpcsync. injection Hpcsync; intros. clear Hpcsync.
        rewrite <- H5, <- H4 in *. 
        injection cfg_sync; intros. rewrite <- H6 in *. clear H6. clear cfg_sync. clear H2.
        apply src_inv with (tp:=(uslh_prog (b :: bs))) (tpc:=spc) in H1; auto; cycle 1.
        { rewrite Hspc. unfold pc_sync. simpl. rewrite Hfst, Hsnd. auto. }
        destruct H1 as (i' & H1). destruct H1 as (Hsome & Hmatch). 
        rewrite H3 in Hsome. injection Hsome; intros. rewrite H1 in *. clear H1. clear Hsome.
        unfold wf_dir in wfds. simpl in wfds. rewrite Hfst, Hsnd in wfds.
        inv Hmatch; clarify. unfold match_branch_target in LB. rewrite Hfst in LB. injection LB; intros.
        rewrite <- H1 in *. clear H1. clear LB. 
        specialize (rev_fetch (b :: bs) (sl, o) iblk <{{ branch e to l0 }}> Hfst Hsnd); intros.
        remember (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc) as f.
        remember (o + fold_left f (firstn o (fst iblk)) (if Bool.eqb (snd iblk) true then 2 else 0)) as so.
        unfold wf_dir in wfds.
        simpl in ms_msf, Hsfst, Hssnd, Hfst, Hsnd.
        rename H3 into tgt_fetch. rename H1 into src_fetch. 
        inv tgt_steps; clarify. 
        unfold wf_block in H0. rewrite Forall_forall in H0.
        specialize (nth_error_In (b :: bs) sl Hfst); intros. 
        apply H0 in H3. destruct H3, H4. rewrite Forall_forall in H5. 
        specialize (H5 <{{ branch e to l0 }}>). 
        specialize (nth_error_In (fst iblk) o Hsnd); intros. 
        apply H5 in H6. unfold wf_instr in H6. unfold wf_lbl in H6. 
        destruct H6. 
        destruct (nth_error (b :: bs) l0) eqn:Hlbl; clarify. rename p into br_blk. 
        destruct br_blk as (br_insts & br_bool) eqn:Hbr_blk. 
        simpl in wfds. specialize (nth_error_In (b :: bs) l0 Hlbl); intros.
        apply H0 in H8. destruct H8, H9. apply blk_not_empty_list in H8. simpl in H8.
        destruct br_insts eqn:Hbri; clarify. simpl in wfds. rewrite Forall_forall in wfds.
        rename l into rest.
        destruct ms.
        { (* speculating *) 
          admit.
        }
        { (* not speculating *)
          admit.
        }
      }
      { (* jump *) 
        apply src_simple_inv with (tp:=(uslh_prog p)) (tpc:=spc) in H1; clarify.
        clear cfg_sync.
        destruct si;
        try (destruct H1 as (i' & H1); destruct H1 as (Hsome & Hmatch);
        rewrite H3 in Hsome; injection Hsome; intros; rewrite <- H1 in *; inv Hmatch).
        injection n_steps; intros. rewrite <- H1 in *.
        clear Hsome. clear n_steps.
        
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inv tgt_steps. exists (l1, 0, r, m, sk, ms).
        assert (ds = [] /\ os = []).
        { inv H9. inv H8; clarify. ss. rewrite app_nil_r in H2, H4. auto. } 
        des; subst. simpl in H2, H4. eapply app_eq_nil in H2, H4. des; subst.
        split.
        - econs. unfold fetch. cbn. replace (fst (l, o)) with l in Hfst by auto.
          rewrite Hfst. replace (snd (l, o)) with o in Hsnd by auto. assumption.
        - inv H9. inv H8; clarify.
          simpl. econs; clarify. 
          { unfold pc_sync. cbn. unfold wf_block in H0. rewrite Forall_forall in H0.
            replace (fst (l, o)) with l in Hfst by auto.
            specialize (nth_error_In (b :: bs) l Hfst); intros. 
            apply H0 in H1. destruct H1, H3. rewrite Forall_forall in H4. 
            specialize (H4 <{{ jump l1 }}>). replace (snd (l, o)) with o in Hsnd by auto.
            specialize (nth_error_In (fst iblk) o Hsnd); intros. 
            apply H4 in H5. unfold wf_instr in H5. unfold wf_lbl in H5. 
            destruct (nth_error (b :: bs) l1) eqn:Hlbl; clarify. rename p into jblk. 
            destruct jblk as (jinsts & jbool) eqn:Hjblk. cbn. rewrite <- H5 in *. cbn. 
            specialize (nth_error_In (b :: bs) l1 Hlbl); intros. apply H0 in H6. destruct H6, H7.
            specialize (blk_not_empty_list (jinsts, false) H6); intros. 
            simpl in H9. destruct jinsts; clarify.
          }
          { econs; clarify. intros. unfold r_sync, TotalMap.t_apply.
            destruct H2. rewrite t_update_neq; clarify. rewrite <- String.eqb_neq in *.
            destruct H1.
            rewrite String.eqb_sym in H1. auto.
          }
      }
      { (* load *) 
        unfold pc_sync in Hpcsync. simpl in Hpcsync. rewrite Hipc in Hfst, Hsnd. 
        simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in Hpcsync. injection Hpcsync; intros.
        injection cfg_sync; intros. rewrite <- H6 in *. clear H6. clear cfg_sync.
        clear Hpcsync. clear H2. 
        apply src_simple_inv with (tp:=(uslh_prog (b :: bs))) (tpc:=spc) in H1; clarify; cycle 1.
        { unfold pc_sync. simpl. rewrite Hfst, Hsnd. auto. }
        destruct H1 as (i' & H1). destruct H1 as (Hsome & Hmatch). 
        rewrite H3 in Hsome. injection Hsome; intros. rewrite H1 in *. inv Hmatch. clear Hsome.
        injection n_steps; intros. rewrite <- H1 in *. clear H1. clear n_steps.
        inv tgt_steps. inv H8. inv H2; clarify. cbn. simpl in ms_msf.
        simpl in H12.
        exists (((sl, o) + 1), x !-> v'; r, m, sk, ms). 
        specialize (rev_fetch (b :: bs) (sl, o) iblk <{{ x <- load[a] }}> Hfst Hsnd); intros.
        simpl in H12.
        split; econs; try econs; eauto.
        { rewrite <- H12. 
          destruct ms eqn:Hms.
          { (* ms = true *)
            rewrite Nat.eqb_refl in *. simpl. simpl in H12. injection H12; intros. 
            rewrite <- H2 in *. clear H12. clear H2. reflexivity.
          }
          { cbn. unfold r_sync. f_equal. unfold unused_prog in unused_p_msf. 
            destruct (split (b :: bs)) as (blks, bools) eqn:Hsplit. rewrite Forall_forall in unused_p_msf.
            specialize (nth_error_In (b :: bs) sl Hfst); intros.
            apply in_split_l in H2. rewrite Hsplit in H2. simpl in H2. apply unused_p_msf in H2.
            unfold b_unused in H2. rewrite Forall_forall in H2.
            specialize (nth_error_In (fst iblk) o Hsnd); intros.
            apply H2 in H3. inv H3. assert (msf = "msf"). { auto. }
            rewrite <- H3 in H5. apply eval_unused_update with (r:=r) (v:=(N 0)) in H5. 
            symmetry. assumption.
          }
        }
        { unfold pc_sync. cbn. rewrite Hfst. rewrite Forall_forall in H0. 
          specialize (nth_error_In (b :: bs) sl Hfst); intros.
          apply H0 in H2. 
          assert (~ (is_terminator <{{ x <- load[a] }}>)).
          { unfold not; intros. inv H3. }
          specialize (block_always_terminator (b :: bs) iblk o <{{ x <- load[a] }}> H2 Hsnd H3); intros.
          destruct H4 as (i' & H4). destruct (nth_error (fst iblk) (add o 1)); clarify.
          assert (forall n, (add n 1) = (S n)). { lia. }
          unfold cptr. remember (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc) as f.
          remember (if Bool.eqb (snd iblk) true then 2 else 0) as prc.
          rewrite H4. specialize (firstnth_error (fst iblk) o <{{ x <- load[a] }}> Hsnd); intros.
          rewrite H5. rewrite fold_left_app. simpl. do 2 f_equal. rewrite <- H4.
          do 2 f_equal. rewrite Heqf. cbn. reflexivity. 
        }
        (* Rsync *)
        { intros. unfold TotalMap.t_apply, r_sync, TotalMap.t_update, t_update.
          destruct H2. rewrite <- String.eqb_neq in H2. rewrite String.eqb_sym in H2. rewrite H2.
          reflexivity.
        }
        { unfold TotalMap.t_apply, r_sync, TotalMap.t_update, t_update. rewrite String.eqb_refl.
          unfold unused_prog in unused_p_msf. 
          destruct (split (b :: bs)) as (blks, bools) eqn:Hsplit. rewrite Forall_forall in unused_p_msf.
          specialize (nth_error_In (b :: bs) sl Hfst); intros.
          apply in_split_l in H2. rewrite Hsplit in H2. simpl in H2. apply unused_p_msf in H2.
          unfold b_unused in H2. rewrite Forall_forall in H2.
          specialize (nth_error_In (fst iblk) o Hsnd); intros.
          apply H2 in H3. inv H3. assert (msf = "msf"). { auto. }
          rewrite <- H3 in H4. rewrite <- String.eqb_neq in H4. rewrite H4.
          reflexivity.
        }
      }
      { (* store *) 
        unfold pc_sync in Hpcsync. simpl in Hpcsync. rewrite Hipc in Hfst, Hsnd. 
        simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in Hpcsync. injection Hpcsync; intros.
        injection cfg_sync; intros. rewrite <- H6 in *. clear H6. clear cfg_sync.
        clear Hpcsync. clear H2. 
        apply src_simple_inv with (tp:=(uslh_prog (b :: bs))) (tpc:=spc) in H1; clarify; cycle 1.
        { unfold pc_sync. simpl. rewrite Hfst, Hsnd. auto. }
        destruct H1 as (i' & H1). destruct H1 as (Hsome & Hmatch). 
        rewrite H3 in Hsome. injection Hsome; intros. rewrite H1 in *. inv Hmatch. clear Hsome.
        injection n_steps; intros. rewrite <- H1 in *. clear H1. clear n_steps.
        inv tgt_steps. inv H8. inv H2; clarify. cbn. simpl in ms_msf. simpl in H12. 
        exists (((sl, o) + 1), r, (upd n0 m (eval r e)), sk, ms).
        specialize (rev_fetch (b :: bs) (sl, o) iblk <{{ store[a] <- e }}> Hfst Hsnd); intros.
        split.
        { econs; eauto. rewrite <- H12. f_equal. 
          destruct ms eqn:Hms; clarify. cbn.
          unfold r_sync. unfold unused_prog in unused_p_msf. 
          destruct (split (b :: bs)) as (blks, bools) eqn:Hsplit. rewrite Forall_forall in unused_p_msf.
          specialize (nth_error_In (b :: bs) sl Hfst); intros.
          apply in_split_l in H2. rewrite Hsplit in H2. simpl in H2. apply unused_p_msf in H2.
          unfold b_unused in H2. rewrite Forall_forall in H2.
          specialize (nth_error_In (fst iblk) o Hsnd); intros.
          apply H2 in H3. inv H3. assert (msf = "msf"). { auto. }
          rewrite <- H3 in H4. apply eval_unused_update with (r:=r) (v:=(N 0)) in H4.
          rewrite H4. reflexivity.
        }
        { assert (eval (r_sync r ms) e = eval r e).
          { unfold TotalMap.t_apply, r_sync in ms_msf.  
            unfold r_sync. unfold unused_prog in unused_p_msf. 
            destruct (split (b :: bs)) as (blks, bools) eqn:Hsplit. rewrite Forall_forall in unused_p_msf.
            specialize (nth_error_In (b :: bs) sl Hfst); intros.
            apply in_split_l in H2. rewrite Hsplit in H2. simpl in H2. apply unused_p_msf in H2.
            unfold b_unused in H2. rewrite Forall_forall in H2.
            specialize (nth_error_In (fst iblk) o Hsnd); intros.
            apply H2 in H3. inv H3. assert (msf = "msf"). { auto. }
            rewrite <- H3 in H5. apply eval_unused_update with (r:=r) (v:=(N (if ms then 1 else 0))) in H5. 
            assumption.
          }
          rewrite H2. econs; eauto.
          { unfold pc_sync. cbn. rewrite Hfst. rewrite Forall_forall in H0. 
          specialize (nth_error_In (b :: bs) sl Hfst); intros.
          apply H0 in H3. 
          assert (~ (is_terminator <{{ store[a] <- e }}>)).
          { unfold not; intros. inv H4. }
          specialize (block_always_terminator (b :: bs) iblk o <{{ store[a] <- e }}> H3 Hsnd H4); intros.
          destruct H5 as (i' & H5). destruct (nth_error (fst iblk) (add o 1)); clarify.
          assert (forall n, (add n 1) = (S n)). { lia. }
          unfold cptr. remember (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc) as f.
          remember (if Bool.eqb (snd iblk) true then 2 else 0) as prc.
          rewrite H5. specialize (firstnth_error (fst iblk) o <{{ store[a] <- e }}> Hsnd); intros.
          rewrite H6. rewrite fold_left_app. simpl. do 2 f_equal. rewrite <- H5.
          do 2 f_equal. rewrite Heqf. cbn. reflexivity.
          }
          { econs; eauto.
            { intros. unfold TotalMap.t_apply, r_sync, TotalMap.t_update, t_update.
              destruct H3. rewrite <- String.eqb_neq in H3. rewrite String.eqb_sym in H3. rewrite H3.
              reflexivity.
            }
          }
        } 
      }
      { (* call *)  
        unfold pc_sync in Hpcsync. simpl in Hpcsync.
        rewrite Hipc in Hfst, Hsnd. simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in *.
        assert (si = <{{ callee := (msf=1) ? &0 : fp }}>). { admit. }
        rewrite H4 in *. cbn in n_steps.
        destruct (nth_error (fst sblk) (add so 1)) eqn:Hsblk; clarify.
        rewrite Forall_forall in wfds. admit.
      }
      { (* ctarget *) 
        unfold pc_sync in Hpcsync. simpl in Hpcsync.
        rewrite Hipc in Hfst, Hsnd. simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in *.
        unfold no_ct_prog in nct. destruct (split (b :: bs)) as (b_insts & b_bools) eqn:Hbb.
        rewrite Forall_forall in nct. specialize (split_combine (b :: bs) Hbb); intros.
        rewrite <- H4 in Hfst. specialize (nth_error_In (combine b_insts b_bools) l Hfst); intros.
        destruct iblk as (iinsts & ibool) eqn:Hiblk. specialize (in_combine_l b_insts b_bools iinsts ibool H5); intros.
        apply nct in H6. assert (iinsts = (fst iblk)). { rewrite Hiblk. simpl. auto. }
        rewrite H7 in H6. unfold no_ct_blk in H6. rewrite Forall_forall in H6. rewrite <- Hiblk in Hsnd.
        specialize (nth_error_In (fst iblk) o Hsnd); intros. apply H6 in H8. 
        unfold no_ct_inst in H8. destruct H8.
      }
      { (* ret *) assert (si = <{{ ret }}>). { admit. } 
        rewrite H4 in *. injection n_steps; intros. rewrite <- H5 in tgt_steps.
        rewrite <- H2 in *. clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inversion tgt_steps. destruct sk as [|pc' sk'] eqn:Hretsk.
        - admit. (* empty stack case: should end with S_Term *)
        - replace (l, o) with ipc by (rewrite <- Hipc; auto). 

          exists (pc', r, m, sk', ms). split.
          { assert (ds = [] /\ os = []).
            { inv H12. inv H11; clarify. ss. rewrite app_nil_r in H6, H7. auto. }
            destruct H13. rewrite H13, H14. econs. eauto.
          }
          { subst. inv H12. admit.

          }
      }
    + (* None *)
      simpl in cfg_sync. destruct (pc_sync p (l, o)) eqn:Hpcsync; try discriminate.
      destruct (map_opt (pc_sync p) sk) eqn:Hsksync; try discriminate. unfold pc_sync in Hpcsync.
      cbn in Hpcsync. destruct (nth_error p l) as [blk'|] eqn:Hfst'; try discriminate.
      injection Hfst; intros. rewrite H1 in *. clear Hfst. clear H1.
      destruct (nth_error (fst iblk) o) as [i'|] eqn:Hsnd'; discriminate.
  - (* None *)
    simpl in cfg_sync. simpl in cfg_sync. destruct (pc_sync p (l, o)) eqn:Hpcsync; try discriminate.
    destruct (map_opt (pc_sync p) sk) eqn:Hsksync; try discriminate. unfold pc_sync in Hpcsync.
    cbn in Hpcsync. destruct (nth_error p l) as [blk'|] eqn:Hfst'; discriminate.
Admitted.

(* End BCC. *)

(* Lemma ultimate_slh_bcc (p: prog) : forall sc1 tsc1 tsc2 n ds os,
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) ->
  tsc1 = spec_cfg_sync p sc1 ->
  uslh_prog p |- <(( S_Running tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( S_Running sc1 ))> -->i*_ ds ^^ os <(( sc2 ))> /\ tsc2 = spec_cfg_sync p sc2 /\ same_result_type sc2 tsc2.
Proof.
   Admitted. *)

 (** * Definition of Relative Secure *) 

 Definition seq_same_obs p pc r1 r2 m1 m2 stk : Prop := 
   forall os1 os2 c1 c2, 
     p |- <(( S_Running (pc, r1, m1, stk) ))> -->*^ os1 <(( c1 ))> -> 
     p |- <(( S_Running (pc, r2, m2, stk) ))> -->*^ os2 <(( c2 ))> -> 
     (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).  

 Definition spec_same_obs p pc r1 r2 m1 m2 stk : Prop := 
   forall ds n os1 os2 c1 c2, 
   p |- <(( S_Running (pc, r1, m1, stk, false, false) ))> -->*_ds^^os1^^n <(( c1 ))> -> 
   p |- <(( S_Running (pc, r2, m2, stk, false, false) ))> -->*_ds^^ os2^^n <(( c2 ))> ->
     os1 = os2.  

 Definition relative_secure (p:prog) (trans1 : prog -> prog)
   (r1 r2 : reg) (m1 m2 : mem): Prop := 
   seq_same_obs p (0,0) r1 r2 m1 m2 [] ->
   spec_same_obs (trans1 p) (0,0) r1 r2 m1 m2 []. 

 (** * Ultimate Speculative Load Hardening *) 


