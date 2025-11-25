(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils ListMaps.
From SECF Require Import MiniCET.
From SECF Require Import TestingLib.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import ExtLib.Data.Monads.OptionMonad.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)


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
  | multi_spec_inst_refl sc : p |- <(( sc ))> -->*_[]^^[]^^0 <(( sc ))>
  | multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>

  where "p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

(** Ideal small-step semantics for MiniCET *)

Definition ideal_cfg :=  (cfg * bool)%type.

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
  | ISMI_Load : forall pc r m sk x e n n' v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      n' = (if ms then 0 else n) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OLoad n'] <(( S_Running ((pc+1, (x !-> v'; r), m, sk), ms) ))>
  | ISMI_Store : forall pc r m sk e e' e'' n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      e'' = (if ms then 0 else n) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OStore e''] <(( S_Running ((pc+1, r, upd n m (eval r e'), sk), ms) ))>
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
  apply r msf.

Definition msf_lookup_ic (ic: ideal_cfg) : val :=
let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  apply r msf.

Definition callee_lookup_sc (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  apply r callee.

Definition callee_lookup_ic (ic: ideal_cfg) : val :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  apply r callee.

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
   (forall x, x <> msf /\ x <> callee -> apply sr x = apply tr x) /\ 
   (apply tr msf = N (if ms then 1 else 0)).

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

Import FunctionalExtensionality.

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
  intros.
  unfold uslh_prog.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn: Huslh.
  enough (length p' = length p).
  {
    rewrite tr_app_correct.
    rewrite length_app.
    lia.
  }
  (* The remaining proof is surprisingly ugly, as it depends on the interplay of mapT, combine, and uslh_bind. *)
  (* unfold mapM until we have the underlying List functions *)
  unfold mapM in Huslh. 
  unfold Traversable.sequence in Huslh.
  unfold Traversable.mapT in Huslh.
  cbn in Huslh.
  revert Huslh.
  generalize (Datatypes.length p) at 1 as len.
  (* need generalized version for induction *)
  unfold add_index. generalize 0 as n.
  revert p' newp.
  induction p.
  - intros p' newp n len [= ->]. reflexivity.
  - intros p' newp n len Huslh. cbn in Huslh.
    unfold uslh_bind, uslh_ret in Huslh. cbn in Huslh.
    (* all these destructors don't simplify by themselves, unfortunately. *)
    (* first, we need to destruct the outer layer to recover the arguments of the recursive call *)
    match goal with 
    | [H: (let '(r, p0) := ?e in _) = _ |- _] => destruct e eqn: He
    end.
    (* Now, we can use the induction hypothesis to get the length of this part *)
    destruct (List.mapT_list id (map uslh_blk (combine (seq (S n) (Datatypes.length p)) p)) (len + Datatypes.length p0)) as [ p'' newp' ] eqn: Heq.
    apply IHp in Heq.
    inv Huslh.
    (* We now need to destruct the expressions in He further, just enough to recover that the function applied here is cons. We don't care about the value, only the length. *)
    match goal with 
    | [H: (let '(_, _) := ?e in _) = _ |- _] => destruct e eqn: He'
    end.
    inv He.
    match goal with 
    | [H: (let '(_, _) := ?e in _) = _ |- _] => destruct e eqn: He''
    end.
    inv He'.
    cbn.
    now rewrite Heq.
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
    assert (   o <= Datatypes.length (rev l ++ [i0]) - 1
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

Lemma src_safe_inv p tp pc tpc
  (WFP: wf_prog p)
  (WFTP: wf_uslh p)
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ skip }}>) :
  tp[[tpc]] = Some <{{ skip }}>.
Proof.
  unfold wf_uslh in WFTP.
  specialize (WFTP WFP).
  unfold pc_sync in PS. ss.
  des_ifs_safe.
  rename p0 into iblk.
  destruct pc as [l o]; ss.
  des_ifs_safe.
  assert (Datatypes.length p <= Datatypes.length (uslh_prog p)). { apply p_le_tp. }
  unfold uslh_prog in *.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn: Huslh.
  rewrite tr_app_correct in *. rewrite nth_error_app.
  assert (nth_error (p' ++ newp) l <> None).
  { unfold not; intros. rewrite nth_error_None in H0.
    assert (nth_error p l <> None). { unfold not; intros; clarify. }
    rewrite nth_error_Some in H1.
    eapply le_trans in H; eauto. rewrite le_succ_l in H.
    assert (~ (l >= Datatypes.length (p' ++ newp))). { lia. }
    contradiction.
  }
  rewrite <- nth_error_app. destruct (nth_error (p' ++ newp) l) as [sblk|] eqn:Happ; clarify.
  unfold wf_prog in WFTP. destruct WFTP. rewrite Forall_forall in H2.
  unfold wf_block in H2. specialize (nth_error_In (p' ++ newp) l Happ); intros. 
  apply H2 in H3. destruct H3, H4. rewrite Forall_forall in H5.
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

(* Yonghyun's lemma, prove this *)
(*
   fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then acc + 1 else acc)
    (l0 ++ [<{{ skip }}>]) (if Bool.eqb (snd iblk) true then 2 else 0) =
  fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then acc + 1 else acc) l0
    (if Bool.eqb (snd iblk) true then 2 else 0) *)

(* Print wf_ds. ==> Forall (wf_dir p pc) ds *)
(* Definition get_pc_sc (sc: spec_cfg) : cptr :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  pc. *)
(* Print wf_dir.
wf_dir =
fun (p : prog) (pc : cptr) (d : direction) =>
match d with
| DBranch _ =>
    match p [[pc]] with
    | Some <{{ branch _ to l }}> => is_some p [[(l, 0)]] = true
    | _ => False
    end
| DCall pc' =>
    match p [[pc]] with
    | Some <{{ call _ }}> => is_some p [[pc']] = true
    | _ => False
    end
   end *)

(* BCC lemma for one single instruction *)
Lemma ultimate_slh_bcc_single_cycle (p: prog) : forall ic1 sc1 sc2 n ds os,
  no_ct_prog p ->
  wf_prog p ->
  wf_ds p (get_pc_sc sc1) ds ->
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
      unfold pc_sync in Hpcsync. simpl in Hpcsync.
      rewrite Hipc in Hfst, Hsnd. simpl in Hfst, Hsnd. rewrite Hfst, Hsnd in *.

      (* put program in form where we can access block 0 and rest *)
      destruct p as [|b bs] eqn:Hp. { simpl in *. inv H. } (*simpl in *.*) 
      destruct i.
      { (* skip *) 
        assert (si = <{{ skip }}>).
        { admit. }
        rewrite H4 in *. injection n_steps; intros. rewrite <- H5 in *.
        rewrite <- H2 in *. clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inv tgt_steps. exists (l, (add o 1), r, m, sk, ms). 
        (*unfold wf_dir in wfds. rewrite Forall_forall in wfds. simpl in wfds.*)
        assert (ds = [] /\ os = []).
        { inv H12. inv H11; clarify. ss. rewrite app_nil_r in H6, H7. auto. }
        des; subst. simpl in H6, H7. eapply app_eq_nil in H6, H7. des; subst.
        split.
        - econs. auto.
        - inv H12. inv H11; clarify.
          econs; eauto.
          { unfold pc_sync. cbn. rewrite Hfst. 
            assert (exists i', (nth_error (fst iblk) (add o 1)) = Some i').
            { apply block_always_terminator with (p:=(b :: bs)) (i:=<{{ skip }}>); clarify.
              rewrite Forall_forall in H0. specialize (H0 iblk). 
              specialize (nth_error_In (b :: bs) sl Hfst); intros.
              apply (H0 H2).
            }
            destruct H2 as (i' & H2). rewrite H2.
            assert (forall n, (add n 1) = S n). { lia. }
            specialize (H5 o). rewrite H5.
            specialize (firstnth_error (fst iblk) o <{{ skip }}> Hsnd) as ->.
            rewrite fold_left_app. cbn.
            repeat f_equal.  
            assert ((add (o + fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc)
                      (firstn o (fst iblk)) (if Bool.eqb (snd iblk) true then 2 else 0)) 1) = 
                    (S ((o + fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc)
                      (firstn o (fst iblk)) (if Bool.eqb (snd iblk) true then 2 else 0))) ) ). { lia. }
            rewrite H6. auto.
          }
          { econs; eauto. intros. destruct H2. unfold apply. destruct r. cbn. 
            destruct (map_get m0 x); clarify; destruct (string_dec x msf); clarify.
          }
      }
      { (* x := e *) 
        assert (si = <{{ x := e }}>).
        { admit. }
        rewrite H4 in *. 
        assert (x <> callee).
        { unfold unused_prog in unused_p_callee. destruct (split (b :: bs)) eqn:Hsplit; clarify.
          rename l0 into insts. rename l1 into bools. rewrite Forall_forall in unused_p_callee.
          specialize unused_p_callee with (x:=(fst iblk)). specialize (nth_error_In (b :: bs) sl Hfst); intros.
          specialize (split_combine (b :: bs) Hsplit); intros. rewrite <- H4 in H2.
          assert (iblk = ((fst iblk), (snd iblk))). { destruct iblk. simpl. auto. }
          rewrite H5 in H2. specialize (in_combine_l insts bools (fst iblk) (snd iblk) H2); intros.
          specialize (unused_p_callee H6). unfold b_unused in unused_p_callee. rewrite Forall_forall in unused_p_callee.
          specialize (nth_error_In (fst iblk) o Hsnd); intros. specialize unused_p_callee with (x:=<{{ x := e }}>).
          specialize (unused_p_callee H7).  cbn in unused_p_callee. destruct unused_p_callee. assumption.
        }
        rewrite <- String.eqb_neq in H5. rewrite H5 in n_steps.
        assert (x <> msf).
        { unfold unused_prog in unused_p_msf. destruct (split (b :: bs)) eqn:Hsplit; clarify.
          rename l0 into insts. rename l1 into bools. rewrite Forall_forall in unused_p_msf.
          specialize unused_p_msf with (x:=(fst iblk)). specialize (nth_error_In (b :: bs) sl Hfst); intros.
          specialize (split_combine (b :: bs) Hsplit); intros. rewrite <- H4 in H2.
          assert (iblk = ((fst iblk), (snd iblk))). { destruct iblk. simpl. auto. }
          rewrite H6 in H2. specialize (in_combine_l insts bools (fst iblk) (snd iblk) H2); intros.
          specialize (unused_p_msf H7). unfold b_unused in unused_p_msf. rewrite Forall_forall in unused_p_msf.
          specialize (nth_error_In (fst iblk) o Hsnd); intros. specialize unused_p_msf with (x:=<{{ x := e }}>).
          specialize (unused_p_msf H8).  cbn in unused_p_msf. destruct unused_p_msf. assumption.
        }
        rewrite <- String.eqb_neq in H6. rewrite H6 in n_steps. 
        injection n_steps; intros. rewrite <- H5 in *.
        rewrite <- H2 in *. clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps. rewrite H5 in tgt_steps.
        inv tgt_steps; try discriminate. (* assert (n0 = 0). { lia. } rewrite H2 in H13. *)
        exists (l, (add o 1), x !-> (eval r e); r, m, sk, ms). 
        (*unfold wf_dir in wfds. rewrite Forall_forall in wfds. simpl in wfds.*)
        assert (ds = [] /\ os = []).
        { inv H13; clarify. inv H12; clarify. ss. 
          rewrite app_nil_r in H8, H9. auto. 
        }
        des; subst. simpl in H8, H9. eapply app_eq_nil in H8, H9. des; subst.
        split; [econs; auto|].
        inv H13; clarify. inv H12; clarify.
        simpl. econs; eauto.
        { unfold pc_sync. cbn. rewrite Hfst. 
          assert (exists i', (nth_error (fst iblk) (add o 1)) = Some i').
          { apply block_always_terminator with (p:=(b :: bs)) (i:=<{{ x := e }}>); clarify.
            rewrite Forall_forall in H0. specialize (H0 iblk). 
            specialize (nth_error_In (b :: bs) sl Hfst); intros.
            apply (H0 H2).
          }
          destruct H2 as (i' & H2). rewrite H2.
          assert (forall n, (add n 1) = S n). { lia. }
          specialize (H3 o). rewrite H3.
          specialize (firstnth_error (fst iblk) o <{{ x := e }}> Hsnd) as ->.
          rewrite fold_left_app. cbn.
          assert ((add (o + fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc)
                    (firstn o (fst iblk)) (if Bool.eqb (snd iblk) true then 2 else 0)) 1) = 
                  (S ((o + fold_left (fun (acc : nat) (i : inst) => if is_br_or_call i then (add acc 1) else acc)
                    (firstn o (fst iblk)) (if Bool.eqb (snd iblk) true then 2 else 0))) ) ). { lia. }
          rewrite H7; auto.
        }
        { econs.
          - admit.
          - admit.
        }
      }
      { (* branch *) admit. }
      { (* jump *) 
        assert (si = <{{ jump l0 }}>). { admit. }
        rewrite H4 in *. injection n_steps; intros. rewrite <- H5 in tgt_steps.
        rewrite <- H2 in *. clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inv tgt_steps. exists (l0, 0, r, m, sk, ms).
        assert (ds = [] /\ os = []).
        { inv H12. inv H11; clarify. ss. rewrite app_nil_r in H6, H7. auto. } 
        des; subst. simpl in H6, H7. eapply app_eq_nil in H6, H7. des; subst.
        split.
        - econs. auto.
        - inv H12. inv H11; clarify.
          simpl. econs; clarify. 
          { unfold pc_sync. cbn. unfold wf_block in H0. rewrite Forall_forall in H0.
            specialize (nth_error_In (b :: bs) sl Hfst); intros. 
            apply H0 in H2. destruct H2, H3. rewrite Forall_forall in H5. 
            specialize (H5 <{{ jump l0 }}>). specialize (nth_error_In (fst iblk) o Hsnd); intros. 
            apply H5 in H6. unfold wf_instr in H6. unfold wf_lbl in H6. 
            destruct (nth_error (b :: bs) l0) eqn:Hlbl; clarify. rename p into jblk. 
            destruct jblk as (jinsts & jbool) eqn:Hjblk. cbn. rewrite <- H6 in *. cbn. 
            specialize (nth_error_In (b :: bs) l0 Hlbl); intros. apply H0 in H7. destruct H7, H8.
            specialize (blk_not_empty_list (jinsts, false) H7); intros. 
            simpl in H10. destruct jinsts; clarify.
          }
          { econs; clarify. admit.
          }
      }
      { (* load *) 
        assert (si = <{{ x <- load[a] }}>). { admit. }
        rewrite H4 in *. injection n_steps; intros. rewrite <- H5 in tgt_steps.
        rewrite <- H2 in *. clear cfg_sync.
        rewrite <- app_nil_r with (l:=ds) in tgt_steps.
        rewrite <- app_nil_r with (l:=os) in tgt_steps.
        inv tgt_steps. 
        assert (ds = []).
        { inv H12. inv H11; clarify. ss. rewrite app_nil_r in H6. auto. }
        rewrite H2 in *.
        inv H12. injection Hpcsync; intros. 
        assert (exists n, to_nat (eval r a) = Some n). { admit. }
        destruct H5 as (n & H5).
        assert (exists v, nth_error m n = Some v). { admit. }
        destruct H8 as (v & H8). 
        assert (os = [OLoad (if ms then 0 else n)]). 
        { admit.  }
        rewrite H9 in *.
        exists (((l, o) + 1), x !-> v; r, m, sk, ms).
        split; [econs; eauto|].
        (*
          | ISMI_Load : forall (pc : cptr) (r : reg) (m : list val) 
                  (sk : list cptr) (x : string) (e : exp) 
                  (n n' : nat) (v' : val) (ms : bool),
                p [[pc]] = Some <{{ x <- load[ e] }}> ->
                to_nat (eval r e) = Some n ->
                nth_error m n = Some v' ->
                n' = (if ms then 0 else n) ->
                p |- <(( S_Running (pc, r, m, sk, ms) ))> -->i_ [] ^^ [OLoad n'] <(( S_Running (pc + 1, x !-> v'; r, m, sk, ms) ))>
          
          | SpecSMI_Load : forall (pc : cptr) (r : reg) (m : list val)
                     (sk : list cptr) (x : string) 
                     (e : exp) (n : nat) (v' : val) 
                     (ms : bool),
                   p [[pc]] = Some <{{ x <- load[ e] }}> ->
                   to_nat (eval r e) = Some n ->
                   nth_error m n = Some v' ->
                   p |- <(( S_Running (pc, r, m, sk, false, ms) ))> -->_ [] ^^ [OLoad n] <((S_Running (pc + 1, x !-> v'; r, m, sk, false, ms) ))>
        
        *)
        

        admit. }
      { (* store *) admit. }
      { (* call *) admit. } Print split.
      { (* ctarget *) unfold no_ct_prog in nct. destruct (split (b :: bs)) as (b_insts & b_bools) eqn:Hbb.
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

(* DONT NEED RIGHT NOW *)
      (* try to get Hmap (info about decorated program wrt blocks and insts) into 
         shape where that info can be accessed and moved around *)
      (* simpl in wfds. rewrite Forall_forall in H0, wfds.
      rewrite <- H2 in tgt_steps, ms_msf, wfds. clear cfg_sync.
      unfold tp in *. unfold uslh_prog in *. 
      destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) eqn:Hmap.
      rename l0 into trans_p. rename p0 into new_blks.
      simpl in *. unfold Utils.app in *. rewrite revs in *.
         rewrite utils_rev_append_and_rev in *. rewrite rev_involutive in *.*)

(* DONT NEED RIGHT NOW
      destruct o as [|o'] eqn:Hoffset.
      { (* offset is 0 *) destruct (Bool.eqb (snd iblk) true) eqn:Hproc.
        { (* proc blk, add 2 steps *) simpl in Hpcsync. injection Hpcsync; intros. 
          rewrite <- H4, <- H5 in *. clear Hpcsync. admit.
          
        }
        { (* non-proc blk *) simpl in Hpcsync. injection Hpcsync; intros.
          rewrite <- H4, <- H5 in *. clear Hpcsync. rewrite Hspc, Hipc in *.
          replace (fst (l, 0)) with l in * by auto.
          replace (snd (l, 0)) with 0 in * by auto.
          admit.
        }
      }
      { (* offset is S _, accumulate steps from earlier in block *) admit.
         } *)

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
     (prefix os1 os2) \/ (prefix os2 os1).  

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


