(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import ListMaps.
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

Inductive state {A} : Type :=
  | S_Running (a: A)
  | S_Undef
  | S_Fault
| S_Term.

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
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( S_Term ))>

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

(*
Definition uslh_inst (i: inst) : M (list inst) :=
  match i with
  | <{{ctarget}}> => ret [<{{skip}}>]
  | <{{x<-load[e]}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{x<-load[e']}}>]
  | <{{store[e] <- e1}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{store[e'] <- e1}}>]
  | <{{branch e to l}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in (* if mispeculating always pc+1 *)
      l' <- add_block_M <{{ i[(msf := ((~e') ? 1 : msf)); jump l] }}>;;
      ret <{{ i[branch e' to l'; (msf := (e' ? 1 : msf))] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &0 : e }> in
      ret <{{ i[callee:=e'; call e'] }}>
  | _ => ret [i]
  end.

Definition uslh_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  bl' <- concatM (mapM uslh_inst bl);;
  if is_proc then
    ret (<{{ i[ctarget; msf := (callee = &l) ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition uslh_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM uslh_blk idx_p (Datatypes.length p) in
  (p' ++ newp).
*)

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
      p |- <(( S_Running ((pc, r, m, pc'::sk), ms) ))> -->i_[]^^[] <(( S_Term ))>

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

Section BCC.

Variable p: prog.
Definition tp : prog := uslh_prog p.

Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

Definition pc_sync (pc: cptr) : option cptr :=
  blk <- nth_error p (fst pc);; (* label in bounds *)
  i <- nth_error (fst blk) (snd pc);; (* offset in bounds *)
  let acc1 := if (Bool.eqb (snd blk) true) then 2 else 0 in (* procedure blocks add 2 insts *)
    match (snd pc) with
    | 0 => Some ((fst pc), add (snd pc) acc1)
    | S _ => let insts_before_pc := (firstn (snd pc) (fst blk)) in (* accumulate extra insts from br and call insts preceding pc inst *)
               let acc2 := fold_left (fun acc (i: inst) =>
                 if (is_br_or_call i) then (add acc 1) else acc) insts_before_pc acc1 in
                   Some ((fst pc), add (snd pc) acc2)
    end.

(* sync src and tgt registers *)
(* can't handle callee here, not enough info if not speculating *)
Definition r_sync (r: reg) (ms: bool) : reg :=
  msf !-> N (if ms then 1 else 0); r.

Fixpoint map_opt {S T} (f: S -> option T) l : option (list T):=
  match l with 
  | [] => Some []
  | a :: l' => a' <- f a;;
      l'' <- map_opt f l';;
      ret (a' :: l'')
  end.

(* sync src/ideal and target cfg (affects pc, register state, and stack) *)
Definition spec_cfg_sync (*(p: prog)*) (ic: ideal_cfg): option spec_cfg :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  pc' <- pc_sync (*p*) pc;;
  stk' <- map_opt (pc_sync (*p*)) stk;;
  ret (pc', r_sync r ms, m, stk', false, ms).

(* How many steps does it take for target program to reach the program point the source reaches in one step? *)
Definition steps_to_sync_point (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
    (* check pc is well-formed *)
    blk <- nth_error p (fst pc);;
    i <- nth_error (fst blk) (snd pc);;
    match i with
    | <{{_ := _}}> => match p[[pc+1]] with
                      | Some i => match i with
                                  | <{{call _}}> => match ds with
                                                    | [DCall lo] => (* decorated call with correct directive *)
                                                                    let '(l, o) := lo in
                                                                    (* check attacker pc is well-formed *)
                                                                    blk <- nth_error p l;;
                                                                    i <- nth_error (fst blk) o;;
                                                                    (* 4 steps if procedure block, fault otherwise *)
                                                                    if (Bool.eqb (snd blk) true) && (o =? 0) then Some 4 else None
                                                    | _ => None (* incorrect directive for call *)
                                                    end
                                  | _ => Some 1 (* assignment from source program, not decoration *)
                                  end
                      | None => Some 1 (* assignment from source program, last instruction in block *)
                      end
    | <{{ branch _ to _ }}> => (* branch decorations all come after the instruction itself, so this is the sync point *)
                               match ds with
                               | [DBranch b] => Some (if b then 3 else 2)
                               | _ => None
                               end
    | _ => Some 1 (* branch and call are the only instructions that add extra decorations *)
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

(* Termination *)

Inductive result : Type :=
| R_Normal
| R_Fault
| R_UB.

(* target *)

Definition is_fault_tgt (res_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := res_t in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ctarget }}> => Some (if ct then false else true)
  | _ => Some (if ct then true else false)
  end.

Definition is_normal_termination_tgt (res_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := res_t in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ret }}> => Some (if seq.nilp sk then true else false)
  | _ => Some false
  end.

Definition is_stuck_tgt (res_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := res_t in
  let '(pc, rs, m, sk) := c in
  _ <- p[[pc]];;
  match (is_fault_tgt res_t, is_normal_termination_tgt res_t) with
  | (Some false, Some false) => Some true
  | _ => Some false
  end.

Definition classify_res_tgt (res_t: spec_cfg) : result :=
  if (is_fault_tgt res_t) then R_Fault else
  if (is_normal_termination_tgt res_t) then R_Normal else R_UB.

(* source *)

Definition is_fault_src (res_s: ideal_cfg) : option bool :=
  let '(c, ms) := res_s in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  Some true.
  (* now what? *)

(* Normal termination: ret + empty stack *)
Definition is_normal_termination_src (res_s: ideal_cfg) : option bool :=
  let '(c, ms) := res_s in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ret }}> => Some (if seq.nilp sk then true else false)
  | _ => Some false
  end.

(* any other final state means the program got stuck because of UB *)
Definition is_stuck_src (res_s: ideal_cfg) : option bool :=
  let '(c, ms) := res_s in
  let '(pc, rs, m, sk) := c in
  _ <- p[[pc]];;
  match (is_fault_src res_s, is_normal_termination_src res_s) with
  | (Some false, Some false) => Some true
  | _ => Some false
  end.

Definition classify_term_src (res_s: ideal_cfg) : result :=
  if (is_fault_src res_s) then R_Fault else
  if (is_normal_termination_src res_s) then R_Normal else R_UB.

Definition same_result_type (sc: spec_cfg) (ic: ideal_cfg) : bool :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  let '(c', ms') := ic in 
  let '(pc', r', m', sk') := c' in
  match (p[[pc]], p[[pc']]) with
  | (Some i, Some i') =>
      let ub_t := is_stuck_tgt sc in
      let ub_s := is_stuck_src ic in
      let normal_t := is_normal_termination_tgt sc in
      let normal_s := is_normal_termination_src ic in
      let fault_t := is_fault_tgt sc in
      let fault_s := is_fault_src ic in
      let ub_match :=
        match (ub_t, ub_s) with
        | (Some b1, Some b2) => b1 && b2
        | _ => false
        end in
      let normal_match :=
        match (normal_t, normal_s) with
        | (Some b1', Some b2') => b1' && b2'
        | _ => false
        end in
      let fault_match :=
        match (fault_t, fault_s) with
        | (Some b1'', Some b2'') => b1'' && b2''
        | _ => false
        end in
          ub_match || normal_match || fault_match
  | _ => false
   end.

(* Well-formedness properties *)

Definition wf_dir (pc: cptr) (d: direction) : Prop :=
  match d, p[[pc]] with
  | DBranch b, Some (IBranch e l) => is_some p[[(l, 0)]] = true
  | DCall pc', Some (ICall e) => is_some p[[pc']] = true
  | _, _ => False
  end.

Definition wf_ds (pc: cptr) (ds: dirs) : Prop :=
  Forall (wf_dir pc) ds.

Definition nonempty_block (blk : (list inst * bool)) : Prop :=
  0 < Datatypes.length (fst blk).

Definition is_return_or_jump (i: inst) : bool :=
  match i with
  | <{{ ret }}> | <{{ jump _}}> => true
  | _ => false
  end.

Definition last_inst_ret_or_jump (blk: (list inst * bool)) : Prop :=
  match (rev (fst blk)) with 
  | [] => False (* unreachable *)
  | h::t => (is_return_or_jump h = true)
  end.

Definition wf_lbl (is_proc: bool) (l: nat) : Prop :=
  match nth_error p l with 
  | Some (_,b) => is_proc = b
  | None => False
  end.

Fixpoint wf_expr (e: exp) : Prop :=
  match e with
  | ANum _ | AId _ => True
  | ABin _ e1 e2  | <{_ ? e1 : e2}> => wf_expr e1 /\ wf_expr e2
  | <{&l}> => wf_lbl true l
  end.

Definition wf_instr (i: inst) : Prop := 
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> => True
  | <{{_:=e}}> | <{{_<-load[e]}}> | <{{call e}}> => wf_expr e
  | <{{store[e]<-e'}}> => wf_expr e /\ wf_expr e'
  | <{{branch e to l}}> => wf_expr e /\ wf_lbl false l
  | <{{jump l}}> => wf_lbl false l
  end.

Definition wf_block (blk : (list inst * bool)) : Prop :=
   nonempty_block blk /\ last_inst_ret_or_jump blk /\ Forall wf_instr (fst blk).

Definition nonempty_program : Prop :=
  0 < Datatypes.length p.

Definition wf_prog : Prop :=
  nonempty_program /\ Forall wf_block p.

(* Tactics *)

From SECF Require Import sflib.

Ltac inv H := inversion H; subst; clear H.

(* BCC lemma for one single instruction *)
(* Starting conditions:
    - program and directives are well-formed
    - msf and callee variables are unused by the source program 
    - The msf variable in the target start state matches the ms flag in the semantics 
    - synchronization relation between source/ideal and target start states:
      • It takes n steps for the target to reach the sync point the source reaches in one ideal step 
      • The start states are synchronized wrt pc, register state, and stack 
*)

(*
Lemma pc_not_none : forall (pc: cptr) (i: inst),
  p[[pc]] = Some i ->
  exists blk, nth_error p (fst pc) = Some blk /\ nth_error (fst blk) (snd pc) = Some i.
Proof.
  intros. destruct pc as (l & o) eqn:Hpc. simpl in *.
  destruct (nth_error p l); [exists p0; split; auto|discriminate].
Qed.
 *)

(* using this *)
Lemma rev_fetch : forall (pc: cptr) (blk: list inst * bool) (i: inst),
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
  simpl in H. assert (~ 0 < 0). { apply nlt_0_r. }
  contradiction.
Qed.

(*
Lemma rev_empty : forall {A} (l: list A),
  l = [] -> rev l = [].
Proof.
  intros; unfold not; intros. rewrite H; reflexivity.
Qed.

Lemma empty_length_0 : forall {A} (l: list A),
  l = [] -> Datatypes.length l = 0.
Proof.
  intros. rewrite H. simpl; reflexivity.
Qed.

Lemma nonempty_length_nonzero : forall {A} (l: list A),
  l <> [] -> Datatypes.length l <> 0.
Proof.
  intros. destruct l; try contradiction.
  simpl. unfold not; intros; discriminate.
Qed.

Lemma rev_not_empty : forall {A} (l: list A),
  l <> [] -> rev l <> [].
Proof.
  intros. destruct l; try contradiction.
  unfold not; intros. simpl in *. apply app_eq_nil in H0.
  destruct H0. discriminate.
Qed.
 *)

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

Lemma oob_block : forall (l o: nat) (blk: list inst * bool) (i: inst) (rest: list inst),
  nth_error p l = Some blk ->
  wf_block blk ->
  block_terminator blk = true ->
  nth_error (fst blk) o = Some i ->
  nth_error (fst blk) (add o 1) = None ->
  Utils.rev (fst blk) = i :: rest.
Proof.
  intros. unfold wf_block in H0. destruct H0, H4. unfold block_terminator in H1.
  rewrite Forall_forall in H5. unfold last_inst_ret_or_jump in H4. destruct (rev (fst blk)); try destruct H4.
  unfold is_return_or_jump in H1. Admitted.

Lemma ultimate_slh_bcc_single_cycle : forall ic1 sc1 sc2 n ds os,
  wf_prog ->
  wf_ds (get_pc_sc sc1) ds ->
  block_terminator_prog p = true ->
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0) ->
  steps_to_sync_point sc1 ds = Some n ->
  spec_cfg_sync ic1 = Some sc1 ->
  uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( S_Running sc2 ))> ->
      exists ic2, p |- <(( S_Running ic1 ))> -->i_ ds ^^ os <(( S_Running ic2 ))> /\ spec_cfg_sync ic2 = Some sc2.
Proof.
  intros until os. intros wfp wfds wfp_term unused_p_msf unused_p_callee ms_msf n_steps cfg_sync tgt_steps.
  destruct ic1 as (c & ms). destruct c as (c & sk). destruct c as (c & m). destruct c as (ipc & r).
  unfold wf_prog in wfp. destruct wfp. unfold wf_block in H0. unfold nonempty_program in H.
  unfold wf_ds in wfds. simpl in ms_msf.
  (* destructing to ipc's instruction, keeping information along the way *)
  destruct ipc as (l & o) eqn:Hipc.
  destruct (nth_error p l) as [iblk|] eqn:Hfst.
  - (* Some blk *)
    destruct (nth_error (fst iblk) o) as [i|] eqn:Hsnd.
    + (* Some i *)
      replace l with (fst ipc) in Hfst by (rewrite Hipc; auto).
      replace o with (snd ipc) in Hsnd by (rewrite Hipc; auto).
      specialize (rev_fetch ipc iblk i Hfst Hsnd); intros. (* recovered single-step premise *)
      (* case over starting instruction in ideal execution *)
      simpl in *.
      destruct (pc_sync (l, o)) as [spc|] eqn:Hpcsync; try discriminate.
      destruct (map_opt pc_sync sk) as [ssk|] eqn:Hsk; try discriminate.
      injection cfg_sync; intros. rewrite <- H2 in n_steps. (* unpacked starting spec cfg *)
      destruct spc as (sl, so) eqn:Hspc. simpl in n_steps.
      destruct (nth_error p sl) eqn:Hsfst; try discriminate. rename p0 into sblk.
      destruct (nth_error (fst sblk) so) eqn:Hssnd; try discriminate. rename i0 into si.
      destruct i eqn:Hi.
      { (* skip *) 
        assert (si = <{{ skip }}>). { admit. }
        specialize (ISMI_Skip p ipc r m sk ms H1); intros. 
        rewrite H3 in n_steps. injection n_steps; intros. rewrite <- H5 in *.
        inv tgt_steps. inv H12. inv H7.
        { (* speculative inst: skip *)
          apply SpecSMI_Skip with (r:=r) (m:=m) (sk:=sk) (ms:=ms) in H12.
          exists ((l, o) + 1, r, m, sk, ms). simpl. split; auto. simpl in *.
          clear H1. clear cfg_sync. clear n_steps.
          rewrite Forall_forall in H0, wfds. simpl in wfds.
          assert (pc_sync (l, (add o 1)) = Some (sl, (add so 1))).
          { unfold pc_sync. cbn. rewrite Hfst.
            (* first, this can't be None if o is skip
               second, o + 1 can't ever match with 0
            *)
            destruct (nth_error (fst iblk) (add o 1)) eqn:Hi_next.
            - (* Some *)
              destruct (add o 1).
              + (* 0 (not possible) *)
                simpl. assert (add o (S 0) <> 0). { induction o; try discriminate. } f_equal. f_equal;
                [inv H4; try contradiction; simpl in *; rewrite Hfst in H3; rewrite Hsnd in H3; discriminate|].
                inv H12; [| |destruct so; try discriminate].
                { simpl in H3. destruct (nth_error (uslh_prog p) sl) as [uslh_blk|]; try discriminate. inv H4; try contradiction.
                  simpl in H5. rewrite Hfst in H5. rewrite Hsnd in H5. discriminate.
                }
                { inv H4; try contradiction. simpl in H5. rewrite Hfst in H5. rewrite Hsnd in H5. discriminate. }
              + (* S _ *) f_equal. admit.
            - (* None (not possible) *)
              inv H4.
              + inv H12.
                * inv H3. destruct (nth_error (uslh_prog p) sl) as [uslh_blk|]; try discriminate. 
                  (* show that skip can't be last inst in blk (i.e. Hsnd and Hi_next together make a contradiction) *)
                  specialize H0 with (x:=iblk). specialize (nth_error_In p l Hfst). intros. specialize (H0 H1).
                  destruct H0, H3. unfold block_terminator_prog in wfp_term. rewrite forallb_forall in wfp_term.
                  specialize wfp_term with (x:=iblk). specialize (wfp_term H1). unfold block_terminator in wfp_term.
                  admit.
                * admit.
                * admit.
              + admit.
              + admit.
          } (* end assert proof *)
          { (* finish skip proof *) admit. }
        }
        (* other speculative instructions *)
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
      }
      (* other instructions *)
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }
      { admit. }        
    + (* None *)
      simpl in cfg_sync. destruct (pc_sync (l, o)) eqn:Hpcsync; try discriminate.
      destruct (map_opt pc_sync sk) eqn:Hsksync; try discriminate. unfold pc_sync in Hpcsync.
      cbn in Hpcsync. destruct (nth_error p l) as [blk'|] eqn:Hfst'; try discriminate.
      injection Hfst; intros. rewrite H1 in *. clear Hfst. clear H1. 
      destruct (nth_error (fst iblk) o) as [i'|] eqn:Hsnd'; discriminate.
  - (* None *)
    simpl in cfg_sync. simpl in cfg_sync. destruct (pc_sync (l, o)) eqn:Hpcsync; try discriminate.
    destruct (map_opt pc_sync sk) eqn:Hsksync; try discriminate. unfold pc_sync in Hpcsync.
    cbn in Hpcsync. destruct (nth_error p l) as [blk'|] eqn:Hfst'; discriminate.
Admitted.
 
End BCC.

(* Lemma ultimate_slh_bcc (p: prog) : forall sc1 tsc1 tsc2 n ds os,
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) ->
  tsc1 = spec_cfg_sync p sc1 ->
  uslh_prog p |- <(( S_Running tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( S_Running sc1 ))> -->i*_ ds ^^ os <(( sc2 ))> /\ tsc2 = spec_cfg_sync p sc2 /\ same_result_type sc2 tsc2.
Proof.
   Admitted. *)

(* (** * Definition of Relative Secure *) *)

(* Definition seq_same_obs p c st1 st2 ast1 ast2 : Prop := *)
(*   forall stt1 stt2 astt1 astt2 os1 os2 c1 c2, *)
(*     p |- <(( (pc1, r1, m1, stk1) ))> -->*^ os1 <(( (pc1', r1', m1', stk1') ))> -> *)
(*     p |- <(( (pc2, r2, m2, stk2) ))> -->*^ os2 <(( (pc2', r2', m2', stk2') ))> -> *)
(*     (prefix os1 os2) \/ (prefix os2 os1).  *)

(* Definition spec_same_obs p c st1 st2 ast1 ast2 : Prop := *)
(*   forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 n c1 c2, *)
(*     p |- <((c, st1, ast1, false))> -->*_ds^^os1^^n <((c1, stt1, astt1, bt1))> -> *)
(*     p |- <((c, st2, ast2, false))> -->*_ds^^os2^^n <((c2, stt2, astt2, bt2))> -> *)
(*     os1 = os2.  *)

(* (* The new definition adds the extra program transformation we  *)
(*    needed to check for speculation at the target of a call instruction. *)
(*    This was needed to apply the bcc proof in the final theorem. *) *)

(* (*  old definition: *)
(*    Definition relative_secure (p:prog) (trans : com -> com) *)
(*     (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop := *)
(*   seq_same_obs p c st1 st2 ast1 ast2 -> *)
(*    spec_same_obs p (trans c) st1 st2 ast1 ast2. *) *)

(* Definition relative_secure (p:prog) (trans1 : prog -> prog) (trans2 : com -> com) *)
(*     (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop := *)
(*   seq_same_obs p c st1 st2 ast1 ast2 -> *)
(*   spec_same_obs (trans1 p) (trans2 c) st1 st2 ast1 ast2. *)

(* (** * Ultimate Speculative Load Hardening *) *)


