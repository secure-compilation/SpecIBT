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
Require Import Stdlib.Setoids.Setoid.
Require Import ExtLib.Data.Monads.OptionMonad.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* %s/\s\+$//e to strip trailing whitespace *)

(** Sequential small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  cfg -> cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( (pc, rs, m, stk) ))> -->^[] <(( (pc+1, rs, m, stk) ))>
  | SSMI_Asgn : forall pc r m sk e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( (pc+1, (x !-> (eval r e); r), m, sk) ))>
  | SSMI_Branch : forall pc pc' r m sk e n l,
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then (l,0) else pc+1) ->
      p |- <(( (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( (pc', r, m, sk) ))>
  | SSMI_Jump : forall l pc r m sk,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( ((l,0), r, m, sk) ))>
  | SSMI_Load : forall pc r m sk x e n v',
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( (pc, r, m, sk) ))> -->^[OLoad n] <(( (pc+1, (x !-> v'; r), m, sk) ))>
  | SSMI_Store : forall pc r m sk e e' n,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( (pc, r, m, sk) ))> -->^[OStore n] <(( (pc+1, r, upd n m (eval r e'), sk) ))>
  | SSMI_Call : forall pc r m sk e l,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      p |- <(( (pc, r, m, sk) ))> -->^[OCall l] <(( ((l,0), r, m, ((pc+1)::sk)) ))>
  | SSMI_Ret : forall pc r m sk pc',
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( (pc, r, m, pc'::sk) ))> -->^[] <(( (pc', r, m, sk) ))>

  where "p |- <(( c ))> -->^ os <(( ct ))>" :=
      (seq_eval_small_step_inst p c ct os).

(** Sequential multi-step relation *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->*^' os '<((' ct '))>'"
      (at level 40, c constr, ct constr).

Inductive multi_seq_inst (p : prog) (c : cfg) : cfg -> obs -> Prop :=
  | multi_seq_inst_refl : p |- <(( c ))> -->*^[] <(( c ))>
  | multi_seq_inst_trans (c' c'' : cfg) (os1 os2 : obs) :
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
    spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then (l, 0) else (pc+1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( (((l,0), r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n] <(( ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore n] <(( ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( ((pc', r, m, sk), false, ms) ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

(** Speculative multi-step relation *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> nat -> Prop :=
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
  ideal_cfg -> ideal_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( ((pc+1, r, m, sk), ms) ))>
  | ISMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( ((pc+1, (x !-> (eval r e); r), m, sk), ms) ))>
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      n' = (if ms then 0 else n) -> (* uslh masking *)
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) ->
      ms' = (ms || (negb (Bool.eqb b b'))) ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( (((l,0), r, m, sk), ms) ))>
  | ISMI_Load : forall pc r m sk x e n n' v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      n' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[]^^[OLoad n'] <(( ((pc+1, (x !-> v'; r), m, sk), ms) ))>
  | ISMI_Store : forall pc r m sk e e' e'' n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      e'' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[]^^[OStore e''] <(( ((pc+1, r, upd n m (eval r e'), sk), ms) ))>
  | ISMI_Call : forall pc pc' blk o r m sk e l l' (ms ms' : bool),
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      l' = (if ms then 0 else l) -> (* uslh masking *)
      nth_error p (fst pc') = Some blk -> (* attacker pc must be in-bounds wrt label and offset *)
      nth_error (fst blk) (snd pc') = Some o ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) -> (* if attacker pc doesn't match source pc we're speculating *)
      (* then also we'd like to detect whether, given pc', the next step will fault. It will fault if the place we're
         speculating to is not the beginning of a proc block. Let's start there. *)
      p |- <(( ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l'] <(( ((pc', r, m, (pc+1)::sk), ms') ))>
  | ISMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), ms) ))> -->i_[]^^[] <(( ((pc', r, m, sk), ms) ))>

  where "p |- <(( ic ))> -->i_ ds ^^ os  <(( ict ))>" :=
    (ideal_eval_small_step_inst p ic ict ds os).

(** Ideal multi-step relation *)

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive multi_ideal_inst (p:prog) :
  ideal_cfg -> ideal_cfg -> dirs -> obs -> Prop :=
  | multi_ideal_inst_refl ic : p |- <(( ic ))> -->i*_[]^^[] <(( ic ))>
  | multi_ideal_inst_trans ic1 ic2 ic3 ds1 ds2 os1 os2 :
      p |- <(( ic1 ))> -->i_ds1^^os1 <(( ic2 ))> ->
      p |- <(( ic2 ))> -->i*_ds2^^os2 <(( ic3 ))> ->
      p |- <(( ic1 ))> -->i*_(ds1++ds2)^^(os1++os2) <(( ic3 ))>
  where "p |- <(( ic ))> -->i*_ ds ^^ os <(( ict ))>" :=
    (multi_ideal_inst p ic ict ds os).

(** * Backwards Compiler Correctness of Ultimate Speculative Load Hardening *)

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
                                                                    (* 4 steps if procedure block *)
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

(* Termination:
  - if instruction is ret and stack is empty: normal
  - if ct && current inst ≠ ctarget \/ if ~ct && current inst = ctarget : fault (second one can't occur, I think, with current constraints)
  - any other sort of termination: stuck/UB

*)

Inductive termination : Type :=
| T_Normal
| T_Fault
| T_UB.

(* Target *)

Definition is_fault_tgt (final_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := final_t in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ctarget }}> => Some (if ct then false else true)
  | _ => Some (if ct then true else false)
  end.

Definition is_normal_termination_tgt (final_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := final_t in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ret }}> => Some (if seq.nilp sk then true else false)
  | _ => Some false
  end.

Definition is_stuck_tgt (final_t: spec_cfg) : option bool :=
  let '(c, ct, ms) := final_t in
  let '(pc, rs, m, sk) := c in
  _ <- p[[pc]];;
  match (is_fault_tgt final_t, is_normal_termination_tgt final_t) with
  | (Some false, Some false) => Some true
  | _ => Some false
  end.

Definition classify_term_tgt (final_t: spec_cfg) : termination :=
  if (is_fault_tgt final_t) then T_Fault else
  if (is_normal_termination_tgt final_t) then T_Normal else T_UB.

(* Source *)

Definition is_fault_src (final_s: ideal_cfg) : option bool :=
  let '(c, ms) := final_s in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  Some true.
  (* now what? *)

(* Normal termination: ret + empty stack *)
Definition is_normal_termination_src (final_s: ideal_cfg) : option bool :=
  let '(c, ms) := final_s in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ret }}> => Some (if seq.nilp sk then true else false)
  | _ => Some false
  end.

(* any other final state means the program got stuck because of UB *)
Definition is_stuck_src (final_s: ideal_cfg) : option bool :=
  let '(c, ms) := final_s in
  let '(pc, rs, m, sk) := c in
  _ <- p[[pc]];;
  match (is_fault_src final_s, is_normal_termination_src final_s) with
  | (Some false, Some false) => Some true
  | _ => Some false
  end.

Definition classify_term_src (final_s: ideal_cfg) : termination :=
  if (is_fault_src final_s) then T_Fault else
  if (is_normal_termination_src final_s) then T_Normal else T_UB.

Definition same_termination (sc: spec_cfg) (ic: ideal_cfg) : bool :=
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

Ltac destruct_cfg c := destruct c as (c & ms); destruct c as (c & ct);
  destruct c as (c & sk); destruct c as (c & m); destruct c as (c & r);
  rename c into pc.

(* BCC lemma for one single instruction *)
(* Starting conditions:
    - program and directives are well-formed
    - msf and callee variables are unused by the source program 
    - The msf variable in the target start state matches the ms flag in the semantics 
    - synchronization relation between source/ideal and target start states:
      • It takes n steps for the target to reach the sync point the source reaches in one ideal step 
      • The start states are synchronized wrt pc, register state, and stack 
*)
Lemma ultimate_slh_bcc_single_cycle : forall ic1 sc1 sc2 n ds os,
  wf_prog ->
  wf_ds (get_pc_sc sc1) ds ->
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0) ->
  steps_to_sync_point sc1 ds = Some n ->
  spec_cfg_sync ic1 = Some sc1 ->
  uslh_prog p |- <(( sc1 ))> -->*_ds^^os^^n <(( sc2 ))> ->
      exists ic2, p |- <(( ic1 ))> -->i_ ds ^^ os <(( ic2 ))> /\ spec_cfg_sync ic2 = Some sc2 /\ same_termination sc2 ic2 = true.
Proof.
  Admitted.

End BCC.

Lemma ultimate_slh_bcc (p: prog) : forall sc1 tsc1 tsc2 n ds os,
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) ->
  spec_cfg_sync p sc1 = Some tsc1 ->
  uslh_prog p |- <(( tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( sc1 ))> -->i*_ ds ^^ os <(( sc2 ))> /\ spec_cfg_sync p sc2 = Some tsc2.
Proof.
Admitted.

(* (** * Definition of Relative Secure *) *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Definition seq_same_obs p i pc1 pc2 r1 r2 m1 m2 stk1 stk2 (i1 i2: inst) : Prop :=
  forall pc1' pc2' r1' r2' m1' m2' stk1' stk2' os1 os2 i1 i2, 
    p[[pc1]] = Some i ->
    p[[pc2]] = Some i ->
    p[[pc1']] = Some i1 ->
    p[[pc2']] = Some i2 ->
    p |- <(( (pc1, r1, m1, stk1) ))> -->*^ os1 <(( (pc1', r1', m1', stk1') ))> ->
    p |- <(( (pc2, r2, m2, stk2) ))> -->*^ os2 <(( (pc2', r2', m2', stk2') ))> ->
    (prefix os1 os2) \/ (prefix os2 os1).

(* not quite -- where to put the transformation *)
(* Definition spec_same_obs p i pc1 pc2 r1 r2 m1 m2 stk1 stk2 (i1 i2: inst) : Prop :=
  forall ds pc1' pc2' r1' r2' m1' m2' stk1' stk2' ct1 ct2 ms1 ms2 os1 os2 n i1 i2,
    p[[pc1]] = Some i ->
    p[[pc2]] = Some i ->
    p[[pc1']] = Some i1 ->
    p[[pc2']] = Some i2 ->
    p |- <((pc1, r1, m1, stk1, false, false))> -->*_ds^^os1^^n <((pc1', r1', m1', stk1' ct1, ms1))> ->
    p |- <((pc2, r2, m2, stk2, false, false))> -->*_ds^^os2^^n <((pc2', r2', m2', stk2', ct2, ms2))> ->
    os1 = os2.

(*  
Definition spec_same_obs p c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 n c1 c2,
    p |- <((c, st1, ast1, false))> -->*_ds^^os1^^n <((c1, stt1, astt1, bt1))> ->
    p |- <((c, st2, ast2, false))> -->*_ds^^os2^^n <((c2, stt2, astt2, bt2))> ->
    os1 = os2.

*)

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

