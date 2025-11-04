(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import ListMaps.
From SECF Require Import TempMiniCET.
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
  | SSMI_CTarget : forall pc r m sk,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( (pc+1, r, m, sk) ))>
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
  | SpecSMI_Call : forall pc pc' blk o r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      nth_error p (fst pc') = Some blk ->
      nth_error (fst blk) (snd pc') = Some o ->
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
  "p '|-' '<((' sc '))>' '-->i_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive ideal_eval_small_step_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | ISMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[]^^[] <(( ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      n' = (if ms then 0 else n) -> (* uslh masking *)
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) -> 
      ms' = (ms || (negb (Bool.eqb b b'))) -> 
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), false, ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[]^^[] <(( (((l,0), r, m, sk), false, ms) ))>
  | ISMI_Load : forall pc r m sk x e n n' v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      n' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[]^^[OLoad n'] <(( ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | ISMI_Store : forall pc r m sk e e' e'' n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      e'' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[]^^[OStore e''] <(( ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | ISMI_Call : forall pc pc' blk o r m sk e l l' (ms ms' : bool),
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      l' = (if ms then 0 else l) -> (* uslh masking *)
      nth_error p (fst pc') = Some blk -> (* attacker pc must be in-bounds wrt label and offset *)
      nth_error (fst blk) (snd pc') = Some o ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) -> (* if attacker pc doesn't match source pc we're speculating *)
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->i_[DCall pc']^^[OCall l'] <(( ((pc', r, m, (pc+1)::sk), false, ms') ))>
  | ISMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), false, ms) ))> -->i_[]^^[] <(( ((pc', r, m, sk), false, ms) ))>

  where "p |- <(( sc ))> -->i_ ds ^^ os  <(( sct ))>" :=
    (ideal_eval_small_step_inst p sc sct ds os).

(*  *)

(** Ideal multi-step relation *)

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive multi_ideal_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | multi_ideal_inst_refl ic : p |- <(( ic ))> -->i*_[]^^[] <(( ic ))>
  | multi_ideal_inst_trans ic1 ic2 ic3 ds1 ds2 os1 os2 :
      p |- <(( ic1 ))> -->i_ds1^^os1 <(( ic2 ))> ->
      p |- <(( ic2 ))> -->i*_ds2^^os2 <(( ic3 ))> ->
      p |- <(( ic1 ))> -->i*_(ds1++ds2)^^(os1++os2) <(( ic3 ))>
  where "p |- <(( ic ))> -->i*_ ds ^^ os <(( ict ))>" :=
    (multi_ideal_inst p ic ict ds os).

(** * Backwards Compiler Correctness of Ultimate Speculative Load Hardening *)

(* get value of msf or callee variables given current register state *)
Definition msf_lookup (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  apply r msf.

Definition callee_lookup (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  apply r callee.

(* are we speculating (semantic level) *)
Definition ms_true (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in ms.

Section BCC.

Variable p: prog.
Definition tp : prog := uslh_prog p.

(* predicate for fold *)
Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

(* synchronizing point relation between src and tgt *)
(*
   checks: are label and offset both in-bounds?
   If proc block, add 2
   If not first instruction in block, accumulate extra steps from all previous insts
   For inst in source, always start from beginning of target decoration so we have access to all of it

*)

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

(* given a source register, sync with target register *)
(* can't handle callee here, not enough info if not speculating *)
Definition r_sync (r: reg) (ms: bool) : reg :=
  msf !-> N (if ms then 1 else 0); r.

(* given a source config, return the corresponding target config *)
Definition spec_cfg_sync (sc: spec_cfg) : option spec_cfg :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  match pc_sync pc with
  | Some pc => let tc := (pc, r_sync r ms, m, stk) in
                Some (tc, ct, ms)
  | _ => None
  end.

(* How many steps does it take for target program to reach the program point the source reaches in one step? *)
(* Here we just consider a single inst, not the slice of the block up to and including pc (in contrast to pc_sync) *)
(* The only insts that add steps are branch and call. *)
(* Branch: 2 extra insts when uslh-created block is jumped to, 1 extra otherwise *)
(* Call: assuming the attacker is in-bounds with both label and offset:  *)
(* if the block is a procedure block, then 3 extra steps are added (callee assign, ctarget, callee check) *)
(* Not sure about None if attacker jumps to a non-procedure block. *)
(* Currently this function doesn't address case where attacker jumps anywhere else in the program than the beginning of a procedure block *)
Definition steps_to_sync_point (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
    blk <- nth_error p (fst pc);;
    i <- nth_error (fst blk) (snd pc);;
    match (i, ds) with
    | (<{{branch _ to _}}>, [DBranch b]) => Some (if b then 3 else 2)
    | (<{{call e}}>, [DCall lo]) => let '(l, o) := lo in
                                      blk <- nth_error p l;;
                                      i <- nth_error (fst blk) o;;
                                      if (Bool.eqb (snd blk) true) && (o =? 0) then Some 4 else None
    | _ => Some 1
   end.

Definition get_reg (spc: spec_cfg) : reg :=
  let '(c, ct, ms) := spc in
  let '(pc, r, m, sk) := c in
  r.

Definition get_pc (spc: spec_cfg) : cptr :=
  let '(c, ct, ms) := spc in
  let '(pc, r, m, sk) := c in
  pc.

Ltac destruct_cfg c := destruct c as (c & ms); destruct c as (c & ct);
  destruct c as (c & sk); destruct c as (c & m); destruct c as (c & r);
  rename c into pc.

(* Termination: update this function to include our latest discussions

   need to specify what sort of termination we have:

  - if instruction is ret and stack is empty: normal
  - if ctarget is expected and the current instruction ≠ ctarget: fault
  - any other sort of termination: stuck/UB

*)

Definition is_fault (final: spec_cfg) : option bool :=
  let '(c, ct, ms) := final in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ctarget }}> => Some (if ct then false else true)
  | _ => Some false
  end.

Definition is_normal_termination (final: spec_cfg) : option bool :=
  let '(c, ct, ms) := final in
  let '(pc, rs, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{ ret }}> => Some (if seq.nilp sk then true else false)
  | _ => Some false
  end.

Definition is_stuck (final: spec_cfg) : option bool :=
  let '(c, ct, ms) := final in
  let '(pc, rs, m, sk) := c in
  _ <- p[[pc]];;
  match (is_fault final, is_normal_termination final) with
  | (Some false, Some false) => Some true
  | _ => Some false
  end.

Definition same_termination (sc2 tsc2 : spec_cfg) : bool :=
  let '(c, ct, ms) := sc2 in
  let '(pc, r, m, sk) := c in
  let '(tc, tct, tms) := tsc2 in
  let '(tpc, tr, tm, tsk) := tc in
  match (p[[pc]], p[[tpc]]) with
  | (Some i, Some ti) =>
      let iss := is_stuck sc2 in
      let ist := is_stuck tsc2 in
      let ins := is_normal_termination sc2 in
      let intg := is_normal_termination tsc2 in
      let ifs := is_fault sc2 in
      let ift := is_fault tsc2 in
      let stuck_match :=
        match (iss, ist) with
        | (Some bs1, Some bt1) => bs1 && bt1
        | _ => false
        end in
      let normal_match :=
        match (ins, intg) with
        | (Some bs2, Some bt2) => bs2 && bt2
        | _ => false
        end in
      let fault_match :=
        match (ifs, ift) with
        | (Some bs3, Some bt3) => bs3 && bt3
        | _ => false
        end in
          stuck_match || normal_match || fault_match
  | _ => false
  end.

(* Well-formedness properties  *)

(* All call directives must be in-bounds wrt label/program and offset/block *)
Definition well_formed_call_directives (ds: dirs) : Prop := 
  forall (d: direction) (pc: cptr), 
    In d ds -> 
    d = DCall pc ->
    exists blk, nth_error p (fst pc) = Some blk /\ exists i, nth_error (fst blk) (snd pc) = Some i.

(* Definition nonempty_arrs (ast : astate) :Prop :=
  forall a, 0 < length (ast a). *)

Definition nonempty_program : Prop := 
  0 < Datatypes.length p.

(* Last instruction in block must be either ret or jump *)
Definition nonempty_block (blk : (list inst * bool)) : Prop :=
  Datatypes.length (fst blk) <> 0.

Definition is_return_or_jump (i: inst) : bool :=
  match i with
  | <{{ ret }}> | <{{ jump _}}> => true 
  | _ => false 
  end.
Print prog.
Definition get_last_inst (blk: (list inst * bool)) : inst :=
  let len := Datatypes.length (fst blk) in 
  nth (len - 1) (fst blk) <{{ skip }}>.

Definition last_inst_ret_or_jump (blk: (list inst * bool)) : Prop :=
  is_return_or_jump (get_last_inst blk) = true.

Definition well_formed_block (blk : (list inst * bool)) : Prop :=
  last_inst_ret_or_jump blk.

(* BCC lemma for one single instruction *)
Lemma ultimate_slh_bcc_single_cycle : forall sc1 tsc1 tsc2 n ds os,
  nonempty_program ->
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) ->
  steps_to_sync_point tsc1 ds = Some n ->
  spec_cfg_sync sc1 = Some tsc1 ->
  well_formed_call_directives ds ->
  (forall (blk: (list inst * bool)), In blk p -> well_formed_block blk) ->
  uslh_prog p |- <(( tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( sc1 ))> -->i_ ds ^^ os <(( sc2 ))> /\ spec_cfg_sync sc2 = Some tsc2 /\ same_termination sc2 tsc2 = true.
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

