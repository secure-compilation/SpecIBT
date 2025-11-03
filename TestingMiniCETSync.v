Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From Stdlib Require Import String.

From SECF Require Import Utils.
From SECF Require Import ListMaps.
Require Import Stdlib.Classes.EquivDec.
From SECF Require Import TestingMiniCET.

Definition ideal_cfg :=  (cfg * bool)%type.

Definition ideal_step (p: prog) (ic: ideal_cfg) (ds:dirs) :option (ideal_cfg * dirs * obs) :=
  let '(c, ms) := ic in 
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with 
  | <{{branch e to l}}> => 
    if seq.nilp ds then
      trace "Branch: directions are empty!" None
    else
    d <- hd_error ds;;
    b' <- is_dbranch d;;
    n <- to_nat (eval r e);;
    let b := not_zero n in
    let ms' := ms || negb (Bool.eqb b b') in
    let pc' := if b' then (l, 0) else (pc+1) in
    ret ((((pc', r, m, sk), ms'), tl ds), [OBranch b])
  | <{{call e}}> =>
    if seq.nilp ds then
      trace "Call: directions are empty!" None
    else
    d <- hd_error ds;;
    pc' <- is_dcall d;;
    l <- to_fp (eval r e);;
    let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in
    ret ((((pc', r, m, (pc+1)::sk), ms'), tl ds), [OCall l])
  | _ =>
    co <- step p c;;
    let '(c', o) := co in
    ret ((c', ms), ds, o)
    end.


Fixpoint ideal_steps (f: nat) (p: prog) (ic: ideal_cfg) (ds: dirs)
  : option (ideal_cfg * dirs * obs) :=
  match f with 
  | S f' => 
      cdo1 <- ideal_step p ic ds;;
      let '(c1, ds1, o1) := cdo1 in
      cdo2 <- ideal_steps f' p c1 ds1;;
      let '(c2, ds2, o2) := cdo2 in
      ret (c2, ds2, o1++o2)
  | 0 =>
      None
  end.

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

Definition pc_sync (p: prog) (pc: cptr) : option cptr :=
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
Definition spec_cfg_sync (p: prog) (sc: spec_cfg) : option spec_cfg :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  match pc_sync p pc with
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
(* if the attacker jumps somewhere else, that means ct is true but we are not going to encounter ctarget inst *)
(* We've decided this should be a fault, so no steps are taken in this case. *)
Definition steps_to_sync_point (p: prog) (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
    blk <- nth_error p (fst pc);;
    i <- nth_error (fst blk) (snd pc);;
    match (i, ds) with
    | (<{{branch _ to _}}>, [DBranch b]) => Some (if b then 3 else 2)
    | (<{{call e}}>, [DCall lo]) => let '(l, o) := lo in
                                      blk <- nth_error p l;;
                                      i <- nth_error (fst blk) o;;
                                      if (Bool.eqb (snd blk) true) then Some 4 else None
    | _ => Some 1
   end.


QuickChick (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  let icfg1 := (ipc, rs1, m1, istk) in (* TODO: generate more meaningful stk (some number of possible call locations should do the trick)*)
  (* TODO: generate a valid program counter *)
  (* TODO: generate a valid synchronized state *)
  (* TODO: generate a single directive matching one ideal step *)
  (* Execute ideal 1 step, spec steps_to_sync_point steps, *)
  (* check that configs are in sync *Up to `callee`* *)

  checker tt )))).

