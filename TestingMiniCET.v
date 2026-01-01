(** * Testing MiniCET *)

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
Import MonadNotation.
From SECF Require Import TestingLib.
From SECF Require Import MiniCET TaintTrackingMiniCET MapsFunctor.

Module MCC := MiniCETCommon(ListTotalMap).
Module TS := TestingStrategies(MCC).
Module TT := TaintTracking(MCC).
Import MCC TS TT.

Definition gen_dbr : G direction :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G direction :=
  l <- (elems_ 0 (proc_hd pst));; ret (DCall (l, 0)).

Derive Show for direction.

(* Extract Constant defNumTests => "1000000". *)

(* check 0: load/store transformation creates basic blocks *)

Definition load_store_trans_basic_blk := TS.load_store_trans_basic_blk.

(*! QuickChick load_store_trans_basic_blk. *)

(* check 1: generated program is stuck-free. *)

Definition load_store_trans_stuck_free := TS.load_store_trans_stuck_free.

(*! QuickChick load_store_trans_stuck_free. *)

(* +++ Passed 10000 tests (6173 discards) *)

Definition no_obs_prog_no_obs := TS.no_obs_prog_no_obs.

(*! QuickChick no_obs_prog_no_obs. *)

(* check 3: implicit flow *)

Example implicit_flow_test p rs icfg
  (P: p = [([ IBranch (AId "x") 1; IJump 1 ], true); ([ IAsgn "y"%string (ANum 1); IRet], false)])
  (RS: rs = (N 0, [("x"%string, N 10); ("y"%string, N 0)]))
  (ICFG: icfg = (ipc, rs, [], [])):
  match taint_tracking 10 p icfg with
  | Some (obs, leaked_vars, _) =>
      existsb (String.eqb "x") leaked_vars
  | None => false
  end = true.
Proof.
  remember (taint_tracking 10 p icfg).
  subst p rs icfg. simpl in Heqo.
  subst. simpl. reflexivity.
Qed.

(* check 4: unused variables never leaked *)

Definition unused_var_no_leak_transform_load_store := 
  unused_var_no_leak (fun c tm p => transform_load_store_prog c tm p).

(*! QuickChick unused_var_no_leak_transform_load_store. *)

(* check 5: gen_pub_equiv_same_ty works *)

Definition gen_pub_equiv_same_ty := TS.gen_pub_equiv_same_ty.

(* check 6: generated register set is well-typed. *)

Definition gen_pub_equiv_is_pub_equiv := TS.gen_pub_equiv_is_pub_equiv.

(*! QuickChick gen_pub_equiv_is_pub_equiv. *)

Definition gen_reg_wt_is_wt := TS.gen_reg_wt_is_wt.

(*! QuickChick gen_reg_wt_is_wt. *)

(* check 5: gen_pub_mem_equiv_same_ty works *)

Definition gen_pub_mem_equiv_is_pub_equiv := TS.gen_pub_mem_equiv_is_pub_equiv.

(*! QuickChick gen_pub_mem_equiv_is_pub_equiv. *)

(* check 7: generated memory is well-typed. *)

Definition gen_mem_wt_is_wt := TS.gen_mem_wt_is_wt.

(*! QuickChick gen_mem_wt_is_wt. *)

(* check 8: non-interference *)

(** Safety Preservation *)

Definition test_ni_transform_load_store := 
  test_ni (fun c tm p => transform_load_store_prog c tm p).
(*! QuickChick test_ni_transform_load_store. *)

(* +++ Passed 1000000 tests (639813 discards) *)
(* Time Elapsed: 152.683837s *)

Definition test_safety_preservation_uslh := test_safety_preservation uslh_prog gen_dbr gen_dcall.

(*! QuickChick test_safety_preservation_uslh. *)

(* +++ Passed 1000000 tests (431506 discards) *)
(* Time Elapsed: 137.819446s *)

(** Testing Relative Security *)

Definition test_relative_security_uslh := test_relative_security uslh_prog gen_dbr gen_dcall.

(*! QuickChick test_relative_security_uslh. *)

(* +++ Passed 1000000 tests (0 discards) *)
(* Time Elapsed: 1308.843714s *)
