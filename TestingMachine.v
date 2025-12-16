Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Classes.EquivDec.
From Stdlib Require Import String.

Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

From SECF Require Import TestingLib.
From SECF Require Import Utils.
From SECF Require Import ListMaps MapsFunctor.
From SECF Require Import MiniCET Machine.
From SECF Require Import TestingMiniCET.
From SECF Require Import sflib.

Import MonadNotation.
Local Open Scope monad_scope.

(*! Section testing_machine_ETE *)

Inductive ty : Type := | TNum.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum => true
                               end.

(* Executable Semantics for testing *)

Module MCC := MachineCommon(ListTotalMap).
Import MCC.

(* Find the condition that make machine_prog total function. I guess its wf. *)
(* Port existing tests from TestingMiniCET and Define some sanity checks for machine langauge. *)
(* Check every branches and jumps jump to the head of some block (If, machine program is generated from MiniCET program) *)

Definition wf_jmp_label (p:prog) (l:nat) : bool :=
  match pc_inj_inv p l with
  | Some (b, 0) => match nth_error p b with
                  | Some (_,is_proc) => negb is_proc
                  | None => false
                  end
  | _ => false
  end.

Definition wf_jmp_inst (p:prog) (i : inst) : bool :=
  match i with
  | <{{branch e to l}}> => wf_jmp_label p l
  | <{{jump l}}> => wf_jmp_label p l
  | _ => true
  end.

Definition wf_jmp_blk (p:prog) (blb : list inst * bool) : bool :=
  forallb (wf_jmp_inst p) (fst blb).

Definition wf_jmp (p:prog) : bool :=
  forallb (wf_jmp_blk p) p.

(* YH: machine_prog is a total function. *)
(* Definition test_machine_prog_total_from_minicet := *)
(*   (forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) => *)
(*   let p' := transform_load_store_prog c tm p in *)
(*   let harden := uslh_prog p' in *)
(*   is_some (machine_prog harden))). *)

Definition test_machine_branch_from_wf_minicet :=
  (forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p' := transform_load_store_prog c tm p in
  let harden := uslh_prog p' in
  wf_jmp (machine_prog harden))).

(*! QuickChick test_machine_prog_total_from_minicet. *)

(*! QuickChick test_machine_branch_from_wf_minicet. *)
