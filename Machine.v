(** * Define Machine *)

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

From SECF Require Import Utils.
From SECF Require Import MapsFunctor.
From SECF Require Import MiniCET.
From SECF Require Import sflib.

(* TODO: Machine.v is a common part. Need to change. *)

(* memory injection *)

(* mem only contains data. *)

(* 0 ~ length m - 1 : data area *)
(* length m ~ length m + length p : code area *)

(* Aux function : move to Utils.v *)

(** Block-based machine level semantics *)
Inductive ty : Type := TNum.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum => true
                               end.

Definition val_injectb_s (p: prog) (vsrc vtgt: val) : bool :=
  match vsrc, vtgt with
  | FP l, N n => Nat.eqb l n
  | N n, N n' => Nat.eqb n n'
  | UV, _ => true
  | _, _ => false
  end.

Definition val_inject_s (p: prog) (vsrc vtgt: val) : Prop :=
  if val_injectb_s p vsrc vtgt
  then True
  else False.

Module MachineCommon (M: TMap).

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

(* Definition prog := MiniCET.prog. *)
Definition reg := M.t val.
Definition reg_init := M.init UV.

Definition cfg : Type := ((cptr * reg)* mem) * list cptr. (* (pc, register set, memory, stack frame) *)
Definition spec_cfg : Type := ((cfg * bool) * bool).

Definition no_fp (r: reg) : Prop :=
  forall x, match (to_fp (r ! x)) with
      | Some _ => False
      | None => True
      end.

Fixpoint eval (st : reg) (e: exp) : val :=
  match e with
  | ANum n => N n
  | AId x => M.t_apply st x
  | ABin b e1 e2 => eval_binop b (eval st e1) (eval st e2)
  | <{b ? e1 : e2}> =>
      match to_nat (eval st b) with (* Can't branch on function pointers *)
      | Some n1 => if not_zero n1 then eval st e1 else eval st e2
      | None => UV
      end
  | <{&l}> => N l
  end.

(* ret with empty stackframe *)
Definition final_spec_cfg (p: prog) (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in
  let '(pc, rs, m, stk) := c in
  match p[[pc]] with
  | Some i => match i with
             | IRet => if seq.nilp stk then true else false (* Normal Termination *)
             | ICTarget => if ct
                          then false (* Call target block: Unreachable *)
                          else true (* TODO: Do we need to distinguish fault and normal termination? *)
             | _ => false
             end
  | None => false
  end.

End MachineCommon.

(* transformation *)

Fixpoint machine_exp (e: exp) : exp :=
  match e with
  | ANum _ | AId _ => e
  | FPtr l => ANum l
  | ABin o e1 e2 => ABin o (machine_exp e1) (machine_exp e2)
  | ACTIf e1 e2 e3 => ACTIf (machine_exp e1) (machine_exp e2) (machine_exp e3)
  end.

Definition machine_inst (i: inst) : inst :=
  match i with
  | <{{branch e to l}}> => <{{ branch (machine_exp e) to l }}>
  | ICall e => ICall (machine_exp e)
  | IAsgn x e => IAsgn x (machine_exp e)
  | ILoad x e => ILoad x (machine_exp e)
  | IStore e1 e2 => IStore (machine_exp e1) (machine_exp e2)
  | _ => i
  end.

Definition machine_blk (blk: (list inst * bool)) : (list inst * bool) :=
  let b := map (machine_inst) (fst blk) in
  (b, snd blk).

Definition machine_prog (p: prog) : prog :=
  map (machine_blk) p.

Module SimCommon (M: TMap).

Module Export MiniC := MiniCETCommon(M).

Module Export MachineC := MachineCommon(M).

Definition minicet_val_to_machine (v : val) := match v with
  | N x => N x
  | FP x => N x
  | UV => UV
  end.

Definition regs := MiniC.reg.
Definition regt := MachineC.reg.

Definition machine_rctx (r : MiniC.reg) : MachineC.reg :=
  M.t_map_values minicet_val_to_machine r.

Definition machine_mem (m : mem) : mem :=
  map minicet_val_to_machine m.

End SimCommon.
