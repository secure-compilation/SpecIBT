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

Definition step (p:prog) (sc:state cfg) : (state cfg * obs) :=
  match sc with
  | S_Running c =>
      let '(pc, r, m, sk) := c in
      match flat_fetch p pc with
      | Some i =>
          match i with
          | <{{skip}}> | <{{ctarget}}> =>
            (S_Running (add pc 1, r, m, sk), [])
          | <{{x:=e}}> =>
            (S_Running (add pc 1, (x !-> eval r e; r), m, sk), [])
          | <{{branch e to l}}> =>
              match to_nat (eval r e) with
              | Some n => let b := not_zero n in
                         (S_Running (if b then l else add pc 1, r, m, sk), [OBranch b])
              | None => (S_Undef, [])
              end
          | <{{jump l}}> =>
            (S_Running (l, r, m, sk), [])
          | <{{x<-load[e]}}> =>
              match to_nat (eval r e) with
              | Some n => match nth_error m n with
                         | Some v' => (S_Running (add pc 1, (x !-> v'; r), m, sk), [OLoad n])
                         | None => (S_Undef, [])
                         end
              | None => (S_Undef, [])
              end
          | <{{store[e]<-e'}}> =>
              match to_nat (eval r e) with
              | Some n => (S_Running (add pc 1, r, (upd n m (eval r e')), sk), [OStore n])
              | None => (S_Undef, [])
              end
          | <{{call e}}> =>
              match to_nat (eval r e) with
              | Some l => (S_Running (l, r, m, (add pc 1)::sk), [OCall l]) (* Checking needed *)
              | None => (S_Undef, [])
              end
          | <{{ret}}> =>
            match sk with
            | [] => (S_Term, [])
            | pc'::stk' => (S_Running (pc', r, m, stk'), [])
            end
          end
      | None => (S_Fault, [])
      end
  | s => (s, [])
  end.

(* Morally state+output monad hidden in here: step p >> steps f' p  *)
Fixpoint steps (f:nat) (p:prog) (sc: state cfg) : (state cfg * obs) :=
  match f with
  | S f' =>
      match sc with
      | S_Running c =>
          let '(c1, o1) := step p sc in
          let '(c2, o2) := steps f' p c1 in
          (c2, o1++o2)
      | s => (s, [])
      end
  | 0 =>
      (sc, [])
  end.

Definition spec_step (p:prog) (ssc: state spec_cfg) (ds:dirs) : (state spec_cfg * dirs * obs) :=
  match ssc with
  | S_Running sc =>
      let '(c, ct, ms) := sc in
      let '(pc, r, m, sk) := c in
      match flat_fetch p pc with
      | None => untrace "lookup fail" (S_Undef, ds, [])
      | Some i =>
          match i with
          | <{{branch e to l}}> =>
            if ct then (*untrace "ct set at branch"*) (S_Fault, ds, []) else
            match
              if seq.nilp ds then
                untrace "Branch: Directions are empty!" None
              else
                d <- hd_error ds;;
                b' <- is_dbranch d;;
                n <- to_nat (eval r e);;
                let b := not_zero n in
                let ms' := ms || negb (Bool.eqb b b') in
                let pc' := if b' then l else (add pc 1) in (* add check exists b, injection l = (b, 0) *)
                ret ((S_Running ((pc', r, m, sk), ct, ms'), tl ds), [OBranch b])
            with
            | None => untrace "branch fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{call e}}> =>
            if ct then (*untrace "ct set at call"*) (S_Fault, ds, []) else
            match
              if seq.nilp ds then
                untrace "Call: Directions are empty!" None
              else
                d <- hd_error ds;;
                pc' <- is_dcall d;;
                l <- to_nat (eval r e);; (* add check exists b, injection l = (b, 0). call target flag (snd block) also shold be checked? *)
                let ms' := ms || negb ((pc' =? l)%nat) in
                ret ((S_Running ((pc', r, m, (add pc 1)::sk), true, ms'), tl ds), [OCall l])
            with
            | None => untrace "call fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{ctarget}}> =>
            match
              is_true ct;; (* ctarget can only run after call? (CET) Maybe not? *)
              (ret (S_Running ((add pc 1, r, m, sk), false, ms), ds, []))
            with
            | None => untrace "ctarget fail!" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | _ =>
            if ct then (*untrace ("ct set at " ++ show i)*) (S_Fault, ds, [])
            else
              match step p (S_Running c) with
              | (S_Running c', o) => (S_Running (c', false, ms), ds, o)
              | (S_Undef, o) => (S_Undef, ds, o)
              | (S_Fault, o) => (S_Fault, ds, o)
              | (S_Term, o) => (S_Term, ds, o)
              end
          end
      end
  | s => (s, ds, [])
  end.

Fixpoint spec_steps (f:nat) (p:prog) (sc: state spec_cfg) (ds:dirs)
  : (state spec_cfg * dirs * obs) :=
  match f with
  | S f' =>
      match sc with
      | S_Running c =>
          let '(c1,ds1,o1) := spec_step p sc ds in
          let '(c2,ds2,o2) := spec_steps f' p c1 ds1 in
          (c2,ds2,o1++o2)
      | s => (s, ds, [])
      end
  | 0 =>
      (sc, ds, []) (* JB: executing for 0 steps should be just the identity... *)
      (* None *) (* Q: Do we need more precise out-of-fuel error here? *)
  end.
