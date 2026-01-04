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

From SECF Require Import TestingLib.
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

Module MachineCommon (M: TMap) <: Semantics M.

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

(* Definition prog := MiniCET.prog. *)
Definition reg := M.t val.
Definition reg_init := M.init UV.

Definition dir := direction.
Definition dirs := dirs.
Definition pc := cptr.
Definition cfg : Type := ((pc * reg)* mem) * list pc. (* (pc, register set, memory, stack frame) *)
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := (cfg * bool)%type.
Definition ipc: pc := (0, 0).
Definition istk: list pc := [].
Definition icfg (ipc : pc) (ireg : reg) (mem : mem) (istk : list pc): cfg := 
  (ipc, ireg, mem, istk).

Definition fetch := fetch.

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

Definition step (p:prog) (sc:state cfg) : (state cfg * obs) :=
  match sc with
  | S_Running c =>
      let '(pc, r, m, sk) := c in
      match p[[pc]] with
      | Some i =>
          match i with
          | <{{skip}}> | <{{ctarget}}> =>
            (S_Running (pc + 1, r, m, sk), [])
          | <{{x:=e}}> =>
            (S_Running (pc + 1, (x !-> eval r e; r), m, sk), [])
          | <{{branch e to l}}> =>
              match to_nat (eval r e) with
              | Some n => let b := not_zero n in
                        (S_Running (if b then (l, 0) else pc + 1, r, m, sk), [OBranch b])
              | None => (S_Undef, [])
              end
          | <{{jump l}}> =>
            (S_Running ((l, 0), r, m, sk), [])
          | <{{x<-load[e]}}> =>
              match to_nat (eval r e) with
              | Some n => match nth_error m n with
                        | Some v' => (S_Running (pc + 1, (x !-> v'; r), m, sk), [OLoad n])
                        | None => (S_Undef, [])
                        end
              | None => (S_Undef, [])
              end
          | <{{store[e]<-e'}}> =>
              match to_nat (eval r e) with
              | Some n => (S_Running (pc + 1, r, (upd n m (eval r e')), sk), [OStore n])
              | None => (S_Undef, [])
              end
          | <{{call e}}> =>
              match to_nat (eval r e) with
              | Some l => (S_Running (l, 0, r, m, (pc + 1)::sk), [OCall l]) (* Checking needed *)
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

Definition spec_step (p:prog) (ssc: state spec_cfg) (ds: dirs) : (state spec_cfg * dirs * obs) :=
  match ssc with
  | S_Running sc =>
      let '(c, ct, ms) := sc in
      let '(pc, r, m, sk) := c in
      match p[[pc]] with
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
                let pc' := if b' then (l, 0) else (pc + 1) in
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
                l <- to_nat (eval r e);;
                let ms' := ms || negb ((fst pc' =? l)%nat && (snd pc' =? 0)%nat) in
                ret ((S_Running ((pc', r, m, (pc + 1)::sk), true, ms'), tl ds), [OCall l])
            with
            | None => untrace "call fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{ctarget}}> =>
            match
              is_true ct;;
              (ret (S_Running ((pc + 1, r, m, sk), false, ms), ds, []))
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
