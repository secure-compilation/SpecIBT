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

(* legacy *)

Definition transpose {X : Type} (l : list (option X)) : option (list X) :=
  fold_right (fun ox ol =>
                match ox, ol with
                | Some x, Some l => Some (x :: l)
                | _, _ => None
                end) (Some nil) l.

Fixpoint coord_to_flat_idx {X} (ll: list (list X)) (c: nat * nat) : option nat :=
  let '(a, b) := c in
  match ll with
  | [] => None
  | l :: ls => match a with
             | 0 => if (b <? Datatypes.length l)%nat then Some b else None
             | S a' => match coord_to_flat_idx ls (a', b) with
                      | Some idx => Some (Datatypes.length l + idx)
                      | None => None
                      end
             end
  end.

Fixpoint flat_idx_to_coord {X} (ll: list (list X)) (idx: nat) : option (nat * nat) :=
  match ll with
  | [] => None
  | l :: ls =>
      let len := Datatypes.length l in
      if (idx <? len)%nat then Some (0, idx)
      else
        match flat_idx_to_coord ls (idx - len) with
        | Some (a', b') => Some (S a', b')
        | _ => None
        end
  end.

Lemma coord_flat_inverse
    A (ll: list (list A)) a b idx
    (CTI: coord_to_flat_idx ll (a, b) = Some idx) :
  flat_idx_to_coord ll idx = Some (a, b).
Proof.
  ginduction ll; i; ss.
  destruct ((idx <? Datatypes.length a)%nat) eqn:E.
  { des_ifs. eapply IHll in Heq. clear -E.
    exfalso. rewrite ltb_lt in E. lia. }
  des_ifs.
  - eapply IHll in Heq0.
    rewrite add_comm in Heq.
    rewrite add_sub in Heq. clarify.
  - eapply IHll in Heq0.
    rewrite add_comm in Heq.
    rewrite add_sub in Heq. clarify.
Qed.

Lemma flat_coord_inverse
    A (ll: list (list A)) a b idx
    (ITC: flat_idx_to_coord ll idx = Some (a, b)) :
  coord_to_flat_idx ll (a, b) = Some idx.
Proof.
  ginduction ll; ii; ss.
  destruct ((idx <? Datatypes.length a)%nat) eqn:E; clarify.
  rewrite ltb_ge in E.
  des_ifs.
  - eapply IHll in Heq0. clarify. f_equal. lia.
  - eapply IHll in Heq0. clarify.
Qed.

Definition pc_inj (p: prog) (pc: cptr) : option nat :=
  let fstp := map fst p in
  coord_to_flat_idx fstp pc.

Lemma coord_to_flat_idx_inject {X} (p: list (list X)) pc1 pc2 pc1' pc2'
    (DIFF: pc1 <> pc2)
    (INJ1: coord_to_flat_idx p pc1 = Some pc1')
    (INJ2: coord_to_flat_idx p pc2 = Some pc2') :
  pc1' <> pc2'.
Proof.
  ginduction p; ss; ii.
  { destruct pc1; ss. }
  des_ifs_safe. des_ifs.
  { rewrite ltb_lt in Heq. lia. }
  { rewrite ltb_lt in Heq0. lia. }
  assert ((n4, n2) <> (n3, n0)).
  { ii. eapply DIFF. inv H. auto. }
  exploit IHp; eauto. lia.
Qed.

Lemma pc_inj_inject p pc1 pc2 pc1' pc2'
    (DIFF: pc1 <> pc2)
    (INJ1: pc_inj p pc1 = Some pc1')
    (INJ2: pc_inj p pc2 = Some pc2') :
  pc1' <> pc2'.
Proof.
  unfold pc_inj in *.
  eapply coord_to_flat_idx_inject; eauto.
Qed.

Definition pc_inj_inv (p: prog) (pc: nat) : option cptr :=
  let fstp := map fst p in
  flat_idx_to_coord fstp pc.

Definition flat_fetch (p: prog) (pc: nat) : option inst :=
  match pc_inj_inv p pc with
  | Some pc' => fetch p pc'
  | _ => None (* out-of-bound code access *)
  end.

(* Sanity Check *)
(* lemma -> if pc is inbound -> pc_inj is a total function. *)
Lemma pc_inj_total p pc i
    (INBDD: fetch p pc = Some i) :
  exists pc', pc_inj p pc = Some pc'.
Proof.
Admitted.

Definition val_injectb (p: prog) (vsrc vtgt: val) : bool :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p (l, 0) with
                | Some n' => Nat.eqb n n'
                | None => false
                end
  | N n, N n' => Nat.eqb n n'
  | UV, _ => true
  | _, _ => false
  end.

Definition val_inject (p: prog) (vsrc vtgt: val) : Prop :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p (l, 0) with
                | Some n' => (n = n')%nat
                | None => False
                end
  | N n, N n' => (n = n')
  | UV, _ => True
  | _, _ => False
  end.

(** Block-based machine level semantics *)

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

Definition reg := M.t val.
Definition reg_init := M.init UV.

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

Definition cfg : Type := ((cptr*reg)*mem)*list cptr. (* (pc, register set, memory, stack frame) *)

Definition spec_cfg : Type := ((cfg * bool) * bool).

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

Definition ideal_cfg : Type := (cfg * bool)%type.

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

Module MiniC := MiniCETCommon(M).
Import MiniC.

Module MachineC := MachineCommon(M).
Import MachineC.

Definition regs := MiniC.reg.
Definition regt := MachineC.reg.

Definition reg_inject (p: prog) (r1: regs) (r2: regt) : Prop :=
  forall x, val_inject_s p (r1 ! x) (r2 ! x).

Lemma eval_binop_inject p o v1 v1' v2 v2'
    (INJ1: val_inject_s p v1 v1')
    (INJ2: val_inject_s p v2 v2') :
  val_inject_s p (eval_binop o v1 v2) (eval_binop o v1' v2').
Proof.
Admitted.

Lemma eval_inject p r1 r2 e1 e2
  (INJ: reg_inject p r1 r2)
  (TRANS: machine_exp e1 = e2) :
  val_inject p (MiniC.eval r1 e1) (MachineC.eval r2 e2).
Proof.
Admitted.

(* common simulation *)

End SimCommon.
