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

Inductive direction : Type :=
| DBranch (b':bool)
| DCall (l:nat).

Definition dirs := list direction.

Definition is_dbranch (d:direction) : option bool :=
  match d with
  | DBranch b => Some b
  | _ => None
  end.

Definition is_dcall (d:direction) : option nat :=
  match d with
  | DCall pc => Some pc
  | _ => None
  end.

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

Definition cfg : Type := ((nat*reg)*mem)*list nat. (* (pc, register set, memory, stack frame) *)

Definition spec_cfg : Type := ((cfg * bool) * bool).

(* ret with empty stackframe *)
Definition final_spec_cfg (p: prog) (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in
  let '(pc, rs, m, stk) := c in
  match flat_fetch p pc with
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

Fixpoint machine_exp (p: prog) (e: exp) : option exp :=
  match e with
  | ANum _ | AId _ => Some e
  | FPtr l => match pc_inj p (l, 0) with
             | Some l' => Some (ANum l')
             | None => None
             end
  | ABin o e1 e2 => match machine_exp p e1, machine_exp p e2 with
                   | Some e1', Some e2' => Some (ABin o e1' e2')
                   | _, _ => None
                   end
  | ACTIf e1 e2 e3 => match machine_exp p e1, machine_exp p e2, machine_exp p e3 with
                     | Some e1', Some e2', Some e3' => Some (ACTIf e1' e2' e3')
                     | _, _, _ => None
                     end
  end.

Definition machine_inst (p: prog) (i: inst) : option inst :=
  match i with
  | <{{branch e to l}}> =>
    match machine_exp p e, pc_inj p (l, 0) with
    | Some e', Some l' => Some <{{ branch e' to l' }}>
    | _, _ => None
    end
  | <{{jump l}}> =>
    match pc_inj p (l, 0) with
    | Some l' => Some <{{ jump l' }}>
    | _ => None
    end
  | ICall e =>
    match machine_exp p e with
    | Some e' => Some (ICall e')
    | _ => None
    end
  | IAsgn x e =>
    match machine_exp p e with
    | Some e' => Some (IAsgn x e')
    | _ => None
    end
  | ILoad x e =>
    match machine_exp p e with
    | Some e' => Some (ILoad x e')
    | _ => None
    end
  | IStore e1 e2 =>
    match machine_exp p e1, machine_exp p e2 with
    | Some e1', Some e2' => Some (IStore e1' e2')
    | _, _ => None
    end
  | ISkip | IRet | ICTarget => Some i
  end.

Definition transpose {X : Type} (l : list (option X)) : option (list X) :=
  fold_right (fun ox ol =>
                match ox, ol with
                | Some x, Some l => Some (x :: l)
                | _, _ => None
                end) (Some nil) l.

Definition machine_blk (p: prog) (blk: (list inst * bool)) : option (list inst * bool) :=
  let ob := map (machine_inst p) (fst blk) in
  match transpose ob with
  | Some ob' => Some (ob', snd blk)
  | _ => None
  end.

Definition machine_prog (p: prog) : option prog :=
  let op := map (machine_blk p) p in
  transpose op.

Module SimCommon (M: TMap).

Module MiniC := MiniCETCommon(M).
Import MiniC.

Module MachineC := MachineCommon(M).
Import MachineC.

Definition regs := MiniC.reg.
Definition regt := MachineC.reg.

Definition reg_inject (p: prog) (r1: regs) (r2: regt) : Prop :=
  forall x, val_inject p (r1 ! x) (r2 ! x).

Lemma eval_binop_inject p o v1 v1' v2 v2'
    (INJ1: val_inject p v1 v1')
    (INJ2: val_inject p v2 v2') :
  val_inject p (eval_binop o v1 v2) (eval_binop o v1' v2').
Proof.
  red in INJ1, INJ2. des_ifs. destruct o; ss.
  f_equal.
  destruct (Nat.eq_dec l0 l); clarify.
  { do 2 rewrite Nat.eqb_refl. auto. }
  hexploit pc_inj_inject; [| eapply Heq0| eapply Heq|].
  { ii. eapply n. inv H. auto. }
  ii. rewrite <- Nat.eqb_neq in n, H. rewrite n, H. auto.
Qed.

Lemma eval_inject p r1 r2 e1 e2
  (INJ: reg_inject p r1 r2)
  (TRANS: machine_exp p e1 = Some e2) :
  val_inject p (MiniC.eval r1 e1) (MachineC.eval r2 e2).
Proof.
  ginduction e1; ss; ii; clarify.
  - des_ifs. ss.
    hexploit IHe1_1; eauto. intros INJ1. hexploit IHe1_2; eauto. intros INJ2.
    eapply (eval_binop_inject p o); eauto.
  - des_ifs_safe. hexploit IHe1_1; eauto. i. ss.
    destruct (MiniC.eval r1 e1_1); ss; auto. des_ifs_safe. ss. clarify.
    des_ifs.
    + hexploit IHe1_2; eauto.
    + hexploit IHe1_3; eauto.
  - des_ifs. ss. clarify.
Qed.

(* common simulation *)

End SimCommon.
