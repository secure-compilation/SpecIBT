(** * Define Linearized Machine *)

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

(* m : mem *)
(* 0 ~ length m - 1 : data area *)
(* 0 ~ length p - 1 : code area *)

(** Linearized machine level semantics *)
Inductive ty : Type := TNum.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum => true
                               end.

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

Definition pc_inj (p: MiniCET.prog) (pc: MiniCET.cptr) : option nat :=
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

Definition pc_inj_inv (p: MiniCET.prog) (pc: nat) : option cptr :=
  let fstp := map fst p in
  flat_idx_to_coord fstp pc.

Definition flat_fetch (p: MiniCET.prog) (pc: nat) : option inst :=
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
  unfold pc_inj, MiniCET.fetch in *. destruct pc as (l & o).
  ginduction p; ss; ii; clarify.
  - rewrite nth_error_nil in INBDD; clarify.
  - rewrite nth_error_cons in INBDD.
    destruct l as [|l'] eqn:Hl.
    + assert (nth_error (fst a) o <> None) by (unfold not; i; clarify).
      rewrite nth_error_Some in H. 
      rewrite <- ltb_lt in H. rewrite H.
      exists o. auto.
    + specialize IHp with (l:=l') (o:=o) (i:=i).
      unfold MiniCET.fetch in IHp. ss. 
      apply IHp in INBDD. des. rewrite INBDD.
      exists (Datatypes.length (fst a) + pc'). auto.
Qed.

Definition prog := list inst.

Definition fetch (p: prog) (pc: nat) : option inst :=
  nth_error p pc.

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

Definition val_injectb (p: MiniCET.prog) (vsrc vtgt: val) : bool :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p (l, 0) with
                | Some n' => Nat.eqb n n'
                | None => false
                end
  | N n, N n' => Nat.eqb n n'
  | UV, _ => true
  | _, _ => false
  end.

Definition val_inject (p: MiniCET.prog) (vsrc vtgt: val) : Prop :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p (l, 0) with
                | Some n' => (n = n')%nat
                | None => False
                end
  | N n, N n' => (n = n')
  | UV, _ => True
  | _, _ => False
  end.

(* To use common testing framework, we need to follow then common
   semantics for testing (defined in MiniCET.v). But before that,
   we need to parameterize the program in the common semantics.

   I expect some troubleshooting will be needed, but to handle all
   all the related issues at once, I've just defined the semantics for now. *)

Module LinearCommon (M: TMap).

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

Definition reg := M.t val.
Definition reg_init := M.init UV.
Definition dir := direction.
Definition dirs := dirs.
Definition pc := nat.
Definition cfg : Type := ((pc * reg)* mem) * list pc. (* (pc, register set, memory, stack frame) *)
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := (cfg * bool)%type.
Definition ipc: pc := 0.
Definition istk: list pc := [].
Definition icfg (ipc : pc) (ireg : reg) (mem : mem) (istk : list pc): cfg := 
  (ipc, ireg, mem, istk).

Definition fetch := Linear.fetch.

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
  match fetch p pc with
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
      match fetch p pc with
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
  | 0 => (sc, [])
  end.

Definition spec_step (p:prog) (ssc: state spec_cfg) (ds: dirs) : (state spec_cfg * dirs * obs) :=
  match ssc with
  | S_Running sc =>
      let '(c, ct, ms) := sc in
      let '(pc, r, m, sk) := c in
      match fetch p pc with
      | None => untrace "lookup fail" (S_Undef, ds, [])
      | Some i =>
          match i with
          | <{{branch e to l}}> =>
              if ct
              then (*untrace "ct set at branch"*) (S_Fault, ds, [])
              else
                match
                  if seq.nilp ds then
                    untrace "Branch: Directions are empty!" None
                  else
                    d <- hd_error ds;;
                    b' <- is_dbranch d;;
                    n <- to_nat (eval r e);;
                    let b := not_zero n in
                    let ms' := ms || negb (Bool.eqb b b') in
                    let pc' := if b' then l else (add pc 1) in
                    ret ((S_Running ((pc', r, m, sk), ct, ms'), tl ds), [OBranch b])
                with
                | None => untrace "branch fail" (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
          | <{{call e}}> =>
              if ct
              then (*untrace "ct set at call"*) (S_Fault, ds, [])
              else
                match
                  if seq.nilp ds then
                    untrace "Call: Directions are empty!" None
                  else
                    d <- hd_error ds;;
                    pc' <- is_dcall d;;
                    l <- to_nat (eval r e);;
                    let ms' := ms || negb ((pc' =? l)%nat) in
                    ret ((S_Running ((pc', r, m, (add pc 1)::sk), true, ms'), tl ds), [OCall l])
                with
                | None => untrace "call fail" (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
          | <{{ctarget}}> =>
              match
                is_true ct;;
                (ret (S_Running ((add pc 1, r, m, sk), false, ms), ds, []))
              with
              | None => untrace "ctarget fail!" (S_Fault, ds, [])
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
  | 0 => (sc, ds, [])
          (* None *)
    end.

End LinearCommon.

(* transformation *)

Fixpoint machine_exp (p: MiniCET.prog) (e: exp) : option exp :=
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

Definition machine_inst (p: MiniCET.prog) (i: inst) : option inst :=
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

Definition machine_blk (p: MiniCET.prog) (blk: (list inst * bool)) : option (list inst) :=
  let ob := map (machine_inst p) (fst blk) in
  transpose ob.

Definition _machine_prog  (p_ctx: MiniCET.prog) (p: MiniCET.prog) : option prog :=
  let op := map (machine_blk p_ctx) p in
  let op' := transpose op in
  match op' with
  | Some lp => Some (List.concat lp)
  | _ => None
  end.

Definition machine_prog (p: MiniCET.prog) : option prog :=
  _machine_prog p p.

Module SimCommon (M: TMap).

Module MiniC := MiniCETCommon(M).
Import MiniC.

Module LinearC := LinearCommon(M).
Import LinearC.

Definition regs := MiniC.reg.
Definition regt := LinearC.reg.

Definition reg_inject (p: MiniCET.prog) (r1: regs) (r2: regt) : Prop :=
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
  val_inject p (MiniC.eval r1 e1) (LinearC.eval r2 e2).
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

