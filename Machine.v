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

(* From stdpp Require Import stringmap. *)

Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.

From SECF Require Import TestingLib.
From SECF Require Import Utils.
From SECF Require Import ListMaps.
From SECF Require Import MiniCET.
From SECF Require Import sflib.

(* TODO: change reg to some better Map. *)
(* cfg for sequential semantics: (pc, register set, memory, stack frame) *)
Definition cfg : Type := ((nat * reg) * mem) * list nat.

(* mem only contains data. *)

(* 0 ~ length m : data area *)
(* length m ~ length m + length p : code area *)

Definition wf_mem (m: mem) : Prop :=
  Forall (fun x => match x with
                | FP _ => False
                | _ => True
                end) m.


(* memory injection *)

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

(* lemma -> if pc is inbound -> pc_inj is a total function. *)
Definition pc_inj (p: prog) (pc: cptr) : option nat :=
  let fstp := map fst p in
  coord_to_flat_idx fstp pc.

Definition pc_inj_inv (p: prog) (pc: nat) : option cptr :=
  let fstp := map fst p in
  flat_idx_to_coord fstp pc.

Definition flat_fetch (p: prog) (pc: nat) : option inst :=
  match pc_inj_inv p pc with
  | Some pc' => fetch p pc'
  | _ => None (* out-of-bound *)
  end.

(* Sanity Check *)

Lemma pc_inj_total p pc i
    (INBDD: fetch p pc = Some i) :
  exists pc', pc_inj p pc = Some pc'.
Proof.
Admitted.

Variant initial_cfg_seq (p: prog) : cfg -> Prop :=
| initial_cfg_seq_intro pc r m stk
    (STK: stk = [])
    (* length m ~ length m + length p : code area *)
    (PC: pc = Datatypes.length m) :
  initial_cfg_seq p (pc, r, m, stk)
.

Variant final_cfg_seq (p: prog) : cfg -> Prop :=
| final_cfg_seq_intro pc r m stk
    (STK: stk = [])
    (FETCH: flat_fetch p pc = Some IRet) :
  final_cfg_seq p (pc, r, m, stk)
.

(* Executable Semantics *)

Definition step (p:prog) (c:cfg) : option (cfg * obs) :=
  let '(pc, r, m, sk) := c in
  match flat_fetch p pc with
  | Some i =>
      match i with
      | <{{skip}}> | <{{ctarget}}> =>
        ret ((add pc 1, r, m, sk), [])
      | <{{x:=e}}> =>
        ret ((add pc 1, (x !-> eval r e; r), m, sk), [])
      | <{{branch e to l}}> => (* Now, l is pc *)
        n <- to_nat (eval r e);;
        let b := not_zero n in
        if b
        then ret ((l, r, m, sk), [OBranch b])
        else ret ((add pc 1, r, m, sk), [OBranch b])
      | <{{jump l}}> =>
          ret ((l, r, m, sk), [])
      | <{{x<-load[e]}}> =>
        n <- to_nat (eval r e);;
        v' <- nth_error m n;;
        ret ((add pc 1, (x !-> v'; r), m, sk), [OLoad n])      
      | <{{store[e]<-e'}}> =>
        n <- to_nat (eval r e);;
        ret ((add pc 1, r, (upd n m (eval r e')), sk), [OStore n])
      | <{{call e}}> =>
        l <- to_nat (eval r e);;
        ret ((l, r, m, (add pc 1)::sk), [OCall l])
      | <{{ret}}> =>
        pc' <- hd_error sk;;
        ret ((pc', r, m, tl sk), [])
      end
  | _ => None
  end.

(* Semantics *)


