From Stdlib Require Import List
  Strings.String String
  Bool.Bool
  Arith.EqNat
  Arith.PeanoNat
  Lia.
Import Nat ListNotations.
Set Default Goal Selector "!".
From SECF Require Import 
    MapsFunctor
    MiniCET
    Machine
    Utils
    ListMaps.
Require Import Stdlib.Classes.EquivDec.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Export ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

Module Type Semantics(M : TMap).
  Parameter pc : Type.
  Definition reg := M.t val.
  Definition cfg : Type := ((pc * reg) * mem) * list pc.
  Definition spec_cfg : Type := (cfg * bool) * bool.
  Definition ideal_cfg : Type := cfg * bool.

  Definition dir := direction.
  Definition dirs := list dir.

  Parameter ipc : pc.
  Parameter istk : list pc.
  Parameter icfg : pc -> reg -> mem -> list pc -> cfg.

  Parameter eval : reg -> exp -> val.
  Parameter fetch : prog -> pc -> option inst.
  Parameter step : prog -> state cfg -> state cfg * obs.
  Parameter steps : nat -> prog -> state cfg -> state cfg * obs.
  Parameter spec_step : prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
  Parameter spec_steps : nat -> prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
End Semantics.

Module MiniCETSemantics (M : TMap) <: Semantics M.
Module Import Common := MiniCETCommon(M).

Definition reg := M.t val.
Definition cfg : Type := ((cptr*reg)*mem)*list cptr. (* (pc, register set, memory, stack frame) *)
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := cfg * bool.

Definition pc := cptr.
Definition ipc : cptr := (0, 0).
Definition istk : list cptr := [].
Definition icfg (ipc : pc) (ireg : reg) (mem : mem) (istk : list pc): cfg := 
  (ipc, ireg, mem, istk).

Definition dir := direction.
Definition dirs := dirs.
Definition fetch := MiniCET.fetch.

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
  | <{&l}> => FP l
  end.

Definition step (p:prog) (sc:state cfg) : (state cfg * obs) :=
    match sc with
    | S_Running c =>
        let '(pc, r, m, sk) := c in
        match p[[pc]] with
        | Some i =>
            match i with
            | <{{skip}}> | <{{ctarget}}> =>
              (S_Running (pc+1, r, m, sk), [])
            | <{{x:=e}}> =>
              (S_Running (pc+1, (x !-> eval r e; r), m, sk), [])
            | <{{branch e to l}}> =>
              match
                n <- to_nat (eval r e);;
                let b := not_zero n in
                ret ((if b then (l,0) else pc+1, r, m, sk), [OBranch b])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{jump l}}> =>
              (S_Running ((l,0), r, m, sk), [])
            | <{{x<-load[e]}}> =>
              match
                n <- to_nat (eval r e);;
                v' <- nth_error m n;;
                ret ((pc+1, (x !-> v'; r), m, sk), [OLoad n])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{store[e]<-e'}}> =>
              match
                n <- to_nat (eval r e);;
                ret ((pc+1, r, upd n m (eval r e'), sk), [OStore n])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{call e}}> =>
              match
                l <- to_fp (eval r e);;
                ret (((l,0), r, m, (pc+1)::sk), [OCall l])
              with
              | Some (c, o) => (S_Running c, o)
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
                  let pc' := if b' then (l, 0) else (pc+1) in
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
                  l <- to_fp (eval r e);;
                  let ms' := ms || negb ((fst pc' =? l) && (0 =? (snd pc')%nat)) in
                  (*! *)
                  ret ((S_Running ((pc', r, m, (pc+1)::sk), true, ms'), tl ds), [OCall l])
                  (*!! spec-call-no-set-ct *)
                  (*! ret ((S_Running ((pc', r, m, (pc+1)::sk), ct, ms'), tl ds), [OCall l]) *)
              with
              | None => untrace "call fail" (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{ctarget}}> =>
              match
                is_true ct;; (* ctarget can only run after call? (CET) Maybe not? *)
                (*! *)
                (ret (S_Running ((pc+1, r, m, sk), false, ms), ds, []))
                (*!! spec_ctarget_no_clear *)
                (*! (ret (S_Running ((pc+1, r, m, sk), ct, ms), ds, [])) *)
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

  Fixpoint spec_steps (f:nat) (p:prog) (sc: state spec_cfg) (ds: dirs)
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

End MiniCETSemantics.

Module MachineSemantics (M : TMap) <: Semantics M.
Module Import Common := MachineCommon(M).

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

Definition fetch := MiniCET.fetch.

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

End MachineSemantics.

Module IdealStepSemantics (Import ST : Semantics ListTotalMap with Definition pc := cptr).

Definition ideal_step (p: prog) (sic: state ideal_cfg) (ds: dirs) : (state ideal_cfg * dirs * obs) :=
  match sic with 
  | S_Running ic => 
      let '(c, ms) := ic in 
      let '(pc, r, m, sk) := c in
      match fetch p pc with 
        None => untrace "lookup fail" (S_Undef, ds, [])
      | Some i => 
          match i with 
            | <{{branch e to l}}> => 
              if seq.nilp ds then
                untrace "idealBranch: directions are empty!" (S_Undef, ds, [])
              else
                match
                  d <- hd_error ds;;
                  b' <- is_dbranch d;;
                  n <- to_nat (eval r e);;
                  let b := (negb ms) && not_zero n in
                  (*! *)
                  let ms' := ms || negb (Bool.eqb b b') in
                  (*!! ideal_branch_bad_update_ms *)
                  (*! let ms' := negb (Bool.eqb b b') in *)
                  let _ := I in (* just to separate the two mutants *)
                  (*! *)
                  let pc' := if b' then (l, 0) else (pc+1) in
                  (*!! ideal_branch_ignore_directive *)
                  (*! let pc' := if b then (l, 0) else (pc+1) in *)
                  ret ((S_Running ((pc', r, m, sk), ms'), tl ds), [OBranch b])
                with 
                | None => (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
            | <{{call e}}> =>
              if seq.nilp ds then
                untrace "idealCall: directions are empty!" (S_Undef, ds, [])
              else
                match
                  d <- hd_error ds;;
                  pc' <- is_dcall d;;
                  l <- (if ms then Some 0 else to_fp (eval r e));;
                  blk <- nth_error p (fst pc');;
                  (*! *)
                  if (snd blk && (snd pc' ==b 0)) then
                  (*!! ideal_call_no_check_target *)
                  (*! if true then *)
                    let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in
                    ret ((S_Running ((pc', r, m, (pc+1)::sk), ms'), tl ds), [OCall l])
                  else Some (S_Fault, ds, [OCall l])
                with 
                | None => (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
            | <{{x<-load[e]}}> =>
              match
                (*! *)
                let i := if ms then (ANum 0) else e in
                (*!! ideal-load-no-mask *)
                (*! let i := e in *)
                n <- to_nat (eval r i);;
                v' <- nth_error m n;;
                let c := (pc+1, (x !-> v'; r), m, sk) in
                ret (S_Running (c, ms), ds, [OLoad n])
              with 
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{store[e]<-e'}}> =>
              match
                (*! *)
                let i := if ms then (ANum 0) else e in
                (*!! ideal-store-no-mask *)
                (*! let i := e in *)
                n <- to_nat (eval r i);;
                let c:= (pc+1, r, upd n m (eval r e'), sk) in
                ret (S_Running (c, ms), ds, [OStore n])
              with 
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
          | _ =>
              match step p (S_Running c) with 
              | (S_Running c', o) => (S_Running (c', ms), ds, o)
              | (S_Undef, o) => (S_Undef, ds, o)
              | (S_Fault, o) => (S_Fault, ds, o)
              | (S_Term, o) => (S_Term, ds, o)
              end
          end
      end
  | s => (s, ds, [])
  end.

Fixpoint ideal_steps (f: nat) (p: prog) (sic: state ideal_cfg) (ds: dirs)
  : (state ideal_cfg * dirs * obs) :=
  match f with 
  | S f' => 
      match sic with 
      | S_Running ic =>
          let '(c1, ds1, o1) := ideal_step p sic ds in
          let '(c2, ds2, o2) := ideal_steps f' p c1 ds1 in
          (c2, ds2, o1++o2)
      | s => (s, ds, [])
      end
  | 0 =>
      (sic, ds, [])
  end.

End IdealStepSemantics.