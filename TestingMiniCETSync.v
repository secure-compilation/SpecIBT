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
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From Stdlib Require Import String.

From SECF Require Import Utils.
From SECF Require Import ListMaps.
Require Import Stdlib.Classes.EquivDec.
From SECF Require Import MiniCET.
From SECF Require Import TestingMiniCET.

(*! Section testing_sync *)

(* Same type as trace, so that you can easily "disable" trace using find+replace *)
Definition untrace {A : Type} (s : string) (a : A) : A := a.


Inductive state A : Type :=
  | S_Running (a: A)
  | S_Undef
  | S_Fault
  | S_Term.
Arguments S_Running {A} a.
Arguments S_Undef {A}.
Arguments S_Fault {A}.
Arguments S_Term {A}.

Instance state_Monad : Monad state.
Proof.
  constructor.
  - intros T t.
    now apply S_Running.
  - intros T U st f.
    destruct st eqn: H.
    + now apply f.
    + apply S_Undef.
    + apply S_Fault.
    + apply S_Term.
Defined.

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

Definition ideal_cfg :=  (cfg * bool)%type.

Definition ideal_step (p: prog) (sic: state ideal_cfg) (ds:dirs) : (state ideal_cfg * dirs * obs) :=
  match sic with 
  | S_Running ic => 
      let '(c, ms) := ic in 
      let '(pc, r, m, sk) := c in
      match p[[pc]] with 
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

Definition spec_step (p:prog) (ssc: state spec_cfg) (ds:dirs) : (state spec_cfg * dirs * obs) :=
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
                let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in
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

(* predicate for fold *)
Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

(* synchronizing point relation between src and tgt *)
(*
   checks: are label and offset both in-bounds?
   If proc block, add 2
   If not first instruction in block, accumulate extra steps from all previous insts
   For inst in source, always start from beginning of target decoration so we have access to all of it

*)

Definition pc_sync (p: prog) (pc: cptr) : option cptr :=
  blk <- nth_error p (fst pc);; (* label in bounds *)
  i <- nth_error (fst blk) (snd pc);; (* offset in bounds *)
  let acc1 := if (Bool.eqb (snd blk) true) then 2 else 0 in (* procedure blocks add 2 insts *)
    match (snd pc) with
    | 0 => Some ((fst pc), add (snd pc) acc1)
    | S _ => let insts_before_pc := (firstn (snd pc) (fst blk)) in (* accumulate extra insts from br and call insts preceding pc inst *)
               let acc2 := fold_left (fun acc (i: inst) =>
                 if (is_br_or_call i) then (add acc 1) else acc) insts_before_pc acc1 in
                   Some ((fst pc), add (snd pc) acc2)
    end.

(* given a source register, sync with target register *)
(* can't handle callee here, not enough info if not speculating *)
Definition r_sync (r: reg) (ms: bool) : reg :=
  msf !-> N (if ms then 1 else 0); r.

Fixpoint map_opt {S T} (f: S -> option T) l : option (list T):=
  match l with 
  | [] => Some []
  | a :: l' => a' <- f a;;
      l'' <- map_opt f l';; 
      ret (a' :: l'')
  end.

(* given a source config, return the corresponding target config *)
Definition spec_cfg_sync (p: prog) (ic: ideal_cfg): option spec_cfg :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  pc' <- pc_sync p pc;;
  (*! *)
  stk' <- map_opt (pc_sync p) stk;;
  (*!! spec_cfg_sync-no-stack *)
  (*! let stk' := stk in *)
  ret (pc', r_sync r ms, m, stk', false, ms).

(* How many steps does it take for target program to reach the program point the source reaches in one step? *)
Definition steps_to_sync_point (p: prog) (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
    (* check pc is well-formed *)
    blk <- nth_error p (fst pc);;
    i <- nth_error (fst blk) (snd pc);;
    match i with
    | <{{_ := _}}> => match p[[pc+1]] with
                      | Some i => match i with
                                  | <{{call _}}> => match ds with
                                                    | DCall lo :: _ => (* decorated call with correct directive *)
                                                                    let '(l, o) := lo in
                                                                    (* check attacker pc is well-formed *)
                                                                    blk <- nth_error p l;;
                                                                    i <- nth_error (fst blk) o;;
                                                                    (* 4 steps if procedure block *)
                                                                    if (Bool.eqb (snd blk) true) && (o =? 0) then 
                                                                    (*! *)
                                                                    Some 4 
                                                                    (*!! steps_to_sync_point-call-3 *)
                                                                    (*! Some 3 *)
                                                                    (*!! steps_to_sync_point-call-5 *)
                                                                    (*! Some 5 *)
                                                                    else None
                                                    | [] => untrace "empty directives for call" None
                                                    | _ => untrace "incorrect directive for call" None (* incorrect directive for call *)
                                                    end
                                  | _ => Some 1 (* assignment from source program, not decoration *)
                                  end
                      | None => Some 1 (* assignment from source program, last instruction in block *)
                      end
    | <{{ branch _ to _ }}> => (* branch decorations all come after the instruction itself, so this is the sync point *)
                               match ds with
                               (*! *)
                               | DBranch b :: _ => Some (if b then 3 else 2)
                               (*!! step_to_sync_point-branch-always-3 *)
                               (*! | DBranch b :: _ => Some 3 *)
                               (*!! step_to_sync_point-branch-always-2 *)
                               (*! | DBranch b :: _ => Some 2 *)
                               (*!! step_to_sync_point-branch-inverted *)
                               (*! | DBranch b :: _ => Some (if b then 2 else 3) *)
                               | [] => untrace "empty directives for branch" None
                               | _ => untrace "missing directive for branch" None
                               end
    | _ => Some 1 (* branch and call are the only instructions that add extra decorations *)
    end.

Definition gen_pc_from_prog (p: prog) : G cptr :=
  iblk <- choose (0, max 0 (Datatypes.length(p) - 1)) ;;
  let blk := nth_default ([],false) p iblk in
  off <- choose (0, max 0 (Datatypes.length(fst blk) - 1));;
  ret (iblk, off).

Fixpoint gen_call_stack_from_prog_sized n (p: prog) : G (list cptr) :=
  match n with 
  | 0 => ret []
  | S n' => l1 <- gen_pc_from_prog p;;
      oneOf (ret [l1] ;;; [liftM (cons l1) (gen_call_stack_from_prog_sized n' p)])
  end.

Definition gen_directive_from_ideal_cfg (p: prog) (pst: list nat) (ic: ideal_cfg) : G dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with 
  | Some i => 
      match i with 
      | <{{branch _ to _}}> => 
        d <- gen_dbr;;
        ret [d]
      | <{{call _}}> =>
        oneOf (
          d <- gen_dcall pst;;
          ret [d] ;;;
          [ pc <- gen_pc_from_prog p ;; ret [DCall pc] ]
        )
      | _ => ret []
      end
  | None => untrace "lookup error" (ret [])
  end.

Definition get_directive_for_seq_behaviour (p: prog) (pst: list nat) (ic: ideal_cfg) : dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with 
  | Some i => 
      match i with 
      | <{{branch e to _}}> => 
        match (to_nat (eval r e)) with 
        | None => []
        | Some n => [DBranch (not_zero n)]
        end
      | <{{call e}}> =>
        match (to_fp (eval r e)) with
        | None => []
        | Some l => [DCall (l, 0)]
        end
      | _ => []
      end
  | None => untrace "lookup error" ([])
  end.

Definition gen_directive_triggering_misspec (p: prog) (pst: list nat) (ic: ideal_cfg) : G dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with 
  | Some i => 
      match i with 
      | <{{branch e to _}}> => 
        match (to_nat (eval r e)) with 
        | None => ret []
        | Some n => ret [DBranch (negb (not_zero n))]
        end
      | <{{call e}}> =>
        match (to_fp (eval r e)) with
        | None => ret []
        | Some l => 
            let targets := (proc_hd pst) in
            let targets := filter (fun x => x <>b l) targets in
            match targets with 
            | [] => ret []
            | e::tl => t <- elems_ e (e::tl);;
                       ret [DCall (t, 0)]
            end
        end
      | _ => ret []
      end
  | None => untrace "lookup error" (ret [])
  end.

Scheme Equality for val.
Scheme Equality for observation.

Check (@equiv_decb cptr Logic.eq _ _).
(*Instance cptr_EqDec : EqDec cptr Logic.eq.*)
(*Proof.*)
  (*typeclasses eauto.*)
(*Qed.*)
Instance direction_EqDec : EqDec direction Logic.eq.
Proof.
  intros x y.
  destruct x, y.
  - destruct (b' == b'0).
    + left. now rewrite e.
    + right. now intros [= H].
  - right. discriminate.
  - right. discriminate.
  - destruct (lo == lo0).
    + left. now rewrite e.
    + right. now intros [= H].
Defined.

Compute ([DBranch true] <>b []).
Compute ([] <>b [DBranch true]).
(* Not quite sure why this is opaque, and why it does not seem to terminate in QuickChick tests...*)

Definition spec_cfg_eqb_up_to_callee (st1 st2 : spec_cfg) :=
  let '(pc1, r1, m1, sk1, c1, ms1) := st1 in
  let '(pc2, r2, m2, sk2, c2, ms2) := st2 in
  (pc1 ==b pc2)
  && (sk1 ==b sk2)
  && (c1 ==b c2) && (ms1 ==b ms2)
  && (m1 ==b m2)
  && pub_equivb (t_empty public) r1 (callee !-> (apply r1 callee) ; r2).

Compute ideal_step ([ ([ <{{skip}}> ], true) ]) (S_Running (((0,0)), (t_empty UV), [UV; UV; UV], [], false)) [].

(* Testing single-step compiler correctness *)
Definition single_step_cc := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack_from_prog_sized 3 p) (fun stk => 
  forAll (@arbitrary bool _) (fun ms =>
  let icfg := (pc, rs1, m1, stk, ms) in
  match (spec_cfg_sync p icfg) with
  | None => collect "hello"%string (checker tt)
  | Some tcfg => 
      forAll (gen_directive_from_ideal_cfg p pst icfg) (fun ds => 
      match ideal_step p (S_Running icfg) ds with 
      | (S_Fault, _, oideal) =>  
          match (steps_to_sync_point (uslh_prog p) tcfg ds) with 
          | None => match spec_steps 4 (uslh_prog p) (S_Running tcfg) ds with 
                    | (S_Fault, _, ospec) => (*untrace "fault"*) (checker (obs_eqb oideal ospec)) (* speculative execution should fail if it won't sync again *)
                    | _ => untrace "spec exec didn't fail"%string (checker false)
                    end
          | Some n => collect ("ideal step failed for "%string ++ show (p[[pc]]) ++ " but steps_to_sync_point was Some"%string)%string (checker tt)
          end
      | (S_Term, _, oideal) =>
          match (steps_to_sync_point (uslh_prog p) tcfg ds) with 
          | None => match spec_steps 1 (uslh_prog p) (S_Running tcfg) ds with 
                    | (S_Term, _, ospec) => (*untrace "term"*) (checker (obs_eqb oideal ospec))
                    | _ => untrace "spec exec didn't terminate"%string (checker false)
                    end
          | Some n => collect ("ideal step failed for "%string ++ show (p[[pc]]) ++ " but steps_to_sync_point was Some"%string)%string (checker tt)
          end
      | (S_Running icfg', _, oideal) => 
          match (steps_to_sync_point (uslh_prog p) tcfg ds) with 
          | None => untrace "Ideal step succeeds, but steps_to_sync_point undefined" (checker false)
          | Some n => match spec_steps n (uslh_prog p) (S_Running tcfg) ds with 
                      | (S_Running tcfg', _, ospec) => match (spec_cfg_sync p icfg') with
                                              | None => collect "sync fails "%string (checker tt)
                                              | Some tcfgref => match (spec_cfg_eqb_up_to_callee tcfg' tcfgref) with 
                                                                | true => (*untrace ("running " ++ show oideal ++ " / " ++ show ospec)*) (checker (obs_eqb oideal ospec))
                                                                | false => (*untrace (show tcfg' ++ "|||||" ++ show tcfgref)*) (checker false)
                                                                end
                                              end
                      | (_, ds, os) => untrace ("spec exec fails "%string ++ (show os) ++ show (uslh_prog p)) (checker false)
                      end
          end
      | _ => collect "ideal exec undef"%string (checker tt)
      end
      )
  end
  ))))))).

(*! QuickChick single_step_cc. *)
(* Results:
  Passed 10000 tests (105 discards due to S_Undef in ideal exec)

  If ideal execution faults or terminates, so does speculative execution, with the same observation.
  If ideal execution succeeds, so does speculative, and it reaches a point that is considered synchronized.
  If ideal execution is undefined, no requirement on spec.
*)

(* Testing (single-step) Gilles' lemma *)
Definition single_step_gilles := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_reg_wt c pst) (fun rs2 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  forAll (gen_wt_mem tm pst) (fun m2 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack_from_prog_sized 3 p) (fun stk => 
  let icfg1 := (pc, rs1, m1, stk, true) in
  let icfg2 := (pc, rs2, m2, stk, true) in
  forAll (gen_directive_from_ideal_cfg p pst icfg1) (fun ds => 
  match (ideal_step p (S_Running icfg1) ds) with 
  | (S_Running _, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Running _, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Undef, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Undef, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Fault, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Fault, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Term, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Term, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  end
  ))))))))).

(*! QuickChick single_step_gilles. *)

(* Testing (single-step) sequential behaviour *)
Definition single_step_seq_ideal := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack_from_prog_sized 3 p) (fun stk => 
  let cfg := (pc, rs1, m1, stk) in
  let icfg := (pc, rs1, m1, stk, false) in
  let ds := get_directive_for_seq_behaviour p pst icfg in
  match (step p (S_Running cfg)) with 
  | (S_Running _, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Running _, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not running" (checker false)
      end
  | (S_Undef, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Undef, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not undef" (checker false)
      end
  | (S_Fault, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Fault, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not fault" (checker false)
      end
  | (S_Term, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Term, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not term" (checker false)
      end
  end
  )))))).
(*! QuickChick single_step_seq_ideal. *)

(* Testing misspeculation-triggering steps *)
Definition single_step_trigger := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack_from_prog_sized 3 p) (fun stk => 
  let cfg := (pc, rs1, m1, stk) in
  let icfg := (pc, rs1, m1, stk, false) in
  forAll (gen_directive_triggering_misspec p pst icfg) (fun ds => 
  match (step p (S_Running cfg)) with 
  | (S_Running _, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Running icfg', _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker ((obs_eqb o1 o2) && (match ds with [] => true | _ => snd icfg' end)))
      | _ => untrace "not running" (checker false)
      end
  | (S_Undef, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Undef, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not undef" (checker false)
      end
  | (S_Fault, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Fault, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not fault" (checker false)
      end
  | (S_Term, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Term, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not term" (checker false)
      end
  end
  ))))))).
(*! QuickChick single_step_trigger. *)
