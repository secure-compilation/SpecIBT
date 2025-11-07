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

(* ideal_cfg = (cfg, ms) *)
Definition ideal_cfg := (cfg * bool)%type.

Definition ideal_step (p: prog) (ic: ideal_cfg) (ds:dirs) :option (ideal_cfg * dirs * obs) :=
  let '(c, ms) := ic in 
  let '(pc, r, m, sk) := c in
  match p[[pc]] with 
    None => trace "lookup fail" None
  | Some i => 
  match i with 
  | <{{branch e to l}}> => 
    if seq.nilp ds then
      trace "idealBranch: directions are empty!" None
    else
    d <- hd_error ds;;
    b' <- is_dbranch d;;
    n <- to_nat (eval r e);;
    let b := not_zero n in
    let ms' := ms || negb (Bool.eqb b b') in
    let pc' := if b' then (l, 0) else (pc+1) in
    ret ((((pc', r, m, sk), ms'), tl ds), [OBranch b])
  | <{{call e}}> =>
    if seq.nilp ds then
      trace "idealCall: directions are empty!" None
    else
    d <- hd_error ds;;
    pc' <- is_dcall d;;
    l <- to_fp (eval r e);;
    let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in
    ret ((((pc', r, m, (pc+1)::sk), ms'), tl ds), [OCall l])
  | <{{x<-load[e]}}> =>
      let i := if ms then (ANum 0) else e in
      n <- to_nat (eval r e);;
      v' <- nth_error m n;;
      let c := (pc+1, (x !-> v'; r), m, sk) in
      ret ((c, ms), ds, [OLoad n])
  | <{{store[e]<-e'}}> =>
      let i := if ms then (ANum 0) else e in
      n <- to_nat (eval r i);;
      let c:= (pc+1, r, upd n m (eval r e'), sk) in
      ret ((c, ms), ds, [OStore n])
  | _ =>
    co <- step p c;;
    let '(c', o) := co in
    ret ((c', ms), ds, o)
    end
  end.

Fixpoint ideal_steps (f: nat) (p: prog) (ic: ideal_cfg) (ds: dirs)
  : option (ideal_cfg * dirs * obs) :=
  match f with 
  | S f' => 
      cdo1 <- ideal_step p ic ds;;
      let '(c1, ds1, o1) := cdo1 in
      cdo2 <- ideal_steps f' p c1 ds1;;
      let '(c2, ds2, o2) := cdo2 in
      ret (c2, ds2, o1++o2)
  | 0 =>
      ret (ic, ds, [])
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
  stk' <- map_opt (pc_sync p) stk;;
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
                                                                    if (Bool.eqb (snd blk) true) && (o =? 0) then Some 4 else None
                                                    | [] => trace "empty directives for call" None
                                                    | _ => trace "incorrect directive for call" None (* incorrect directive for call *)
                                                    end
                                  | _ => Some 1 (* assignment from source program, not decoration *)
                                  end
                      | None => Some 1 (* assignment from source program, last instruction in block *)
                      end
    | <{{ branch _ to _ }}> => (* branch decorations all come after the instruction itself, so this is the sync point *)
                               match ds with
                               | DBranch b :: _ => Some (if b then 3 else 2)
                                | [] => trace "empty directives for branch" None
                               | _ => trace "missing directive for branch" None
                               end
    | _ => Some 1 (* branch and call are the only instructions that add extra decorations *)
    end.

Definition gen_pc_from_prog (p: prog) : G cptr :=
  iblk <- choose (0, Datatypes.length(p) - 1) ;;
  let blk := nth_default ([],false) p iblk in
  off <- choose (0, Datatypes.length(fst blk) - 1);;
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
  | None => trace "lookup error" (ret [])
  end.

Scheme Equality for val.
(*Instance val_EqDec : EqDec val _ .*)
(*Proof.*)
  (*intros x y.*)
  (*destruct x, y; try (right; discriminate).*)
  (*- destruct (n == n0).*)
    (*+ left. now rewrite e.*)
    (*+ right. intros [= ?]. contradiction.*)
  (*- destruct (l == l0).*)
    (*+ left. now rewrite e.*)
    (*+ right. intros [= ?]. contradiction.*)
  (*- now left.*)
(*Qed.*)
(**)

Definition spec_cfg_eqb_up_to_callee (st1 st2 : spec_cfg) :=
  let '(pc1, r1, m1, sk1, c1, ms1) := st1 in
  let '(pc2, r2, m2, sk2, c2, ms2) := st2 in
  (pc1 ==b pc2)
  && (sk1 ==b sk2)
  && (c1 ==b c2) && (ms1 ==b ms2)
  && (m1 ==b m2)
  && pub_equivb (t_empty public) r1 (callee !-> (apply r1 callee) ; r2).

Compute ideal_step ([ ([ <{{skip}}> ], true) ]) (((0,0)), (t_empty UV), [UV; UV; UV], [], false) [].

(* Check 1: Single step diagram *)
QuickChick (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 => 
  forAll (gen_wt_mem tm pst) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack_from_prog_sized 3 p) (fun stk => 
  let icfg := (pc, rs1, m1, stk, false) in (* TODO: generate more meaningful stk (some number of possible call locations should do the trick)*)
  match (spec_cfg_sync p icfg) with
  | None => collect "hello"%string (checker tt)
  | Some tcfg => 
      forAll (gen_directive_from_ideal_cfg p pst icfg) (fun ds => 
      match ideal_step p icfg ds with 
      | None =>  collect ("ideal step failed "%string (* ++ " ICFG: "%string ++ show(icfg) ++ " INST: "%string *) ++ show (p[[pc]]))%string (checker tt)
          (* TODO: handle return on empty stack?*)
      | Some (icfg', _, _) => 
          match (steps_to_sync_point (uslh_prog p) tcfg ds) with 
          | None => match spec_steps 4 (uslh_prog p) tcfg ds with 
                    | None => checker true (* speculative execution should fail if it won't sync again *)
                    | Some _ => checker false
                    end
          | Some n => match spec_steps n (uslh_prog p) tcfg ds with 
                      | None => collect "spec exec fails "%string (checker tt) (* TODO: investigate these cases *)
                      | Some (tcfg', _, _) => match (spec_cfg_sync p icfg') with
                                              | None => collect "sync fails "%string (checker tt)
                                              | Some tcfgref => match (spec_cfg_eqb_up_to_callee tcfg' tcfgref) with 
                                                                | true => checker true
                                                                | false => trace (show tcfg' ++ "|||||" ++ show tcfgref) (checker false)
                                                                end
                                              end
                      end
          end
      end
      )
  end
  )))))).
(* Results:
  Passed 10000 tests (211 discards)

   Anything that failse steps_to_sync_point indeed feels speculative execution, and looking at traces, it is not just because of missing directives :)
*)

