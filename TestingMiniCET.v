(** * Testing MiniCET *)

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
Import MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From SECF Require Import MiniCET TaintTrackingMiniCET.
From Stdlib Require Import String.

From SECF Require Import Utils.
From SECF Require Import ListMaps.
From SECF Require Import MapsFunctor.
From Stdlib Require Import Classes.EquivDec.


Module MCC := MiniCETCommon(ListTotalMap).
Module MTT := TaintTracking(MCC).
Import MCC MTT.

(* Extract Constant defNumTests => "1000000". *)

(* check 0: load/store transformation creates basic blocks *)

Definition load_store_trans_basic_blk := (
    forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
      List.forallb basic_block_checker (map fst (transform_load_store_prog c tm p)))
).
(*! QuickChick load_store_trans_basic_blk. *)

(* check 1: generated program is stuck-free. *)

Definition stuck_free (f : nat) (p : prog) (c: cfg) : exec_result :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  steps_taint_track f p ist [].

Definition load_store_trans_stuck_free := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p' := transform_load_store_prog c tm p in
  let icfg := (ipc, rs, m, istk) in
  let r1 := stuck_free 1000 p' icfg in
  match r1 with
  | ETerm st os => checker true
  | EOutOfFuel st os => checker tt
  | EError st os => printTestCase (show p' ++ nl) (checker false)
  end)))).

(*! QuickChick load_store_trans_stuck_free. *)

(* +++ Passed 10000 tests (6173 discards) *)

Definition taint_tracking (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (steps_taint_track f p ist []) with
    (* JB: also return the (partial) trace in the oof case, even if the taint tracking won't be sound in this case. *)
    (* This should be fine if the speculative execution does not get more fuel than the sequential one *)
  | ETerm (_, _, tobs) os | EOutOfFuel (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.


Definition no_obs_prog_no_obs := (
  forAll gen_no_obs_prog (fun p =>
  let icfg := (ipc, empty_rs, empty_mem, istk) in
    match taint_tracking 10 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker tt
    end
  )).

(*! QuickChick no_obs_prog_no_obs. *)

(* check 3: implicit flow *)

Example implicit_flow_test p rs icfg
  (P: p = [([ IBranch (AId "x") 1; IJump 1 ], true); ([ IAsgn "y"%string (ANum 1); IRet], false)])
  (RS: rs = (N 0, [("x"%string, N 10); ("y"%string, N 0)]))
  (ICFG: icfg = (ipc, rs, [], [])):
  match taint_tracking 10 p icfg with
  | Some (obs, leaked_vars, _) =>
      existsb (String.eqb "x") leaked_vars
  | None => false
  end = true.
Proof.
  remember (taint_tracking 10 p icfg).
  subst p rs icfg. simpl in Heqo.
  subst. simpl. reflexivity.
Qed.

(* check 4: unused variables never leaked *)

Definition gen_prog_and_unused_var : G (rctx * tmem * list nat * prog * string) :=
  '(c, tm, pst, p) <- (gen_prog_wt_with_basic_blk 3 5);;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (c, tm, pst, p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (c, tm, pst, p, x).

Definition unused_var_no_leak (transform : rctx -> tmem -> prog -> prog) := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform c tm p in
  match stuck_free 100 p' icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      checker (negb (existsb (String.eqb unused_var) leaked_vars))
  | EOutOfFuel st os => checker tt
  | EError st os => checker false
  end)))).

Definition unused_var_no_leak_transform_load_store := 
  unused_var_no_leak (fun c tm p => transform_load_store_prog c tm p).
(*! QuickChick unused_var_no_leak_transform_load_store. *)

(* check 5: gen_pub_equiv_same_ty works *)

Definition gen_pub_equiv_same_ty (P : total_map label) (s: total_map val) : G (total_map val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 | UV => ret UV (* shouldn't happen *)
                 end in
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map val)) (c : string * val) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if t_apply P k then ret v else f v);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

Definition gen_pub_equiv_is_pub_equiv := (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv_same_ty P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).
(*! QuickChick gen_pub_equiv_is_pub_equiv. *)


(* check 6: generated register set is well-typed. *)

Definition gen_reg_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs => rs_wtb rs c))).
(*! QuickChick gen_reg_wt_is_wt. *)

(* check 5: gen_pub_mem_equiv_same_ty works *)

Definition gen_pub_mem_equiv_is_pub_equiv := (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).
(*! QuickChick gen_pub_mem_equiv_is_pub_equiv. *)

(* check 7: generated memory is well-typed. *)

Definition gen_mem_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst) (fun m => m_wtb m tm))).
(*! QuickChick gen_mem_wt_is_wt. *)

(* check 8: non-interference *)

Definition test_ni (transform : rctx -> tmem -> prog -> prog) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform c tm p in
  let r1 := taint_tracking 100 p' icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let icfg' := (ipc, rs', m', istk) in
      let r2 := taint_tracking 100 p' icfg' in
      match r2 with
      | Some (os2', _, _) => checker (obs_eqb os1' os2')
      | None => checker false (* fail *)
      end))
   | None => checker tt (* discard *)
  end)))).

Definition test_ni_transform_load_store := 
  test_ni (fun c tm p => transform_load_store_prog c tm p).
(*! QuickChick test_ni_transform_load_store. *)

(* +++ Passed 1000000 tests (639813 discards) *)
(* Time Elapsed: 152.683837s *)

(** Safety Preservation *)

(* Extract Constant defNumTests => "1000000". *)

Definition test_safety_preservation (harden : prog -> prog) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform_load_store_prog c tm p in
  let harden := harden p' in
  let rs' := spec_rs rs in
  let icfg' := (ipc, rs', m, istk) in
  let iscfg := (icfg', true, false) in
  let h_pst := pst_calc harden in
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError (c', _, _) _ ds => checker false
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

Definition test_safety_preservation_uslh := test_safety_preservation uslh_prog.
(*! QuickChick test_safety_preservation_uslh. *)

(* +++ Passed 1000000 tests (431506 discards) *)
(* Time Elapsed: 137.819446s *)

(** Testing Relative Security *)

(* Extract Constant defNumTests => "1000000". *)

Definition test_relative_security (harden : prog -> prog) := (
  (* TODO: should make sure shrink indeed satisfies invariants of generator;
           or define a better shrinker *)
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst) (fun m1 =>
  let icfg1 := (ipc, rs1, m1, istk) in
  let p' := transform_load_store_prog c tm p in
  let r1 := taint_tracking 1000 p' icfg1 in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m1) tms in
      forAll (gen_pub_equiv_same_ty P rs1) (fun rs2 =>
      forAll (gen_pub_mem_equiv_same_ty PM m1) (fun m2 =>
      let icfg2 := (ipc, rs2, m2, istk) in
      let r2 := taint_tracking 1000 p' icfg2 in
      match r2 with
      | Some (os2', _, _) =>
          if (obs_eqb os1' os2') (* The source program produces the same leakage for a pair of inputs. *)
          then (let harden := harden p' in
                let rs1' := spec_rs rs1 in
                let icfg1' := (ipc, rs1', m1, istk) in
                let iscfg1' := (icfg1', true, false) in
                let h_pst := pst_calc harden in
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1') (fun ods1 =>
                (match ods1 with
                 | SETerm _ os1 ds =>
                     (* checker true *)
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => checker (obs_eqb os1 os2)
                     | SEOutOfFuel _ _ _ => collect "se2 oof"%string (checker tt)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                     end
                 | SEOutOfFuel _ os1 ds => 
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => collect "se1 oof but se2 term"%string (checker tt) (* this would be very weird *)
                     | SEOutOfFuel _ os2 _ => checker (obs_eqb os1 os2) (* equality should hold because essentially lockstep *)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                     end
                 | _ =>  collect "1st speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                 end))
               )
          else collect "seq obs differ"%string (checker tt) (* discard *)
      | None => collect "tt2 failed"%string (checker tt) (* discard *)
      end))
   | None => collect "tt1 failed"%string (checker tt) (* discard *)
  end)))).

Definition test_relative_security_uslh := test_relative_security uslh_prog.
(*! QuickChick test_relative_security_uslh. *)

(* Outdated. available commit: 58fa2d5c090d764b548c967ff4c40a6d6f2fb679*)
(* +++ Passed 1000000 tests (0 discards) *)
(* Time Elapsed: 1308.843714s *)
