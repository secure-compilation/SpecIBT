Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import String.
Require Import Stdlib.Classes.EquivDec.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.

From SECF Require Import 
  ListMaps 
  MapsFunctor 
  MiniCET 
  Utils 
  TaintTracking 
  TestingSemantics.
From SECF Require Export Generation Printing.

(* TERSE: HIDEFROMHTML *)

(** * Reusable testing strategies, which are based on generators from this library.  *)

Module TestingStrategies(Import ST : Semantics ListTotalMap).
(* Extract Constant defNumTests => "1000000". *)

Module Import MTT := TaintTracking(ST).

(* ** Direction generators *)
(* 
Definition gen_dbr : G direction :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G direction :=
  l <- (elems_ 0 (proc_hd pst));; ret (DCall (l, 0)). *)

Variant sc_output_st : Type :=
  | SRStep : obs -> dirs -> spec_cfg -> sc_output_st
  | SRError : obs -> dirs -> spec_cfg -> sc_output_st
  | SRTerm : obs -> dirs -> spec_cfg -> sc_output_st.

Definition gen_step_direction (i: inst) (c: cfg) (pst: list nat)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G dirs :=
  let '(pc, rs, m, s) := c in
  match i with
  | <{ branch e to l }> => db <- gen_dbr;; ret [db]
  | <{ call e }> =>  dc <- gen_dcall pst;; ret [dc]
  | _ => ret []
  end.

Definition gen_spec_step (p:prog) (sc:spec_cfg) (pst: list nat) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir): G sc_output_st :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  match fetch p pc with
  | Some i =>
      match i with
      | <{{branch e to l}}> =>
          d <- gen_dbr;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | <{{call e}}> =>
          d <- gen_dcall pst;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | IRet | ICTarget =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [ ] sc'
               | (S_Term, _, _) => SRTerm [] [] sc
               | _ => SRError [] [] sc
               end)
      | _ =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [ ] sc'
               | _ => SRError [] [] sc
               end)
      end
  | None => ret (SRError [] [] sc)
  end.

Variant spec_exec_result : Type :=
  | SETerm (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEError (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEOutOfFuel (sc: spec_cfg) (os: obs) (ds: dirs).

#[export] Instance showSER `{Show dir} : Show spec_exec_result :=
  {show :=fun ser => 
      match ser with
      | SETerm sc os ds => show ds
      | SEError _ _ ds => ("error!!"%string ++ show ds)%string
      | SEOutOfFuel _ _ ds => ("oof!!"%string ++ show ds)%string
      end
  }.

Fixpoint _gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc: spec_cfg) (os: obs) (ds: dirs) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G (spec_exec_result) :=
  match f with
  | 0 => ret (SEOutOfFuel sc os ds)
  | S f' =>
      sr <- gen_spec_step p sc pst gen_dbr gen_dcall;;
      match sr with
      | SRStep os1 ds1 sc1 =>
          _gen_spec_steps_sized f' p pst sc1 (os ++ os1) (ds ++ ds1) gen_dbr gen_dcall
      | SRError os1 ds1 sc1 =>
          (* trace ("ERROR STATE: " ++ show sc1)%string *)
          (ret (SEError sc1 (os ++ os1) (ds ++ ds1)))
      | SRTerm  os1 ds1 sc1 =>
          ret (SETerm sc1 (os ++ os1) (ds ++ ds1))
      end
  end.

Definition gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc:spec_cfg) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G (spec_exec_result) :=
  _gen_spec_steps_sized f p pst sc [] [] gen_dbr gen_dcall.

(* Speculative Step functions *)
Definition spec_step_acc (p:prog) (sc:spec_cfg) (ds: dirs) : sc_output_st :=
  match spec_step p (S_Running sc) ds with
  | (S_Running sc', ds', os) => SRStep os ds' sc' (* sc': current spec_cfg, os: observations, ds': remaining dirs *)
  | (S_Term, _, _) => SRTerm [] [] sc
  | _ => SRError [] [] sc
  end.

Fixpoint _spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (os: obs) (ds: dirs) : spec_exec_result :=
  match f with
  | 0 => SEOutOfFuel sc os ds (* sc: current spec_cfg, os: observations, ds: remaining dirs *)
  | S f' =>
      match spec_step_acc p sc ds with
      | SRStep os1 ds1 sc1 =>
          _spec_steps_acc f' p sc1 (os ++ os1) ds1
      | SRError os1 ds1 sc1 =>
          (SEError sc1 (os ++ os1) ds1)
      | SRTerm os1 ds1 sc1 =>
          (SETerm sc1 (os ++ os1) ds1)
      end
  end.

Definition spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (ds: dirs) : spec_exec_result :=
  _spec_steps_acc f p sc [] ds.

Definition load_store_trans_basic_blk := (
    forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
      List.forallb basic_block_checker (map fst (transform_load_store_prog c tm p)))
).

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

Definition no_obs_prog_no_obs := (
  forAll gen_no_obs_prog (fun p =>
  let icfg := (ipc, empty_rs, empty_mem, istk) in
    match taint_tracking 10 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker tt
    end
  )).

Definition gen_prog_and_unused_var : G (rctx * tmem * list nat * prog * string) :=
  '(c, tm, pst, p) <- (gen_prog_wt_with_basic_blk 3 5);;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (c, tm, pst, p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (c, tm, pst, p, x).

(* TODO YF: I think we need a TransformSemantics type class  *)
Definition unused_var_no_leak 
  (transform_prog : rctx -> tmem -> prog -> prog) := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform_prog c tm p in
  match stuck_free 100 p' icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      checker (negb (existsb (String.eqb unused_var) leaked_vars))
  | EOutOfFuel st os => checker tt
  | EError st os => checker false
  end)))).

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

Definition gen_reg_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs => rs_wtb rs c))).

Definition gen_pub_mem_equiv_is_pub_equiv := (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

Definition gen_mem_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst) (fun m => m_wtb m tm))).

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

Definition test_safety_preservation `{Show dir} 
  (harden : prog -> prog) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
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
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg gen_dbr gen_dcall) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError (c', _, _) _ ds => checker false
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

Definition test_relative_security `{Show dir} 
  (harden : prog -> prog) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
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
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1' gen_dbr gen_dcall) (fun ods1 =>
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

End TestingStrategies.
