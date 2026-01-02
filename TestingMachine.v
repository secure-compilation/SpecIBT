Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.

From Stdlib Require Import List. Import ListNotations.

Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

From SECF Require Import 
  Utils
  ListMaps
  MapsFunctor
  MiniCET
  Machine
  TaintTracking
  TestingLib.

Import MonadNotation.
Local Open Scope monad_scope.
(* Executable Semantics for testing *)

Module Import MCC := MachineCommon(ListTotalMap).
Module Import TS := TestingStrategies(MCC).
Module Import TT := TaintTracking(MCC).
Module Import SC := SimCommon(ListTotalMap).

Definition gen_dbr : G dir :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G direction :=
  l <- (elems_ 0 (proc_hd pst));; ret (DCall (l, 0)).

Derive Show for direction.

(* Find the condition that make machine_prog total function. I guess its wf. *)
(* Port existing tests from TestingMiniCET and Define some sanity checks for machine langauge. *)
(* Check every branches and jumps jump to the head of some block (If, machine program is generated from MiniCET program) *)

Definition wf_jmp_label (p:prog) (l:nat) : bool :=
  match nth_error p l with
  | Some (_,is_proc) => negb is_proc
  | None => false
  end.

Definition wf_jmp_inst (p:prog) (i : inst) : bool :=
  match i with
  | <{{branch e to l}}> => wf_jmp_label p l
  | <{{jump l}}> => wf_jmp_label p l
  | _ => true
  end.

Definition wf_jmp_blk (p:prog) (blb : list inst * bool) : bool :=
  forallb (wf_jmp_inst p) (fst blb).

Definition wf_jmp (p:prog) : bool :=
  forallb (wf_jmp_blk p) p.

Definition test_machine_branch_from_wf_minicet :=
  (forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p' := transform_load_store_prog c tm p in
  let harden := uslh_prog p' in
  wf_jmp (machine_prog harden))).

(*! QuickChick test_machine_branch_from_wf_minicet. *)

Print cfg.

Class Transform (A : Type) := mkTransform {
  transform : A -> A
}.

Instance MachineProg : Transform prog := {
  transform p := machine_prog p
}.

Instance MachineMem : Transform mem := {
  transform m := machine_mem m
}.

Instance MachineReg : Transform reg := {
  transform r := machine_rctx r
}.

Instance TransformPair {A B : Type} `{Transform A} `{Transform B}: Transform (A * B) := {
  transform x := let '(a, b) := x in (transform a, transform b)
}.

Instance TransformTuple {A B C : Type} `{Transform A} `{Transform B} `{Transform C}: Transform (A * B * C) := {
  transform '(a, b, c) := (transform a, transform b, transform c)
}.

Definition stuck_free (f : nat) (p : prog) (c: cfg) : exec_result :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  steps_taint_track f p ist [].

Definition load_store_trans_stuck_free `{Transform (prog * mem * reg)} := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p := transform_load_store_prog c tm p in
  let '(p, m, rs)  := transform (p, m, rs) in 
  let icfg := (ipc, rs, m, istk) in
  let r1 := stuck_free 1000 (machine_prog p) icfg in
  match r1 with
  | ETerm st os => checker true
  | EOutOfFuel st os => checker tt
  | EError st os => printTestCase (show p ++ nl) (checker false)
  end)))).

QuickChick load_store_trans_stuck_free.
(* +++ Passed 10000 tests (6286 discards) *)

Definition unused_var_no_leak `{Transform (prog * mem * reg)} := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p := transform_load_store_prog c tm p in
  let '(p, m, rs) := transform (p, m, rs) in
  let icfg := (ipc, rs, m, istk) in
  match stuck_free 100 p icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      checker (negb (existsb (String.eqb unused_var) leaked_vars))
  | EOutOfFuel st os => checker tt
  | EError st os => checker false
  end)))).

QuickChick unused_var_no_leak.
(* +++ Passed 10000 tests (8072 discards) *)

Definition test_ni `{Transform (prog * mem * reg)} := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p := transform_load_store_prog c tm p in
  let '(p, m, rs) := transform (p, m, rs) in
  let icfg := (ipc, rs, m, istk) in
  let r1 := taint_tracking 100 p icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let (m', rs') := transform (m', rs') in
      let icfg' := (ipc, rs', m', istk) in
      let r2 := taint_tracking 100 p icfg' in
      match r2 with
      | Some (os2', _, _) => checker (obs_eqb os1' os2')
      | None => checker false (* fail *)
      end))
   | None => checker tt (* discard *)
  end)))).

QuickChick test_ni.
(* +++ Passed 10000 tests (0 discards) *)

(* 
  NOTE: This test
  * generates MiniCET program
  * transforms it to block-based Machine program
  * runs speculative step on block-based Machine program
*)

Definition test_safety_preservation `{Show dir} `{Transform (prog * mem * reg)}
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p := transform_load_store_prog c tm p in
  let harden := uslh_prog p in
  let '(harden, m, rs) := transform (harden, m, spec_rs rs) in
  let icfg := (ipc, rs, m, istk) in
  let iscfg := (icfg, true, false) in
  let h_pst := pst_calc harden in
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg gen_dbr gen_dcall) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError (c', _, _) _ ds => checker false
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

QuickChick (test_safety_preservation gen_dbr gen_dcall).
(* +++ Passed 10000 tests (4236 discards) *)

(* 
  NOTE: This test
  * generates MiniCET program
  * transforms it to block-based Machine program
  * runs speculative step on block-based Machine program
*)

Definition test_relative_security `{Show dir} `{Transform (prog * mem * reg)}
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst) (fun m1 =>
  let p := transform_load_store_prog c tm p in
  let '(p, m1, rs1) := transform (p, m1, rs1) in
  let icfg1 := (ipc, rs1, m1, istk) in
  let r1 := taint_tracking 1000 p icfg1 in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m1) tms in
      forAll (gen_pub_equiv_same_ty P rs1) (fun rs2 =>
      forAll (gen_pub_mem_equiv_same_ty PM m1) (fun m2 =>
      let icfg2 := (ipc, rs2, m2, istk) in
      let r2 := taint_tracking 1000 p icfg2 in
      match r2 with
      | Some (os2', _, _) =>
          if (obs_eqb os1' os2') (* The source program produces the same leakage for a pair of inputs. *)
          then (let harden := uslh_prog p in
                let rs1' := transform (spec_rs rs1) in
                let icfg1' := (ipc, rs1', m1, istk) in
                let iscfg1' := (icfg1', true, false) in
                let h_pst := pst_calc harden in
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1' gen_dbr gen_dcall) (fun ods1 =>
                (match ods1 with
                 | SETerm _ os1 ds =>
                     (* checker true *)
                     let rs2' := transform (spec_rs rs2) in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => checker (obs_eqb os1 os2)
                     | SEOutOfFuel _ _ _ => collect "se2 oof"%string (checker tt)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                     end
                 | SEOutOfFuel _ os1 ds => 
                     let rs2' := transform (spec_rs rs2) in
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

QuickChick (test_relative_security gen_dbr gen_dcall).
(* +++ Passed 10000 tests (0 discards) *)