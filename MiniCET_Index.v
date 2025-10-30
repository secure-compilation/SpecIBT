(*** UltimateSLH: Relative Security Against Speculation Attacks*)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import ListMaps.
From SECF Require Import TempMiniCET.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import Stdlib.Setoids.Setoid.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* %s/\s\+$//e to strip trailing whitespace *)

(** Sequential small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  cfg -> cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( (pc, rs, m, stk) ))> -->^[] <(( (pc+1, rs, m, stk) ))>
  | SSMI_Asgn : forall pc r m sk e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( (pc+1, (x !-> (eval r e); r), m, sk) ))>
  | SSMI_Branch : forall pc pc' r m sk e n l,
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then (l,0) else pc+1) ->
      p |- <(( (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( (pc', r, m, sk) ))>
  | SSMI_Jump : forall l pc r m sk,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( ((l,0), r, m, sk) ))>
  | SSMI_Load : forall pc r m sk x e n v',
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( (pc, r, m, sk) ))> -->^[OLoad n] <(( (pc+1, (x !-> v'; r), m, sk) ))>
  | SSMI_Store : forall pc r m sk e e' n,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( (pc, r, m, sk) ))> -->^[OStore n] <(( (pc+1, r, upd n m (eval r e'), sk) ))>
  | SSMI_Call : forall pc r m sk e l,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      p |- <(( (pc, r, m, sk) ))> -->^[OCall l] <(( ((l,0), r, m, ((pc+1)::sk)) ))>
  | SSMI_CTarget : forall pc r m sk,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( (pc, r, m, sk) ))> -->^[] <(( (pc+1, r, m, sk) ))>
  | SSMI_Ret : forall pc r m sk pc',
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( (pc, r, m, pc'::sk) ))> -->^[] <(( (pc', r, m, sk) ))>

  where "p |- <(( c ))> -->^ os <(( ct ))>" :=
      (seq_eval_small_step_inst p c ct os).

(** Sequential multi-step relation *)

Reserved Notation
  "p '|-' '<((' c '))>' '-->*^' os '<((' ct '))>'"
      (at level 40, c constr, ct constr).

Inductive multi_seq_inst (p : prog) (c : cfg) : cfg -> obs -> Prop :=
  | multi_seq_inst_refl : p |- <(( c ))> -->*^[] <(( c ))>
  | multi_seq_inst_trans (c' c'' : cfg) (os1 os2 : obs) :
      p |- <(( c ))> -->^os1 <(( c' ))> ->
      p |- <(( c' ))> -->*^os2 <(( c'' ))> ->
      p |- <(( c ))> -->*^(os1 ++ os2) <(( c'' ))>

  where "p |- <(( c ))> -->*^ os <(( ct ))>" :=
      (multi_seq_inst p c ct os).

(** Speculative small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive spec_eval_small_step (p:prog):
    spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then (l, 0) else (pc+1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( (((l,0), r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n] <(( ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore n] <(( ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( ((pc', r, m, sk), false, ms) ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

(** Speculative multi-step relation *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> nat -> Prop :=
  | multi_spec_inst_refl sc : p |- <(( sc ))> -->*_[]^^[]^^0 <(( sc ))>
  | multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>
  where "p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

(** Ideal small-step semantics for MiniCET *)

Reserved Notation
  "p '|-' '<((' sc '))>' '-->i_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive ideal_eval_small_step_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | ISMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      n' = (if ms then 0 else n) ->
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) ->
      ms' = (ms || (negb (Bool.eqb b b'))) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), false, ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( (((l,0), r, m, sk), false, ms) ))>
  | ISMI_Load : forall pc r m sk x e n n' v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      n' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n'] <(( ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | ISMI_Store : forall pc r m sk e e' e'' n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      e'' = (if ms then 0 else n) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore e''] <(( ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | ISMI_Call : forall pc pc' blk r m sk e l l' (ms ms' : bool),
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      l' = (if ms then 0 else l) ->
      (* attacker isn't allowed to jump to non-proc blocks, nor to jump over ctarget to middle of proc block *)
      (* may need to change this, depending on how Intel CET handles OOB attacker pc *)
      nth_error p (fst pc') = Some blk ->
      snd blk = true ->
      snd pc' = 0 ->
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l'] <(( ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | ISMI_CTarget : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | ISMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( ((pc', r, m, sk), false, ms) ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (ideal_eval_small_step_inst p sc sct ds os).

(** Ideal multi-step relation *)

Reserved Notation
  "p '|-' '<((' ic '))>' '-->*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive multi_ideal_inst (p:prog) :
  spec_cfg -> spec_cfg -> dirs -> obs -> Prop :=
  | multi_ideal_inst_refl ic : p |- <(( ic ))> -->*_[]^^[] <(( ic ))>
  | multi_ideal_inst_trans ic1 ic2 ic3 ds1 ds2 os1 os2 :
      p |- <(( ic1 ))> -->_ds1^^os1 <(( ic2 ))> ->
      p |- <(( ic2 ))> -->*_ds2^^os2 <(( ic3 ))> ->
      p |- <(( ic1 ))> -->*_(ds1++ds2)^^(os1++os2) <(( ic3 ))>
  where "p |- <(( ic ))> -->*_ ds ^^ os <(( ict ))>" :=
    (multi_ideal_inst p ic ict ds os).

(** * Backwards Compiler Correctness of Ultimate Speculative Load Hardening *)

(* get value of "msf" bit (program level) given current register state *)
Definition msf_lookup (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  apply r msf.

Definition callee_lookup (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  apply r callee.

(* returns bool corresponding to state of ms flag (semantics level) *)
Definition ms_true (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in ms.

Section BCC.

Variable p: prog.
Definition tp : prog := uslh_prog p.

(* predicate for fold *)
Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

(* Implementing pc_sync:

    - Add 1 to any br or call insts before the one being synchronized.
    - Add 2 if the blk is proc start.

*)

(* synchronizing point relation between src and tgt *)
Definition pc_sync (pc: cptr) : option cptr :=
  match p with
  | []   => None
  | _    =>
      match nth_error p (fst pc) with
      | Some blk => let acc1 := if (snd blk) then 2 else 0 in
                      match (snd pc) with
                      | 0   => Some ((fst pc), add (snd pc) acc1)
                      | S _ => let insts_before_pc := (firstn (snd pc) (fst blk)) in
                                 let acc2 :=
                                   fold_left (fun acc (i:inst) =>
                                              if (is_br_or_call i) then (add acc 1) else acc) insts_before_pc acc1 in
                                     Some ((fst pc), add (snd pc) acc2)
                      end
      | None     => None
      end
  end.

(* given a source register, sync with target register *)
(* can't handle callee here, not enough info if not speculating *)
Definition r_sync (r: reg) (ms: bool) : reg :=
  msf !-> N (if ms then 1 else 0); r.

(* given a source config, return the corresponding target config *)
Definition spec_cfg_sync (sc: spec_cfg) : option spec_cfg :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  match pc_sync pc with
  | Some pc => let tc := (pc, r_sync r ms, m, stk) in
                Some (tc, ct, ms)
  | _ => None
  end.

(* How many steps does it take for target program to reach the
   program point the source reaches in one step? *)
Definition steps_to_sync_point (tsc: spec_cfg) (ds : dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in
  match p[[pc]] with (* number of steps for T -> T' depends on which inst *)
  | Some i => match (i, ds) with
              | (<{{branch e to l}}>, [DBranch b]) => Some (if b then 3 else 2)
              | (<{{call e}}>, [DCall lo]) => let '(l, o) := lo in
                                              match nth_error p l with
                                              (* not sure how to handle sync point steps if attacker jumped to a totally different block *)
                                              (* currently just forbidding it as in current ideal semantics *)
                                              | Some blk => if (snd blk) && (o =? 0) then Some 4 else None
                                              | _ => None
                                              end
              | _ => Some 1
              end
  | _ => None
  end.

Definition get_reg (spc: spec_cfg) : reg :=
  let '(c, ct, ms) := spc in
  let '(pc, r, m, sk) := c in
  r.

Definition get_pc (spc: spec_cfg) : cptr :=
  let '(c, ct, ms) := spc in
  let '(pc, r, m, sk) := c in
  pc.


(*
  Lemma ultimate_slh_bcc_generalized (p:prog) : forall n c ds st ast (b b' : bool) c' st' ast' os,
  nonempty_arrs ast ->
  unused_prog "b" p ->
  unused "b" c ->
  unused_prog "callee" p ->
  unused "callee" c ->
  st "b" = (if b then 1 else 0) ->
  ultimate_slh_prog p |- <((ultimate_slh c, st, ast, b))> -->*_ds^^os^^n <((c', st', ast', b'))> ->
      exists c'', p |- <((c, st, ast, b))> -->i*_ds^^os <((c'', "callee" !-> st "callee"; "b" !-> st "b"; st', ast', b'))>
  /\ (c' = <{{ skip }}> -> c'' = <{{ skip }}> /\ st' "b" = (if b' then 1 else 0)). (* <- generalization *)

*)

(* BCC lemma for one single instruction *)
Lemma ultimate_slh_bcc_single_cycle : forall sc1 tsc1 tsc2 n ds os,
  unused_prog msf p -> (* variables msf and callee are not used by the program *)
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) -> (* "msf" must correspond to ms at the outset *)
  steps_to_sync_point tsc1 ds = Some n -> (* given starting target cfg, how many steps to first sync point? *)
  spec_cfg_sync sc1 = Some tsc1 ->
  (* multiple steps of tgt correspond to one step of src *)
  uslh_prog p |- <(( tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( sc1 ))> -->_ ds ^^ os <(( sc2 ))> /\ spec_cfg_sync sc2 = Some tsc2.

Proof.
  intros until os. intros unused_msf unused_callee msf_ms n_steps sync_1 tgt.
Admitted.

End BCC.

Lemma ultimate_slh_bcc (p: prog) : forall sc1 tsc1 tsc2 n ds os,
  unused_prog msf p ->
  unused_prog callee p ->
  msf_lookup tsc1 = N (if (ms_true tsc1) then 1 else 0) ->
  tsc1 = spec_cfg_sync p sc1 ->
  uslh_prog p |- <(( tsc1 ))> -->*_ds^^os^^n <(( tsc2 ))> ->
  exists sc2, p |- <(( sc1 ))> -->*_ ds ^^ os <(( sc2 ))> /\ tsc2 = spec_cfg_sync p sc2.
Proof.
Admitted.

(* (** * Definition of Relative Secure *) *)

(* Definition seq_same_obs p c st1 st2 ast1 ast2 : Prop := *)
(*   forall stt1 stt2 astt1 astt2 os1 os2 c1 c2, *)
(*     p |- <(( (pc1, r1, m1, stk1) ))> -->*^ os1 <(( (pc1', r1', m1', stk1') ))> -> *)
(*     p |- <(( (pc2, r2, m2, stk2) ))> -->*^ os2 <(( (pc2', r2', m2', stk2') ))> -> *)
(*     (prefix os1 os2) \/ (prefix os2 os1).  *)

(* Definition spec_same_obs p c st1 st2 ast1 ast2 : Prop := *)
(*   forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2 n c1 c2, *)
(*     p |- <((c, st1, ast1, false))> -->*_ds^^os1^^n <((c1, stt1, astt1, bt1))> -> *)
(*     p |- <((c, st2, ast2, false))> -->*_ds^^os2^^n <((c2, stt2, astt2, bt2))> -> *)
(*     os1 = os2.  *)

(* (* The new definition adds the extra program transformation we  *)
(*    needed to check for speculation at the target of a call instruction. *)
(*    This was needed to apply the bcc proof in the final theorem. *) *)

(* (*  old definition: *)
(*    Definition relative_secure (p:prog) (trans : com -> com) *)
(*     (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop := *)
(*   seq_same_obs p c st1 st2 ast1 ast2 -> *)
(*    spec_same_obs p (trans c) st1 st2 ast1 ast2. *) *)

(* Definition relative_secure (p:prog) (trans1 : prog -> prog) (trans2 : com -> com) *)
(*     (c:com) (st1 st2 : state) (ast1 ast2 : astate): Prop := *)
(*   seq_same_obs p c st1 st2 ast1 ast2 -> *)
(*   spec_same_obs (trans1 p) (trans2 c) st1 st2 ast1 ast2. *)

(* (** * Ultimate Speculative Load Hardening *) *)

