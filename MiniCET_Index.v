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


(** Sequential small-step semantics for MiniCET *)

(* Definition step (p:prog) (c:cfg) : option (cfg * obs) :=
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{skip}}> | <{{ctarget}}> =>
      ret ((pc+1, r, m, sk), [])
  | <{{x:=e}}> =>
      ret ((pc+1, (x !-> eval r e; r), m, sk), [])
  | <{{branch e to l}}> =>
      n <- to_nat (eval r e);;
      let b := not_zero n in
      ret ((if b then (l,0) else pc+1, r, m, sk), [OBranch b])
  | <{{jump l}}> =>
      ret (((l,0), r, m, sk), [])
  | <{{x<-load[e]}}> =>
      n <- to_nat (eval r e);;
      v' <- nth_error m n;;
      ret ((pc+1, (x !-> v'; r), m, sk), [OLoad n])      
  | <{{store[e]<-e'}}> =>
      n <- to_nat (eval r e);;
      ret ((pc+1, r, upd n m (eval r e'), sk), [OStore n])
  | <{{call e}}> =>
      l <- to_fp (eval r e);;
      ret (((l,0), r, m, (pc+1)::sk), [OCall l])
  | <{{ret}}> =>
      pc' <- hd_error sk;;
      ret ((pc', r, m, tl sk), [])
  end. 

 *)

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

(* Reserved Notation *)
(*    "p '|-' '<((' c , st , ast '))>' '-->*^' os '<((' ct , stt , astt '))>'" *)
(*    (at level 40, c custom com at level 99, ct custom com at level 99, *)
(*     st constr, ast constr, stt constr, astt constr at next level). *)

(* Inductive multi_seq (p:prog) (c:com) (st:state) (ast:astate) : *)
(*     com -> state -> astate -> obs -> Prop := *)
(*   | multi_seq_refl : p |- <((c, st, ast))> -->*^[] <((c, st, ast))> *)
(*   | multi_seq_trans (c':com) (st':state) (ast':astate) *)
(*                 (c'':com) (st'':state) (ast'':astate) *)
(*                 (os1 os2 : obs) : *)
(*       p |- <((c, st, ast))> -->^os1 <((c', st', ast'))> -> *)
(*       p |- <((c', st', ast'))> -->*^os2 <((c'', st'', ast''))> -> *)
(*       p |- <((c, st, ast))> -->*^(os1++os2) <((c'', st'', ast''))> *)

(*   where "p |- <(( c , st , ast ))> -->*^ os <(( ct ,  stt , astt ))>" := *)
(*     (multi_seq p c st ast ct stt astt os). *)

(** Small-step speculative semantics for MiniCET *)

(* Definition spec_step (p:prog) (sc:spec_cfg) (ds:dirs) : option (spec_cfg * dirs * obs) := *)
(*   let '(c, ct, ms) := sc in *)
(*   let '(pc, r, m, sk) := c in *)
(*   i <- p[[pc]];; *)
(*   match i with *)
(*   | <{{branch e to l}}> => *)
(*       is_false ct;; *)
(*       d <- hd_error ds;; *)
(*       b' <- is_dbranch d;; *)
(*       n <- to_nat (eval r e);; *)
(*       let b := not_zero n in *)
(*       let ms' := ms || negb (Bool.eqb b b') in  *)
(*       let pc' := if b' then (l, 0) else (pc+1) in *)
(*       ret ((((pc', r, m, sk), ct, ms'), tl ds), [OBranch b]) *)
(*   | <{{call e}}> => *)
(*       is_false ct;; *)
(*       d <- hd_error ds;; *)
(*       pc' <- is_dcall d;; *)
(*       l <- to_fp (eval r e);; *)
(*       let ms' := ms || negb ((fst pc' =? l) && (snd pc' =? 0)) in *)
(*       ret ((((pc', r, m, (pc+1)::sk), true, ms'), tl ds), [OCall l]) *)
(*   | <{{ctarget}}> => *)
(*       is_true ct;; (* ctarget can only run after call? (CET) Maybe not? *) *)
(*       ret (((pc+1, r, m, sk), false, ms), ds, []) *)
(*   | _ => *)
(*       is_false ct;; *)
(*       co <- step p c;; *)
(*       let '(c',o) := co in *)
(*       ret ((c',false,ms), ds, o) *)
(*   end. *)

(* Fixpoint spec_steps (f:nat) (p:prog) (c:spec_cfg) (ds:dirs) *)
(*   : option (spec_cfg * dirs * obs) := *)
(*   match f with *)
(*   | S f' => *)
(*       cdo1 <- spec_step p c ds;; *)
(*       let '(c1,ds1,o1) := cdo1 in *)
(*       cdo2 <- spec_steps f' p c1 ds1;; *)
(*       let '(c2,ds2,o2) := cdo2 in *)
(*       ret (c2,ds2,o1++o2) *)
(*   | 0 => *)
(*       None (* Q: Do we need more precise out-of-fuel error here? *) *)
(*   end. *)

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
  | ISMI_Branch : forall pc pc' r m sk ms ms' b b' e n n' l l', 
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n -> 
      n' = (if (ms =? 1) then 0 else n) -> (* mask branch condition *)
      b = (not_zero n') ->
      add_block_M <{{ i[(msf := ((~n') ? 1 : msf)); jump l] }}> = M l' -> (* not sure if this is right but need l' *)     
      pc' = if n' then (l',0) else pc+1 ->
      ms' = ms || (negb (Bool.eqb b b')) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( ((pc', r, m, sk), false, ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> -> 
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( (((l,0), r, m, sk), false, ms) ))>
  | ISMI_Load : forall pc r m sk x e e' n v' ms,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      e' = (if (ms =? 1) then 0 else e) ->
      to_nat (eval r e') = Some n ->
      nth_error m n = Some v' ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n] <(( ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | ISMI_Store : forall pc r m sk e e' e'' n ms,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      e'' = (if (ms =? 1) then 0 else e) ->
      to_nat (eval r e'') = Some n ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore n] <(( ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | ISMI_Call : forall pc pc' r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      e' = if (ms =? 1) then (FP 0) else e ->
      to_fp (eval r e') = Some l -> 
      ms' = ms || negb ((fst pc' =? l) && (snd pc' =? 0)) ->
      p |- <(( ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( ((pc', r, m, (pc+1)::sk), true, ms') ))>
  | ISMI_CTarget : forall pc r m sk ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( ((pc+1, r, m, sk), false, ms) ))>
  | ISMI_Ret : forall pc r m sk pc' ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( ((pc, r, m, pc'::sk), false, ms) ))> -->_[]^^[] <(( ((pc', r, m, sk), false, ms) ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (ideal_eval_small_step_inst p sc sct ds os).
(* 
  
uslh: 

   Definition M (A: Type) := nat -> A * prog.

Definition u_ret {A: Type} (x: A) : M A :=
  fun c => (x, []).

Definition u_bind {A B: Type} (m: M A) (f: A -> M B) : M B :=
  fun c =>
    let '(r, p) := m c in
    let '(r', p') := f r (c + Datatypes.length p) in
    (r', p ++ p').

#[export] Instance monad : Monad M :=
  { ret := @u_ret;
    bind := @u_bind
  }.

Definition mapM {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  sequence (List.map f l).

Definition concatM {A: Type} (m: M (list (list A))) : M (list A) :=
  xss <- m;; ret (List.concat xss).

Definition add_block (bl: list inst) (c: nat) := (c, [(bl, false)]).

Definition add_block_M (bl: list inst) : M nat :=
  fun c => add_block bl c.

Definition u_inst (i: inst) : M (list inst) :=
  match i with
  | <{{ctarget}}> => ret [<{{skip}}>]
  | <{{x<-load[e]}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{x<-load[e']}}>]
  | <{{store[e] <- e1}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{store[e'] <- e1}}>]
  | <{{branch e to l}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in (* if mispeculating always pc+1 *)
      l' <- add_block_M <{{ i[(msf := ((~e') ? 1 : msf)); jump l] }}>;;
      ret <{{ i[branch e' to l'; (msf := (e' ? 1 : msf))] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &0 : e }> in
      ret <{{ i[callee:=e'; call e'] }}>
  | _ => ret [i]
  end.

Definition u_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  bl' <- concatM (mapM u_inst bl);;
  if is_proc then
    ret (<{{ i[ctarget; msf := (callee = &l) ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition u_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM u_blk idx_p (Datatypes.length p) in
  (p' ++ newp).

*)

   
