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

Inductive multi_spec_inst (p : prog) (sc : spec_cfg) : spec_cfg -> dirs -> obs -> nat -> Prop :=
  | multi_spec_inst_refl : p |- <(( sc ))> -->*_[]^^[]^^0 <(( sc ))>
  | multi_spec_inst_trans (sc' sc'' : spec_cfg) (ds1 ds2 : dirs) (os1 os2 : obs) (n : nat) : 
      p |- <(( sc ))> -->_ds1^^os1 <(( sc' ))> -> 
      p |- <(( sc' ))> -->*_ds2^^os2^^n <(( sc'' ))> ->
      p |- <(( sc ))> -->*_(ds1 ++ ds2)^^(os1 ++ os2)^^(S n) <(( sc'' ))>

  where "p |- <(( sc ))> -->*_ds^^os^^n <(( sct ))>" :=
      (multi_seq_inst p sc sct ds os).

(* Reserved Notation *)
(*   "p '|-' '<((' c , st , ast , b '))>' '-->*_' ds '^^' os '^^' n '<((' ct , stt , astt , bt '))>'" *)
(*   (at level 40, c custom com at level 99, ct custom com at level 99, *)
(*    st constr, ast constr, stt constr, astt constr at next level). *)

(* Inductive multi_spec (p:prog) (c:com) (st:state) (ast:astate) (b:bool) : *)
(*   com -> state -> astate -> bool -> dirs -> obs -> nat -> Prop := *)
(*   | multi_spec_refl : p |- <((c, st, ast, b))> -->*_[]^^[]^^0 <((c, st, ast, b))> *)
(*   | multi_spec_trans (c':com) (st':state) (ast':astate) (b':bool) *)
(*                 (c'':com) (st'':state) (ast'':astate) (b'':bool) *)
(*                 (ds1 ds2 : dirs) (os1 os2 : obs) (n : nat) : *)
(*       p |- <((c, st, ast, b))> -->_ds1^^os1 <((c', st', ast', b'))> -> *)
(*       p |- <((c', st', ast', b'))> -->*_ds2^^os2^^n <((c'', st'', ast'', b''))> -> *)
(*       p |- <((c, st, ast, b))> -->*_(ds1++ds2)^^(os1++os2)^^(S n) <((c'', st'', ast'', b''))> *)

(*     where "p |- <(( c , st , ast , b ))> -->*_ ds ^^ os ^^ n <(( ct ,  stt , astt , bt ))>" := *)
(*     (multi_spec p c st ast b ct stt astt bt ds os n). *)

(** Ideal small-step semantics for MiniCET *)

(** * Ideal small-step evaluation *)

(* Reserved Notation *)
(*   "p '|-' '<((' c , st , ast , b '))>' '-->i_' ds '^^' os '<((' ct , stt , astt , bt '))>'" *)
(*   (at level 40, c custom com at level 99, ct custom com at level 99, *)
(*    st constr, ast constr, stt constr, astt constr at next level). *)

(* Inductive ideal_eval_small_step (p:prog): *)
(*     com -> state -> astate -> bool -> *)
(*     com -> state -> astate -> bool -> dirs -> obs -> Prop := *)
(*   | ISM_Asgn  : forall st ast b e n x, *)
(*       aeval st e = n -> *)
(*       p |- <((x := e, st, ast, b))> -->i_[]^^[] <((skip, x !-> n; st, ast, b))> *)
(*   | ISM_Seq : forall c1 st ast b ds os c1t stt astt bt c2, *)
(*       p |- <((c1, st, ast, b))>  -->i_ds^^os <((c1t, stt, astt, bt))>  -> *)
(*       p |- <(((c1;c2), st, ast, b))>  -->i_ds^^os <(((c1t;c2), stt, astt, bt))> *)
(*   | ISM_Seq_Skip : forall st ast b c2, *)
(*       p |- <(((skip;c2), st, ast, b))>  -->i_[]^^[] <((c2, st, ast, b))> *)
(*   | ISM_If : forall be ct cf st ast b c' b', *)
(*       b' = (is_empty (vars_bexp be) || negb b) && beval st be -> *)
(*       c' = (if b' then ct else cf) -> *)
(*       p |- <((if be then ct else cf end, st, ast, b))> -->i_[DStep]^^[OBranch b'] <((c', st, ast, b))> *)
(*   | ISM_If_F : forall be ct cf st ast b c' b', *)
(*       b' = (is_empty (vars_bexp be) || negb b) && beval st be -> *)
(*       c' = (if b' then cf else ct) -> *)
(*       p |- <((if be then ct else cf end, st, ast, b))> -->i_[DForce]^^[OBranch b'] <((c', st, ast, true))> *)
(*   | ISM_While : forall be c st ast b, *)
(*       p |- <((while be do c end, st, ast, b))> -->i_[]^^[] *)
(*            <((if be then c; while be do c end else skip end, st, ast, b))> *)
(*   | ISM_ARead : forall x a ie st ast (b :bool) i, *)
(*       (if negb (is_empty (vars_aexp ie)) && b then 0 else (aeval st ie)) = i -> *)
(*       i < length (ast a) -> *)
(*       p |- <((x <- a[[ie]], st, ast, b))> -->i_[DStep]^^[OARead a i] *)
(*            <((skip, x !-> nth i (ast a) 0; st, ast, b))> *)
(*   | ISM_ARead_U : forall x a ie st ast i a' i', *)
(*       aeval st ie = i -> *)
(*       is_empty (vars_aexp ie) = true -> *)
(*       i >= length (ast a) -> *)
(*       i' < length (ast a') -> *)
(*       p |- <((x <- a[[ie]], st, ast, true))> -->i_[DLoad a' i']^^[OARead a i] *)
(*            <((skip, x !-> nth i' (ast a') 0; st, ast, true))> *)
(*   | ISM_Write : forall a ie e st ast (b :bool) i n, *)
(*       aeval st e = n -> *)
(*       (if negb (is_empty (vars_aexp ie)) && b then 0 else (aeval st ie)) = i -> *)
(*       i < length (ast a) -> *)
(*       p |- <((a[ie] <- e, st, ast, b))> -->i_[DStep]^^[OAWrite a i] *)
(*            <((skip, st, a !-> upd i (ast a) n; ast, b))> *)
(*   | ISM_Write_U : forall a ie e st ast i n a' i', *)
(*       aeval st e = n -> *)
(*       is_empty (vars_aexp ie) = true -> *)
(*       aeval st ie = i -> *)
(*       i >= length (ast a) -> *)
(*       i' < length (ast a') -> *)
(*       p |- <((a[ie] <- e, st, ast, true))> -->i_[DStore a' i']^^[OAWrite a i] *)
(*            <((skip, st, a' !-> upd i' (ast a') n; ast, true))> *)
(*   | ISM_Call : forall e i c st ast b, *)
(*       (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i -> *)
(*       nth_error p i = Some c -> *)
(*       p |- <((call e, st, ast, b))> -->i_[DStep]^^[OCall i] <((c, st, ast, b))> *)
(*   | ISM_Call_F : forall e i j c st ast b, *)
(*       (if negb (is_empty (vars_aexp e)) && b then 0 else aeval st e) = i -> *)
(*       i <> j -> *)
(*       nth_error p j = Some c -> *)
(*       p |- <((call e, st, ast, b))> -->i_[DForceCall j]^^[OForceCall] <((c, st, ast, true))> *)

(*     where "p |- <(( c , st , ast , b ))> -->i_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" := *)
(*     (ideal_eval_small_step p c st ast b ct stt astt bt ds os). *)

(* (* HIDE: This one now has again `_U` cases because of out-of-bounds array *)
(*    accesses at constant indices. Since the array sizes are also statically *)
(*    known, we could easily reject such programs statically.  *) *)

(* Reserved Notation *)
(*   "p '|-' '<((' c , st , ast , b '))>' '-->i*_' ds '^^' os '<((' ct , stt , astt , bt '))>'" *)
(*   (at level 40, c custom com at level 99, ct custom com at level 99, *)
(*    st constr, ast constr, stt constr, astt constr at next level). *)

(* Inductive multi_ideal (p:prog) (c:com) (st:state) (ast:astate) (b:bool) : *)
(*     com -> state -> astate -> bool -> dirs -> obs -> Prop := *)
(*   | multi_ideal_refl : p |- <((c, st, ast, b))> -->i*_[]^^[] <((c, st, ast, b))> *)
(*   | multi_ideal_trans (c':com) (st':state) (ast':astate) (b':bool) *)
(*                 (c'':com) (st'':state) (ast'':astate) (b'':bool) *)
(*                 (ds1 ds2 : dirs) (os1 os2 : obs) : *)
(*       p |-<((c, st, ast, b))> -->i_ds1^^os1 <((c', st', ast', b'))> -> *)
(*       p |-<((c', st', ast', b'))> -->i*_ds2^^os2 <((c'', st'', ast'', b''))> -> *)
(*       p |-<((c, st, ast, b))> -->i*_(ds1++ds2)^^(os1++os2) <((c'', st'', ast'', b''))> *)

(*           where "p |- <(( c , st , ast , b ))> -->i*_ ds ^^ os  <(( ct ,  stt , astt , bt ))>" := *)
(*     (multi_ideal p c st ast b ct stt astt bt ds os). *)

