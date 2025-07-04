(** * FlexSLH: Selective Ultimate SLH *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From SECF Require Import TestingSpecCT.
(* From SECF Require Import UltimateSLH. *)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".
(* TERSE: /HIDEFROMHTML *)

(* Tail recursive append to prevent stack overflows when testing *)
Fixpoint rev_append {A:Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1 => rev_append l1 (x :: l2)
  end.
Definition rev {A : Type} (l : list A) := rev_append l [].
Definition app {A:Type} (l1:list A) := rev_append (rev l1).
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Fixpoint vars_aexp (a:aexp) : list string :=
  match a with
  | ANum n => []
  | AId (Var i) => [i]
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ be ? a1 : a2 }> => vars_bexp be ++ vars_aexp a1 ++ vars_aexp a2
  end
with vars_bexp (a:bexp) : list string :=
  match a with
  | <{ true }> | <{ false }> => []
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => vars_aexp a1 ++ vars_aexp a2
  | <{ ~b }> => vars_bexp b
  | <{ b1 && b2 }> => vars_bexp b1 ++ vars_bexp b2
  end.

Definition label_of_aexp (P:pub_vars) (a:aexp) : label :=
  List.fold_left (fun l a => join l (apply P a)) (vars_aexp a) public.

Definition label_of_bexp (P:pub_vars) (b:bexp) : label :=
  List.fold_left (fun l b => join l (apply P b)) (vars_bexp b) public.

Lemma no_vars_public_bexp : forall P b,
  seq.nilp (vars_bexp b) = true ->
  label_of_bexp P b = public.
Proof. intros P b H. unfold label_of_bexp. destruct (vars_bexp b); eauto. Qed.

Lemma no_vars_public_aexp : forall P a,
  seq.nilp (vars_aexp a) = true ->
  label_of_aexp P a = public.
Proof. intros P a H. unfold label_of_aexp. destruct (vars_aexp a); eauto. Qed.

Definition AllPub : pub_vars := (_!-> public).
Definition AllSecret : pub_vars := (_!-> secret).

Lemma joining_to_secret : forall l' (xs:list string),
  List.fold_left (fun l b => join l l') xs secret = secret.
Proof. intros P xs. induction xs; eauto. Qed.

Lemma all_secret_bexp : forall b,
  seq.nilp (vars_bexp b) = false ->
  label_of_bexp AllSecret b = secret.
Proof.
  intros b H. unfold label_of_bexp. destruct (vars_bexp b) eqn:Eq; eauto.
  simpl. apply joining_to_secret.
Qed.

Lemma all_secret_aexp : forall a,
  seq.nilp (vars_aexp a) = false ->
  label_of_aexp AllSecret a = secret.
Proof.
  intros a H. unfold label_of_aexp. destruct (vars_aexp a) eqn:Eq; eauto.
  simpl. apply joining_to_secret.
Qed.

Fixpoint flex_slh (P:pub_vars) (c:com) : com :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ flex_slh P c1; flex_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{if be' then "b" := be' ? "b" : 1; flex_slh P c1
                   else "b" := be' ? 1 : "b"; flex_slh P c2 end}}>
  | <{{while be do c end}}> =>
      let be' := if label_of_bexp P be
        then be                  (* Selective SLH -- tracking speculation, but not masking *)
        else <{{"b" = 0 && be}}> (* Ultimate SLH -- tracking speculation and also masking *)
      in <{{while be' do "b" := be' ? "b" : 1; flex_slh P c end;
             "b" := be' ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    if label_of_aexp P i && apply P x then (* Selective SLH -- mask the value of public loads *)
      <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
    else
      let i' := if label_of_aexp P i
        then i (* Selective SLH -- mask the value of public loads *)
        else <{{("b" = 1) ? 0 : i}}> in (* Ultimate SLH -- mask private address of load *)
      <{{x <- a[[i']]}}>
(* Previous equivalent version, but worse for the proofs:
    then (* Selective SLH -- mask the value of public loads *)
      if apply P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
                   else <{{x <- a[[i]]}}>
    else (* Ultimate SLH -- mask private address of load *)
      <{{x <- a[[("b" = 1) ? 0 : i]] }}> *)
  | <{{a[i] <- e}}> =>
    let i' := if label_of_aexp P i
      then i (* Selective SLH -- no mask even if it's out of bounds! *)
      else <{{("b" = 1) ? 0 : i}}> (* Ultimate SLH *)
    in <{{a[i'] <- e}}> (* <- Doing nothing here in label_of_aexp P i = true case okay for Spectre v1,
                              but would be problematic for return address or code pointer overwrites *)
  end)%string.

(* For CT programs this is the same as sel_slh *)

Ltac rewrite_eq :=
  match goal with
  | H:_=_ |- _ => rewrite H; clear H
  | H:forall _, _=_ |- _ => rewrite H; clear H
  | _ => idtac
 end.

Module RelatingSelSLH.

  Lemma label_of_aexp_sound : forall P a,
    P |-a- a \IN label_of_aexp P a.
  Admitted.

  Lemma label_of_aexp_unique : forall P a l,
    P |-a- a \IN l ->
    l = label_of_aexp P a.
  Admitted.

  Lemma label_of_bexp_sound : forall P b,
    P |-b- b \IN label_of_bexp P b.
  Admitted.

  Lemma label_of_bexp_unique : forall P b l,
    P |-b- b \IN l ->
    l = label_of_bexp P b.
  Admitted.

  Lemma sel_slh_is_flex_slh : forall P PA c,
      ct_well_typed P PA c ->
      sel_slh P c = flex_slh P c.
  Proof.
    intros P PA c H. induction H; simpl; repeat rewrite_eq; try reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_bexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
    - apply label_of_aexp_unique in H. rewrite <- H. reflexivity.
  Qed.

End RelatingSelSLH.

(* The following standard IFC type system that just tracks explicit and implicit
   flows seems good enough for what we need. Most importantly, it gives us
   noninterference both sequentially and speculatively after applying flex_slh
   (see testing below). *)

Reserved Notation "P '&' PA ',' pc '|--' c" (at level 40).

Inductive well_typed (P PA : pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P & PA, pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P X) = true ->
      P & PA, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P & PA, pc |-- c1 ->
      P & PA, pc |-- c2 ->
      P & PA, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, (join pc l) |-- c2 ->
      P & PA, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \IN l ->
      P & PA, (join pc l) |-- c1 ->
      P & PA, pc |-- <{ while b do c1 end }>
  | WT_ARead : forall pc x a i li,
      P |-a- i \IN li ->
      can_flow (join pc (join li (apply PA a))) (apply P x) = true ->
      P & PA, pc |-- <{{ x <- a[[i]] }}>
  | WT_AWrite : forall pc a i e li l,
      P |-a- i \IN li ->
      P |-a- e \IN l ->
      can_flow (join pc (join li l)) (apply PA a) = true ->
      P & PA, pc |-- <{{ a[i] <- e }}>
where "P '&' PA ',' pc '|--' c" := (well_typed P PA pc c).

Definition nonempty_arrs (ast :astate) :Prop :=
  forall a, 0 < length (apply ast a).

(* TODO: This hypothesis is too weak and needs to be changed to execution
   prefixes in small-step semantics, like in UltimateSHL.v *)
Definition seq_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall stt1 stt2 astt1 astt2 os1 os2,
    <(st1, ast1)> =[ c ]=> <(stt1, astt1, os1)> ->
    <(st2, ast2)> =[ c ]=> <(stt2, astt2, os2)> ->
    os1 = os2.

Definition spec_same_obs c st1 st2 ast1 ast2 : Prop :=
  forall ds stt1 stt2 astt1 astt2 bt1 bt2 os1 os2,
    <(st1, ast1, false, ds)> =[ c ]=> <(stt1, astt1, bt1, os1)> ->
    <(st2, ast2, false, ds)> =[ c ]=> <(stt2, astt2, bt2, os2)> ->
    os1 = os2.

Definition relative_secure trans c st1 st2 ast1 ast2 : Prop :=
  seq_same_obs c st1 st2 ast1 ast2 ->
  spec_same_obs (trans c) st1 st2 ast1 ast2.

Definition ct_preservation trans : Prop := forall c,
  (forall st1 st2 ast1 ast2, seq_same_obs c st1 st2 ast1 ast2) ->
  (forall st1 st2 ast1 ast2, spec_same_obs (trans c) st1 st2 ast1 ast2).

Theorem relative_secure_implies_ct_preservation : forall trans,
  (forall c st1 st2 ast1 ast2, relative_secure trans c st1 st2 ast1 ast2) ->
  ct_preservation trans.
Proof.
  unfold relative_secure, ct_preservation.
  intros trans Hrs c Hct st1 st2 ast1 ast2. apply Hrs. apply Hct.
Qed.

(* The converse is generally not true *)
Lemma not_true_that_ct_preservation_implies_relative_secure : forall trans,
  ct_preservation trans ->
  (forall c st1 st2 ast1 ast2, relative_secure trans c st1 st2 ast1 ast2).
Proof.
  unfold relative_secure, ct_preservation.
  intros trans H c st1 st2 ast1 ast2 Hsrc. apply H. intros st1' st2' ast1' ast2'.
Abort.

Conjecture flex_slh_relative_secure :
  forall P PA c st1 st2 ast1 ast2,
    (* Selective SLH assumptions *)
    P & PA, public |-- c -> (* just that this is weaker (not ct_well_typed) *)
    pub_equiv P st1 st2 ->
    pub_equiv PA ast1 ast2 ->
    (* Joint assumptions *)
    unused "b" c ->
    apply st1 "b" = 0 ->
    apply st2 "b" = 0 ->
    (* Ultimate SLH assumptions  *)
    nonempty_arrs ast1 ->
    nonempty_arrs ast2 ->
    relative_secure (flex_slh P) c st1 st2 ast1 ast2.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String.

Notation label := TestingSpecCT.label.
Notation apply := TestingSpecCT.apply.
Notation join := TestingSpecCT.join.

Fixpoint wt_typechecker (P PA:pub_vars) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp P a)) (apply P X)
  | <{ c1 ; c2 }> => wt_typechecker P PA pc c1 && wt_typechecker P PA pc c2
  | <{ if b then c1 else c2 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1 &&
      wt_typechecker P PA (join pc (label_of_bexp P b)) c2
  | <{ while b do c1 end }> =>
      wt_typechecker P PA (join pc (label_of_bexp P b)) c1
  | <{{ x <- a[[i]] }}> =>
      can_flow (join pc (join (label_of_aexp P i) (apply PA a))) (apply P x)
  | <{{ a[i] <- e }}> =>
      can_flow (join pc (join (label_of_aexp P i) (label_of_aexp P e))) (apply PA a)
  end.

Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Definition gen_pub_aexp_leaf (P : pub_vars) : G aexp :=
  oneOf (liftM ANum arbitrary ;;;
         (let pubs := map Var (filter (apply P) (map_dom (snd P))) in
         if seq.nilp pubs then []
         else [liftM AId (elems_ (Var "X0"%string) pubs)] ) ).

Fixpoint gen_pub_aexp (sz:nat) (P:pub_vars) : G aexp :=
  match sz with
  | O => thunkGen (fun _ => gen_pub_aexp_leaf P)
  | S sz' =>
      freq [ (3, thunkGen (fun _ => gen_pub_aexp_leaf P));
             (sz, thunkGen (fun _ => liftM2 APlus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMinus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)));
             (sz, thunkGen (fun _ => liftM2 AMult (gen_pub_aexp sz' P) (gen_pub_aexp sz' P)))]
  end.

Definition gen_secure_asgn (P:pub_vars) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  e <- (if apply P x then gen_pub_aexp 1 P else arbitrarySized 1);;
  ret <{ x := e }>.

Definition gen_name (P:pub_vars) (label:bool) : G (option string) :=
  let names := filter (fun x => Bool.eqb label (apply P x))
                      (map_dom (snd P)) in
  match names with
  | x0 :: _ => liftM Some (elems_ x0 names)
  | [] => ret None
  end.

Definition gen_asgn_in_ctx (gen_asgn : pub_vars -> G com)
    (pc:label) (P:pub_vars) : G com :=
  if pc then gen_asgn P
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      e <- arbitrarySized 1;;
      ret <{ x := e }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_aread (P:pub_vars) (PA:pub_arrs) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  if apply P x then
    a <- gen_name PA public;; (* public array *)
    match a with
    | Some a =>
        i <- gen_pub_aexp 1 P;; (* public index *)
        ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end
  else
    a <- arbitrary;;
    i <- arbitrarySized 1;;
    ret <{ x <- a[[i]] }>.

Definition gen_aread_in_ctx (gen_aread : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_aread P PA
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      a <- arbitrary;;
      i <- arbitrarySized 1;;
      ret <{ x <- a[[i]] }>
    | None => ret <{ skip }>
    end.

Definition gen_secure_awrite (P:pub_vars) (PA:pub_arrs) : G com :=
  let arrs := map_dom (snd PA) in
  a <- elems_ "A0"%string arrs;;
  if apply PA a then
    i <- gen_pub_aexp 1 P;; (* public index *)
    e <- gen_pub_aexp 1 P;; (* public expression *)
    ret <{ a[i] <- e }>
  else
    i <- arbitrarySized 1;;
    e <- arbitrarySized 1;;
    ret <{ a[i] <- e }>.

Definition gen_awrite_in_ctx (gen_awrite : pub_vars -> pub_arrs -> G com)
    (pc:label) (P:pub_vars) (PA:pub_arrs) : G com :=
  if pc then gen_awrite P PA
  else
    a <- gen_name PA secret;; (* secret array *)
    match a with
    | Some a =>
      i <- arbitrarySized 1;;
      e <- arbitrarySized 1;;
      ret <{ a[i] <- e }>
    | None => ret <{ skip }>
    end.

Fixpoint gen_com_rec (gen_asgn : pub_vars -> G com)
                     (gen_aread : pub_vars -> pub_arrs -> G com)
                     (gen_awrite : pub_vars -> pub_arrs -> G com)
                     (P:pub_vars) (PA:pub_arrs) (sz:nat) : G com :=
  match sz with
  | O => freq [(1, ret Skip);
               (4, thunkGen (fun _ => gen_asgn P));
               (4, thunkGen (fun _ => gen_aread P PA));
               (4, thunkGen (fun _ => gen_awrite P PA))]
  | S sz' =>
      freq [ (1, ret Skip);
             (sz, thunkGen (fun _ => gen_asgn P));
             (sz, thunkGen (fun _ => gen_aread P PA));
             (sz, thunkGen (fun _ => gen_awrite P PA));
             (2*sz, thunkGen (fun _ =>
                    liftM2 Seq (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')
                               (gen_com_rec gen_asgn gen_aread gen_awrite P PA sz')));
             (sz, thunkGen (fun _ =>
                  b <- arbitrarySized 2;;
                  liftM3 If (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                 (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                 (gen_awrite_in_ctx gen_awrite (label_of_bexp P b))
                                 P PA sz')));
             (sz, thunkGen (fun _ =>
                  b <- arbitrarySized 2;;
                  (* Trying to generate assignment to one of the loop variables *)
                  casgn <- gen_asgn_in_ctx gen_asgn (label_of_bexp P b) P;;
                  cend <- match casgn with
                  | <{y := e}> =>
                      if existsb (String.eqb y) (vars_bexp b) then ret casgn
                      else
                        match find (fun x => Bool.eqb (apply P y)
                                                      (apply P x)) (vars_bexp b) with
                        | Some x => ret <{x := e}>
                        | None => ret <{skip}>
                        end
                  | _ => ret <{skip}>
                  end;;
                  c <- gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b))
                                   (gen_aread_in_ctx gen_aread (label_of_bexp P b))
                                   (gen_awrite_in_ctx gen_aread (label_of_bexp P b))
                                   P PA sz';;
                  ret (While b <{c;cend}>)))]
  end.

Definition gen_wt_com := gen_com_rec gen_secure_asgn gen_secure_aread gen_secure_awrite.

Sample gen_pub_vars.

Definition someP := (false, [("X0", false); ("X1", true); ("X2", true);
                             ("X3", true); ("X4", false); ("X5", false)])%string.

Sample gen_pub_arrs.

Definition somePA := (true, [("A0", true); ("A1", true); ("A2", false)])%string.

Sample (sized (gen_wt_com someP somePA)).

(* Strange that we need such a big hack here, but if we use AllPub we don't get
   public variables/arrays generated *)
Definition gen_com := gen_wt_com
                        (true, [("X0", true); ("X1", true); ("X2", true);
                          ("X3", true); ("X4", true); ("X5", true)])%string
                        (true, [("A0", true); ("A1", true); ("A2", true)])%string.

Sample (sized gen_com).

(* Preventing empty arrays *)
Definition gen_astate : G astate :=
  ld <- choose (1,10);;
  d <- vectorOf ld arbitrary;;
  l0 <- choose (1,10);;
  v0 <- vectorOf l0 arbitrary;;
  l1 <- choose (1,10);;
  v1 <- vectorOf l1 arbitrary;;
  l2 <- choose (1,10);;
  v2 <- vectorOf l2 arbitrary;;
  ret (d, [("A0",v0); ("A1",v1); ("A2",v2)]) % string.

(* Extract Constant defNumTests => "1000000". *)

(* We first validate that our generator produces well-typed commands *)

QuickChick (forAll gen_pub_vars (fun P =>
           (forAll gen_pub_arrs (fun PA =>
           (forAll (sized (gen_wt_com P PA)) (fun (c:com) =>
             wt_typechecker P PA public c)))))).

(* Noninterference for source sequential execution *)

Definition check_sequential_noninterference P PA P' PA' c : Checker :=
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 =>
  forAll gen_astate (fun a1 =>
  forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
    let r1 := cteval_engine 10 c s1 a1 in
    let r2 := cteval_engine 10 c s2 a2 in
    match (r1, r2) with
    | (Some (s1', a1', os1), Some (s2', a2', os2)) =>
        checker ((pub_equivb P' s1' s2') && (pub_equivb_astate PA' a1' a2'))
    | _ => checker tt (* discard *)
    end
)))).

QuickChick (forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
    check_sequential_noninterference P PA P PA c)))).

(* For testing relative security we do taint tracking of sequential executions
   (as a variant of Lucie's interpreter). We use this to track which initial
   values of variables and arrays affect CT observations. *)

Definition taint : Type := list (var_id + arr_id).

#[export] Instance showTaint : Show (var_id + arr_id) :=
  {show := fun x =>
     match x with
     | inl x => show x
     | inr a => show a
     end}.

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

Definition sum_eqb (s1 s2 : (var_id + arr_id)) : bool :=
  match s1, s2 with
  | inl x1, inl x2
  | inr x1, inr x2 => String.eqb x1 x2
  | _, _ => false
  end.

Definition join_taints t1 t2 := remove_dupes sum_eqb (t1 ++ t2).

Module TaintTracking.

Definition tstate := total_map taint.
Definition tastate := total_map taint.

Definition input_st : Type := state * astate * tstate * tastate * taint.
Inductive output_st (A : Type) : Type :=
  | ROutOfFuel : obs -> input_st -> output_st A
  | ROutOfBounds : obs -> input_st -> output_st A
  | ROk : A -> obs -> input_st -> output_st A.

(* An 'evaluator A'. This is the monad.
   It transforms an input state into an output state, returning an A. *)
Record evaluator (A : Type) : Type := mkEvaluator
  { evaluate : input_st -> output_st A }.
(* An interpreter is a special kind of evaluator *)
Definition interpreter: Type := evaluator unit.

(* Generic monad operators *)
#[export] Instance monadEvaluator: Monad evaluator :=
  { ret := fun A value => mkEvaluator A (fun (ist : input_st) => ROk A value [] ist);
    bind := fun A B e f =>
      mkEvaluator B (fun (ist : input_st) =>
        match evaluate A e ist with
        | ROk _ value os1 ist'  =>
            match evaluate B (f value) ist' with
            | ROk _ value os2 ist'' => ROk B value (os1 ++ os2) ist''
            | ROutOfFuel _ os2 ist'' => ROutOfFuel B (os1 ++ os2) ist''
            | ROutOfBounds _ os2 ist'' => ROutOfBounds B (os1 ++ os2) ist''
            end
        | ROutOfFuel _ os ist' => ROutOfFuel B os ist'
        | ROutOfBounds _ os ist' => ROutOfBounds B os ist'
        end
      )
   }.

(* specialized operators *)
Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _, _) := ist in
    evaluate _ (ret (apply st name)) ist
  ).
Definition get_arr (name : string): evaluator (list nat) :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, ast, _, _, _) := ist in
    evaluate _ (ret (apply ast name)) ist
  ).
Definition set_var (name : string) (value : nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast, tobs) := ist in
    let new_st := (name !-> value ; st) in
    evaluate _ finish (new_st, ast, tst, tast, tobs)
  ).
Definition set_arr (name : string) (value : list nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast, tobs) := ist in
    let new_ast := (name !-> value ; ast) in
    evaluate _ finish (st, new_ast, tst, tast, tobs)
  ).
Definition eval_aexp (a : aexp) : evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _, _) := ist in
    let v := aeval st a in
    evaluate _ (ret v) ist
  ).
Definition eval_bexp (b : bexp) : evaluator bool :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _, _) := ist in
    let v := beval st b in
    evaluate _ (ret v) ist
  ).
Definition raise_out_of_bounds {a:Type} : evaluator a :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROutOfBounds _ [] ist
  ).
Definition raise_out_of_fuel {a:Type} : evaluator a :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROutOfFuel _ [] ist
  ).
Definition observe (o : observation) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROk _ tt [o] ist
  ).

Definition get_taint_of_vars (xs:list string) : evaluator taint :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, _, tst, _, _) := ist in
    evaluate _ (ret (remove_dupes sum_eqb (List.concat (map (apply tst) xs)))) ist).

Definition get_taint_of_arr (a:string) : evaluator taint :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, _, _, tast, _) := ist in
    evaluate _ (ret (apply tast a)) ist).

Definition set_var_taint (x : string) (t : taint) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast, tobs) := ist in
    let new_tst := (x !-> remove_dupes sum_eqb t ; tst) in
    evaluate _ finish (st, ast, new_tst, tast, tobs)).

Definition add_arr_taint (a : string) (t : taint) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, tst, tast, tobs) := ist in
    let new_tast := (a !-> (join_taints t (apply tast a)); tast) in
    evaluate _ finish (st, ast, tst, new_tast, tobs)).

Definition add_obs_taint (t : taint) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    (* trace ("add_obs_taint:"++show t++nl) ( *)
    let '(st, ast, tst, tast, tobs) := ist in
    let new_tobs := join_taints t tobs in
    evaluate _ finish (st, ast, tst, tast, new_tobs)).

Fixpoint taint_track (f : nat) (c : com) : interpreter :=
  match f with
  | O => raise_out_of_fuel
  | S f =>

  match c with
  | <{ skip }> =>
      finish
  | <{ x := e }> =>
      v <- eval_aexp e;;
      set_var x v;;
      t <- get_taint_of_vars (vars_aexp e);;
      set_var_taint x t
  | <{ c1 ; c2 }> =>
      taint_track f c1;;
      taint_track f c2
  | <{ if b then ct else cf end }> =>
      condition <- eval_bexp b;;
      let next_c := if Bool.eqb condition true then ct else cf in
      observe (OBranch condition);;
      tb <- get_taint_of_vars (vars_bexp b);;
      add_obs_taint tb;;
      taint_track f next_c
  | <{ while be do c end }> =>
    taint_track f <{
      if be then
        c;
        while be do c end
      else
        skip
      end
    }>
  | <{ x <- a[[ie]] }> =>
      i <- eval_aexp ie;;
      l <- get_arr a;;
      if (i <? List.length l) then
        observe (OARead a i);;
        set_var x (nth i l 0);;
        ti <- get_taint_of_vars (vars_aexp ie);;
        add_obs_taint ti;;
        ta <- get_taint_of_arr a;;
        set_var_taint x (join_taints ti ta)
      else
        raise_out_of_bounds
  | <{ a[ie] <- e }> =>
      n <- eval_aexp e;;
      i <- eval_aexp ie;;
      l <- get_arr a;;
      if (i <? List.length l) then
        observe (OAWrite a i);;
        set_arr a (upd i l n);;
        ti <- get_taint_of_vars (vars_aexp ie);;
        add_obs_taint ti;;
        te <- get_taint_of_vars (vars_aexp e);;
        add_arr_taint a (join_taints ti te)
      else
        raise_out_of_bounds
  end
  end.

End TaintTracking.

Fixpoint split_sum_list {A B : Type} (l : list (A + B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | inl a :: xs => let (la, lb) := split_sum_list xs in (a :: la, lb)
  | inr b :: xs => let (la, lb) := split_sum_list xs in (la, b :: lb)
  end.

Definition taint_tracking (f : nat) (c : com) (st : state) (ast : astate)
    : option (obs * list string * list string) :=
  let tst := ([], map (fun x => (x,[@inl var_id arr_id (Var x)])) (map_dom (snd st))) in
  let tast := ([], map (fun a => (a,[@inr var_id arr_id (Arr a)])) (map_dom (snd ast))) in
  let ist := (st, ast, tst, tast, []) in
  match TaintTracking.evaluate _ (TaintTracking.taint_track f c) ist with
  | TaintTracking.ROk _ tt os (_, _, _, _, tobs) =>
  (* | TaintTracking.ROutOfFuel _ os (_, _, _, _, tobs) => *)
      let (vars, arrs) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb (map var_id_to_string vars),
                remove_dupes String.eqb (map arr_id_to_string arrs))
  | _ => None
  end.

(* We first test the taint_tracking itself: it needs to enforce that if we make
   the initial values of the leaked variables/arrays public we can vary all the
   remaining secret variables/arrays and still obtain the same CT leakage. *)

(* Extract Constant defNumTests => "1000000". *)

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (os1', tvars, tarrs) =>
      (* trace ("Leaked vars: " ++ show tvars ++ " arrs: " ++ show tarrs ++ nl) ( *)
      (* collect (show (List.length tvars + List.length tarrs)) ( *)
      let P := (false, map (fun x => (x,true)) tvars) in
      let PA := (false, map (fun a => (a,true)) tarrs) in
      forAll (gen_pub_equiv P s1) (fun s2 =>
      forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (_, _, os2') => checker (*trace (if obs_eqb os1' os2' then "" else "os1':"++show os1'++"os2':"++show os2'++nl*) (obs_eqb os1' os2')
      | None => checker false (* fail *)
      end))
   | None => checker tt (* discard *)
   end)))).

(* Testing noninterference for target speculative execution *)

Definition extend_pub (P:pub_vars) (xs:list string) :=
  fold_left (fun P x => x !-> public; P) xs P.

Definition check_speculative_noninterference P PA P' PA' c hardened : Checker :=
  forAll gen_state (fun s1 =>
  let s1 := ("b" !-> 0; s1) in
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (os1', tvars, tarrs) =>
      (* collect (show (List.length os1')) ( *)
      (* collect (show (List.length (tvars ++ tarrs))) ( *)
      forAll (gen_pub_equiv (extend_pub P tvars) s1) (fun s2 =>
      let s2 := ("b" !-> 0; s2) in
      forAll (gen_pub_equiv_and_same_length (extend_pub PA tarrs) a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (_s2', _a2', os2') =>
          (* implication (obs_eqb os1' os2') -- no longer needed *)
          (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
             (fun '(ds, s1', a1', b', os1) =>
                (* collect (show (List.length ds)) ( *)
                match spec_eval_engine hardened s2 a2 false ds with
                | Some (s2', a2', b'', os2) =>
                    checker (Bool.eqb b' b'' && (pub_equivb P' s1' s2') &&
                           (b' || (* <-- needed since we don't (yet) mask stores *)
                                  pub_equivb_astate PA' a1' a2'))
                | None => checker tt (* discard -- doesn't seem to happen *)
                end))
      | None => checker tt (* discard -- doesn't seem to happen *)
      end))
  | None => checker tt (* discard *)
  end)).

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_speculative_noninterference P PA P PA c (flex_slh P c))))).

(* One may wonder if this property is enforced ENTIRELY by the source type
   system and would hold for any transformation that doesn't introduce (explicit
   or implicit) information flows, including no transformation at all?
   This doesn't work though because of out of bounds loads, and testing can
   find it -- SHOULD FAIL: *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_speculative_noninterference P PA P PA c c)))).

(* In fact this doesn't even work for CT programs -- SHOULD FAIL: *)

Definition gen_ct_well_typed P PA := sized (gen_ct_well_typed_sized P PA).

QuickChick (
  forAllShrink gen_pub_vars shrink (fun P =>
  forAllShrink gen_pub_arrs shrink (fun PA =>
  forAllShrink (gen_ct_well_typed P PA) (shrink_ct_well_typed P PA) (fun c =>
  check_speculative_noninterference P PA P PA c c)))).

(* This was the main reason for introducing sel_slh, which satisfies something
   even stronger as we proved in SpecCT.v (and we are testing it anyway below). *)

(* Testing flex_slh_relative_secure *)

Definition check_relative_security P PA c hardened : Checker :=
  forAll gen_state (fun s1 =>
  let s1 := ("b" !-> 0; s1) in
  forAll gen_astate (fun a1 =>
  let r1 := taint_tracking 10 c s1 a1 in
  match r1 with
  | Some (os1', tvars, tarrs) =>
      collect (show (List.length os1')) (
      (* collect (show (List.length (tvars ++ tarrs))) ( *)
      forAll (gen_pub_equiv (extend_pub P tvars) s1) (fun s2 =>
      let s2 := ("b" !-> 0; s2) in
      forAll (gen_pub_equiv_and_same_length (extend_pub PA tarrs) a1) (fun a2 =>
      let r2 := cteval_engine 10 c s2 a2 in
      match r2 with
      | Some (s2', a2', os2') =>
          (* implication (obs_eqb os1' os2') -- no longer needed *)
          (forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
             (fun '(ds, s1', a1', b', os1) =>
                match spec_eval_engine hardened s2 a2 false ds with
                | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
                | None => checker tt (* discard -- doesn't seem to happen *)
                end))
      | None => checker tt (* discard -- doesn't seem to happen *)
      end)))
  | None => checker tt (* discard *)
  end)).

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  check_relative_security P PA c (flex_slh P c))))).

(* Also testing Unwinding Lemma for Ideal Misspeculated Executions here, not for ideal semantics, but for the translation *)

Definition check_ideal_misspeculated_unwinding hardened s1 s2 : Checker :=
  let s1 := ("b" !-> 1; s1) in
  let s2 := ("b" !-> 1; s2) in
  forAll gen_astate (fun a1 =>
  forAll gen_astate (fun a2 => (* same length doesn't seem not needed *)
  forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100)
    (fun '(ds, s1', a1', b', os1) =>
       match spec_eval_engine hardened s2 a2 false ds with
       | Some (s2', a2', b'', os2) => checker (obs_eqb os1 os2)
       | None => checker tt (* discard *)
       end))).

(* Unwinding lemma as stated in UltimateSLH.v fails for flex_slh! -- SHOULD FAIL!
   Didn't expect it, but it makes sense in retrospect:
   for flex_slh public variables should *never* contain secrets,
   and our type-system ensures that *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_ideal_misspeculated_unwinding (flex_slh P c) s1 s2)))))).

(* A variant of the unwinding lemma works for flex_slh,
   but we need to only generate equivalent initial states *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (sized (gen_wt_com P PA)) (fun c =>
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_ideal_misspeculated_unwinding (flex_slh P c) s1 s2)))))).

(* Directly testing also the top-level statement for our naive Ultimate SLH,
   even if it is KIND OF(!) just a special case of flex_slh AllSecret. *)

Fixpoint naive_ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ naive_ultimate_slh c1; naive_ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; naive_ultimate_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; naive_ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; naive_ultimate_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
    <{{x <- a[[("b" = 1) ? 0 : i]] }}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

Module RelatingOurUltimateSLH.
  (* naive_ultimate_slh above is just a suboptimal version of `flex_slh AllSecret` *)

  (* Suboptimal because it even masks constant expressions, which clearly cannot
     leak secrets via observations. Still without such constant expressions we
     can prove it's the same. Here is a crude way of proving this using axioms
     that are generally false. *)

  Axiom no_constant_bexps : forall b, seq.nilp (vars_bexp b) = false.
  Axiom no_constant_aexps : forall a, seq.nilp (vars_aexp a) = false.

  Lemma naive_ultimate_slh_is_flex_slh :
    forall c, naive_ultimate_slh c = flex_slh AllSecret c.
  Proof.
    pose proof (fun b => all_secret_bexp b (no_constant_bexps b)).
    pose proof (fun b => all_secret_aexp b (no_constant_aexps b)).
    intros c. induction c; simpl; repeat rewrite_eq; reflexivity.
  Qed.

End RelatingOurUltimateSLH.

(* Testing naive_ultimate_slh *)

(* Here is where taint_tracking really shines, since it halves the number of
   discards, and much more than that for long observations traces *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_relative_security AllSecret AllSecret c (naive_ultimate_slh c)))).

QuickChick (
  forAll (sized gen_com) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_ideal_misspeculated_unwinding (naive_ultimate_slh c) s1 s2)))).

(* Finally, we check a very weak AllSecret instantiation of speculative
   noninterference, which only gives us something about the final flag. *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_speculative_noninterference AllSecret AllSecret AllSecret AllSecret
     c (naive_ultimate_slh c)))).

(* This works without any protection though, probably because of the way our
   speculative semantics works and the fact that we share the directions. *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_speculative_noninterference AllSecret AllSecret AllSecret AllSecret
     c c))).

(* There is no other sound instantiation of P and PA that would satisfy the
   conclusion of check_speculative_noninterference for naive_ultimate_slh and
   arbitrary programs though. Here is a very naive attempt -- SHOULD FAIL! *)

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAllShrink gen_pub_vars shrink (fun P =>
  forAllShrink gen_pub_arrs shrink (fun PA =>
  (check_speculative_noninterference P PA P PA c (naive_ultimate_slh c)))))).

(* Now defining an optimized version of Ultimate SLH, even if it is
   just a special case of flex_slh AllSecret (we prove this below). *)

Fixpoint opt_ultimate_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ opt_ultimate_slh c1; opt_ultimate_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      let be' := if seq.nilp (vars_bexp be) then be (* optimized *)
                                            else <{{"b" = 0 && be}}> in
        <{{if be' then "b" := be' ? "b" : 1; opt_ultimate_slh c1
                  else "b" := be' ? 1 : "b"; opt_ultimate_slh c2 end}}>
  | <{{while be do c end}}> =>
      let be' := if seq.nilp (vars_bexp be) then be (* optimized *)
                                            else <{{"b" = 0 && be}}> in
        <{{while be' do "b" := be' ? "b" : 1; opt_ultimate_slh c end;
           "b" := be' ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> =>
      let i' := if seq.nilp (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                          else <{{("b" = 1) ? 0 : i}}> in
        <{{x <- a[[i']]}}>
  | <{{a[i] <- e}}> =>
      let i' := if seq.nilp (vars_aexp i) then i (* optimized -- no mask even if it's out of bounds! *)
                                          else <{{("b" = 1) ? 0 : i}}> in
        <{{a[i'] <- e}}> (* <- Doing nothing here in the seq.nilp (vars_aexp i) case okay for Spectre v1,
                               but problematic for return address or code pointer overwrites *)
  end)%string.

(* This `opt_ultimate_slh` version is just `flex_slh AllSecret` *)

Lemma opt_ultimate_slh_is_flex_slh :
  forall c, opt_ultimate_slh c = flex_slh AllSecret c.
Proof.
  pose proof all_secret_bexp as Hb.
  pose proof all_secret_aexp as Ha.
  intros c. induction c; simpl; repeat rewrite_eq; try reflexivity.
  - destruct (seq.nilp (vars_bexp be)) eqn:Eq.
    + eapply no_vars_public_bexp in Eq. rewrite Eq. reflexivity.
    + erewrite Hb; eauto.
  - destruct (seq.nilp (vars_bexp be)) eqn:Eq.
    + eapply no_vars_public_bexp in Eq. rewrite Eq. reflexivity.
    + erewrite Hb; eauto.
  - destruct (seq.nilp (vars_aexp i)) eqn:Eq.
    + eapply no_vars_public_aexp in Eq. rewrite Eq. reflexivity.
    + erewrite Ha; eauto.
  - destruct (seq.nilp (vars_aexp i)) eqn:Eq.
    + eapply no_vars_public_aexp in Eq. rewrite Eq. reflexivity.
    + erewrite Ha; eauto.
Qed.

(* Testing opt_ultimate_slh *)

QuickChick (
  forAll (sized gen_com) (fun c =>
  (check_relative_security AllSecret AllSecret c (opt_ultimate_slh c)))).

QuickChick (
  forAll (sized gen_com) (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_ideal_misspeculated_unwinding (opt_ultimate_slh c) s1 s2)))).

(** Now testing Standard SLH and Sel SLH *)

(** Standard SLH -- INSECURE FOR ARBITRARY PROGRAMS! SHOULD FAIL! *)

Definition slh := sel_slh AllPub.

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  check_relative_security AllSecret AllSecret c (slh c))).

(* Standard SLH is secure for constant-time programs though *)
QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_relative_security P PA c (slh c))))).

(* But then for constant-time programs we should better use sel_slh *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_relative_security P PA c (sel_slh P c))))).

(* Also testing unwinding lemma -- WRONG FOR ARBITRARY PROGRAMS! SHOULD FAIL! *)
QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAllShrink gen_state shrink (fun s1 =>
  forAllShrink gen_state shrink (fun s2 =>
  check_ideal_misspeculated_unwinding (slh c) s1 s2)))).

(* This works for constant-time programs on equivalent initial states though *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c => (* <- extra assumption *)
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_ideal_misspeculated_unwinding (slh c) s1 s2)))))).

(* For constant-time programs we can use sel_slh though *)
QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c => (* <- extra assumption *)
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_ideal_misspeculated_unwinding (sel_slh P c) s1 s2)))))).

(* Finally, we can also check speculative noninterference for constant-time
   programs, but then for sel_slh we already proved a stronger version, which
   doesn't assume agreement of source leakages, so this is not a surprise. *)

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed P PA) (fun c =>
  check_speculative_noninterference P PA P PA c (sel_slh P c))))).

(* Much more interestingly, I was expecting this to hold even for our weaker
   typing notion. But QuickChick found the beautiful counterexample below
   involving a loop that branches on an unmasked secret variable that gets
   assigned in the loop body and makes the directions go out of sync in the two
   executions, so the following public if gets different directions and based on
   that assigns or not to a public variable. So a new kind of implicit flow
   coming from running with different directions. SHOULD FAIL! *)

(* Since this is not consistently found with 10000 tests and shrinking doesn't
   work perfectly consistently even with forAllShrinkNonDet I've hard-coded the
   counterexample for now. Otherwise just set a larger number of tests and
   comment out the forAllShrinkNonDets: *)

(* Extract Constant defNumTests => "100000". *)

Definition forAllShrinkNonDet {A prop : Type} {_ : Checkable prop} `{Show A}
           (n : nat) (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=
  let repeated_shrinker (x : A) : list A :=
    List.concat (List.repeat (shrinker x) n) in
  bindGen gen (fun x : A =>
                 shrinking repeated_shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

Definition X0 := "X0"%string.
Definition X2 := "X2"%string.
Definition A0 := "A0"%string.
QuickChick (
  (* forAllShrinkNonDet 100 gen_pub_vars shrink (fun P => *)
  (* forAllShrinkNonDet 100 gen_pub_arrs shrink (fun PA => *)
  (* forAllShrinkNonDet 100 (sized (gen_wt_com P PA)) shrink (fun c => *)
  let P := (true, [("X0", true); ("X1", true); ("X2", false); ("X3", false); ("X4", false); ("X5", false)])%string in
  let PA := (true, [("A0", false); ("A1", true); ("A2", true)])%string in
  let c := <{{while (1 > X2) do (X2 <- A0[[0]]) end ; if (X0 > 0) then X0 := 0 else skip end}}> in
  implication (wt_typechecker P PA public c)
  (check_speculative_noninterference P PA P PA c (sel_slh P c))).

(* Counterexamples also exist without while loops, but they are harder to find: *)
(* <{{if (0 <= 0) then (X0 := X0) else (if (1 > X3) then skip else (X0 <- A0[[X0]]) end) end}}> *)

(** * Exorcising Spectre SLH -- INSECURE! SHOULD FAIL! *)

Fixpoint exorcised_slh (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ exorcised_slh c1; exorcised_slh c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; exorcised_slh c1
                          else "b" := ("b" = 0 && be) ? 1 : "b"; exorcised_slh c2 end}}>
  | <{{while be do c end}}> =>
      <{{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; exorcised_slh c end;
         "b" := ("b" = 0 && be) ? 1 : "b"}}>
  | <{{x <- a[[i]]}}> => (* only masking output, this is wrong! *)
      <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
  | <{{a[i] <- e}}> => <{{a[("b" = 1) ? 0 : i] <- e}}>
  end)%string.

QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  check_relative_security AllSecret AllSecret c (exorcised_slh c))).

(* Also testing unwinding lemma -- SHOULD FAIL! *)
QuickChick (
  forAllShrink (sized gen_com) shrink (fun c =>
  forAll gen_state (fun s1 =>
  forAll gen_state (fun s2 =>
  check_ideal_misspeculated_unwinding (exorcised_slh c) s1 s2)))).

(** * Flow-sensitive IFC tracking for flex_slh *)

(* Since we want to apply flex_slh to all programs, without rejecting anything
   as "ill-typed", we implement flow-sensitive static IFC tracking: *)

Inductive acom : Type :=
  | ASkip
  | AAsgn (x : string) (e : aexp)
  | ASeq (c1 c2 : acom)
  | AIf (be : bexp) (lbe : label) (c1 c2 : acom)
  | AWhile (be : bexp) (lbe : label) (c : acom)
  | AARead (x : string) (lx : label) (a : string) (i : aexp)  (li : label)
  | AAWrite (a : string) (i : aexp) (li : label) (e : aexp).

Declare Custom Entry acom.
Declare Scope acom_scope.

Notation "'<[' e ']>'" := e (at level 0, e custom acom at level 99) : acom_scope.
Notation "( x )" := x (in custom acom, x at level 99) : acom_scope.
Notation "x" := x (in custom acom at level 0, x constr at level 0) : acom_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom acom at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : acom_scope.

Open Scope acom_scope.

Notation "'skip'"  :=
  ASkip (in custom acom at level 0) : acom_scope.
Notation "x := y"  :=
  (AAsgn x y)
    (in custom acom at level 0, x constr at level 0,
      y custom acom at level 85, no associativity) : acom_scope.
Notation "x ; y" :=
  (ASeq x y)
    (in custom acom at level 90, right associativity) : acom_scope.
Notation "'if' x '@' lbe 'then' y 'else' z 'end'" :=
  (AIf x lbe y z)
    (in custom acom at level 89, x custom acom at level 99,
     y at level 99, z at level 99) : acom_scope.
Notation "'while' x '@' lbe 'do' y 'end'" :=
  (AWhile x lbe y)
    (in custom acom at level 89, x custom acom at level 99, y at level 99) : acom_scope.
Notation "x '@@' lx '<-' a '[[' i '@' li ']]'"  :=
  (AARead x lx a i li)
     (in custom acom at level 0, x constr at level 0,
      a at level 85, i custom acom at level 85, no associativity) : acom_scope.
Notation "a '[' i '@' li  ']'  '<-' e"  :=
  (AAWrite a i li e)
     (in custom acom at level 0, a constr at level 0,
      i custom acom at level 0, e custom acom at level 85,
         no associativity) : acom_scope.

Fixpoint erase (ac:acom) : com :=
  match ac with
  | <[ skip ]> => <{skip}>
  | <[ X := ae ]> => <{X := ae}>
  | <[ ac1 ; ac2 ]> => <{ erase ac1; erase ac2 }>
  | <[ if be@lbe then ac1 else ac2 end ]> => <{ if be then erase ac1
                                                      else erase ac2 end }>
  | <[ while be @ lbe do ac1 end ]> => <{ while be do erase ac1 end }>
  | <[ X@@lx <- a[[i@li]] ]> => <{ X <- a[[i]] }>
  | <[ a[i@li] <- e ]> => <{ a[i] <- e }>
  end.

Definition join_total_maps (P1 P2: pub_vars) : pub_vars :=
  match P1, P2 with
  | (d1,m1), (d2,m2) =>
      let dm := remove_dupes String.eqb (map_dom m1 ++ map_dom m2) in
      let m := List.map (fun x => (x, join (apply P1 x) (apply P2 x))) dm in
      (join d1 d2, m)
  end.

(* First attempt at implementing fully permissive static IFC tracking *)

Fixpoint static_tracking_naive (P:pub_vars) (PA:pub_arrs) (pc:label) (c:com)
  : (pub_vars*pub_arrs*acom) :=
  match c with
  | <{ skip }> => (P, PA, <[skip]>)
  | <{ X := ae }> => (X !-> (join pc (label_of_aexp P ae)); P, PA, <[X := ae]>)
  | <{ c1; c2 }> => let '(P1, PA1, ac1) := static_tracking_naive P PA pc c1 in
                     let '(P2, PA2, ac2) := static_tracking_naive P1 PA1 pc c2 in
                     (P2, PA2, <[ ac1; ac2 ]>)
  | <{ if be then c1 else c2 end }> =>
      let lbe := label_of_bexp P be in
      let '(P1, PA1, ac1) := static_tracking_naive P PA (join pc lbe) c1 in
      let '(P2, PA2, ac2) := static_tracking_naive P PA (join pc lbe) c2 in
      (join_total_maps P1 P2, join_total_maps PA1 PA2,
        <[ if be@lbe then ac1 else ac2 end ]>)
  | <{ while be do c1 end }> =>
      let lbe := label_of_bexp P be in
      let '(P1, PA1, ac1) := static_tracking_naive P PA (join pc lbe) c1 in
      (join_total_maps P1 P, join_total_maps PA1 PA,
        <[ while be@lbe do ac1 end ]>)
      (* We can't be sure we converged so quickly.  Having only two security
         levels doesn't seem enough!  In the worst case need to iterate over all
         assigned vars + arrs (see below) *)
  | <{ X <- a[[i]] }> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (apply PA a)) in
      (X !-> lx; P, PA, <[ X@@lx <- a[[i@li]] ]>)
  | <{ a[i] <- e }> =>
      let li := label_of_aexp P i in
      let la := join (apply PA a) (join pc (join li (label_of_aexp P e))) in
      (* It seems likely that the arrays will all become private quite quickly;
         but it's not what we see in the experiments below (search for collect). *)
      (P, a !-> la; PA, <[ a[i@li] <- e ]>)
  end.

Fixpoint eq_aexp (a1 a2 : aexp) : bool :=
  match a1, a2 with
  | ANum n1, ANum n2 => Nat.eqb n1 n2
  | AId x1, AId x2 => String.eqb x1 x2
  | APlus a11 a12, APlus a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | AMinus a11 a12, AMinus a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | AMult a11 a12, AMult a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | ACTIf b1 a11 a12, ACTIf b2 a21 a22 =>
      andb (eq_bexp b1 b2) (andb (eq_aexp a11 a21) (eq_aexp a12 a22))
  | _, _ => false
  end
with eq_bexp (b1 b2 : bexp) : bool :=
  match b1, b2 with
  | BTrue, BTrue => true
  | BFalse, BFalse => true
  | BEq a11 a12, BEq a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | BNeq a11 a12, BNeq a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | BLe a11 a12, BLe a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | BGt a11 a12, BGt a21 a22 => andb (eq_aexp a11 a21) (eq_aexp a12 a22)
  | BNot b1, BNot b2 => eq_bexp b1 b2
  | BAnd b11 b12, BAnd b21 b22 => andb (eq_bexp b11 b21) (eq_bexp b12 b22)
  | _, _ => false
  end.

Fixpoint eq_com (c1 c2 : com) : bool :=
  match c1, c2 with
  | Skip, Skip => true
  | Asgn x1 e1, Asgn x2 e2 => andb (String.eqb x1 x2) (eq_aexp e1 e2)
  | Seq c11 c12, Seq c21 c22 => andb (eq_com c11 c21) (eq_com c12 c22)
  | If be1 c11 c12, If be2 c21 c22 =>
      andb (eq_bexp be1 be2) (andb (eq_com c11 c21) (eq_com c12 c22))
  | While be1 c1, While be2 c2 => andb (eq_bexp be1 be2) (eq_com c1 c2)
  | ARead x1 a1 i1, ARead x2 a2 i2 =>
      andb (String.eqb x1 x2) (andb (String.eqb a1 a2) (eq_aexp i1 i2))
  | AWrite a1 i1 e1, AWrite a2 i2 e2 =>
      andb (String.eqb a1 a2) (andb (eq_aexp i1 i2) (eq_aexp e1 e2))
  | _, _ => false
  end.

QuickChick (forAll (sized gen_com) (fun c =>
    forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    let '(_,_,ac) := static_tracking_naive P PA public c in
    checker (eq_com (erase ac) c))))).

(* Extract Constant defNumTests => "10000000". *)

(* Noninterference for source sequential execution -- SHOULD FAIL! *)
QuickChick (forAllShrinkNonDet 100 (sized gen_com) shrink (fun c =>
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  let '(P',PA',_) := static_tracking_naive P PA public c in
    check_sequential_noninterference P PA P' PA' c)))).
(* This one finds counterexample, but sometimes needs millions of tests for that: *)

(* (while (X1 <= 1) do ((X1 := X0) ; (X0 <- A0[[0]])) end) *)
(* (false, [("X0", true); ("X1", true); ("X2", false); ("X3", false); ("X4", true); ("X5", true)]) *)
(* (true, [("A0", false); ("A1", true); ("A2", true)]) *)

(* (while (7 > X3) do ((X3 := (X1 * 3)) ; (X1 <- A0[[X0]])) end) *)
(* (false, [("X0", true); ("X1", true); ("X2", false); ("X3", true); ("X4", true); ("X5", true)]) *)
(* (false, [("A0", false); ("A1", true); ("A2", false)]) *)

(* TODO: Can we improve our testing so that it's better at finding this?
         We basically need loops where the read variables are also assigned?
         The loops should additionally also be (1) executed at least once; and
         (2) terminating, since otherwise we discard them.
         So a loop condition variable should be assigned in the loop.
         - Implemented: this alone took us from ~10 millions to around 1 million
         Could gather statistics of how many times are loops executed.
         - related to fuel? *)


(* To implement a sound flow-sensitive static IFC tracking we need a better
   story for while loops *)

Fixpoint assigned_vars (c:com) : list string :=
  match c with
  | <{ skip }> => []
  | <{ X := ae }> => [var_id_to_string X]
  | <{ c1; c2 }> => assigned_vars c1 ++ assigned_vars c2
  | <{ if be then c1 else c2 end }> => assigned_vars c1 ++ assigned_vars c2
  | <{ while be do c1 end }> => assigned_vars c1
  | <{ X <- a[[i]] }> => [var_id_to_string  X]
  | <{ a[i] <- e }> => []
  end.

Fixpoint assigned_arrs (c:com) : list string :=
  match c with
  | <{ skip }> => []
  | <{ X := ae }> => []
  | <{ c1; c2 }> => assigned_arrs c1 ++ assigned_arrs c2
  | <{ if be then c1 else c2 end }> => assigned_arrs c1 ++ assigned_arrs c2
  | <{ while be do c1 end }> => assigned_arrs c1
  | <{ X <- a[[i]] }> => []
  | <{ a[i] <- e }> => [arr_id_to_string a]
  end.

Definition list_eqb l1 l2 := if list_eq_dec string_dec l1 l2 then true else false.

Fixpoint static_tracking (P:pub_vars) (PA:pub_arrs) (pc:label) (c:com)
  : (pub_vars*pub_arrs*acom) :=
  match c with
  | <{ skip }> => (P, PA, <[skip]>)
  | <{ X := ae }> => (X !-> (join pc (label_of_aexp P ae)); P, PA, <[X := ae]>)
  | <{ c1; c2 }> => let '(P1, PA1, ac1) := static_tracking P PA pc c1 in
                    let '(P2, PA2, ac2) := static_tracking P1 PA1 pc c2 in
                     (P2, PA2, <[ ac1; ac2 ]>)
  | <{ if be then c1 else c2 end }> =>
      let lbe := label_of_bexp P be in
      let '(P1, PA1, ac1) := static_tracking P PA (join pc lbe) c1 in
      let '(P2, PA2, ac2) := static_tracking P PA (join pc lbe) c2 in
      (join_total_maps P1 P2, join_total_maps PA1 PA2,
        <[ if be@lbe then ac1 else ac2 end ]>)
  | <{ while be do c1 end }> =>
      let avars := remove_dupes String.eqb (assigned_vars c1) in
      let aarrs := remove_dupes String.eqb (assigned_arrs c1) in
      let pvars := filter (apply P) avars in
      let parrs := filter (apply PA) aarrs in
      let max_iters := List.length pvars + List.length parrs in
      let fix aux (i:nat) (P:pub_vars) (PA:pub_arrs) (pc:label)
          : (pub_vars*pub_arrs*label*acom) :=
         let lbe := label_of_bexp P be in
         let '(P1, PA1, ac1) := static_tracking P PA (join pc lbe) c1 in
         let P1 := join_total_maps P1 P in
         let PA1 := join_total_maps PA1 PA in
         let pvars' := filter (apply P1) avars in
         let parrs' := filter (apply PA1) aarrs in
         let stop := list_eqb pvars pvars' && list_eqb parrs parrs' in
         match i, stop with
         | _,true (* Stopping if a fixpoint was already reached *)
         | 0,_ => (P1, PA1, lbe, ac1)
         | S i',false => aux i' P1 PA1 lbe
         end in 
      let '(P', PA', lbe, ac1) := aux max_iters P PA pc in
      (P', PA', <[ while be@lbe do ac1 end ]>)
  | <{ X <- a[[i]] }> =>
      let li := label_of_aexp P i in
      let lx := join pc (join li (apply PA a)) in
      (X !-> lx; P, PA, <[ X@@lx <- a[[i@li]] ]>)
  | <{ a[i] <- e }> =>
      let li := label_of_aexp P i in
      let la := join (apply PA a) (join pc (join li (label_of_aexp P e))) in
      (* It seems likely that the arrays will all become private quite quickly *)
      (P, a !-> la; PA, <[ a[i@li] <- e ]>)
  end.

QuickChick (forAll (sized gen_com) (fun c =>
    forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    let '(P',PA',ac) := static_tracking P PA public c in
    let pvars := filter (apply P') (map_dom (snd P)) in
    let parrs := filter (apply PA') (map_dom (snd PA)) in
    collect (List.length pvars) (
    (* Looking at these ^ statistics it doesn't seem we're overtainting.
       - For arrays from 1.5 initially to 1 / 3 finally.
       - For vars from 3 initially to 2.6 / 6 finally.
       Could it be that some arrays / variables are never assigned?
       TODO: use assigned_arrs / vars below to gather better data *)
    checker (eq_com (erase ac) c)))))).

(* Noninterference for source sequential execution -- should work this time *)
QuickChick (forAll (sized gen_com) (fun c =>
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  let '(P',PA',_) := static_tracking P PA public c in
    check_sequential_noninterference P PA P' PA' c)))).

Fixpoint flex_slh_acom (ac:acom) : com :=
  (match ac with
  | <[skip]> => <{skip}>
  | <[x := e]> => <{x := e}>
  | <[c1; c2]> => <{ flex_slh_acom c1; flex_slh_acom c2}>
  | <[if be@lbe then c1 else c2 end]> =>
      if lbe
      then (* Selective SLH -- tracking speculation, but not masking *)
        <{if be then "b" := be ? "b" : 1; flex_slh_acom c1
                else "b" := be ? 1 : "b"; flex_slh_acom c2 end}>
      else (* Ultimate SLH -- tracking speculation and also masking *)
        <{if "b" = 0 && be then "b" := ("b" = 0 && be) ? "b" : 1; flex_slh_acom c1
                           else "b" := ("b" = 0 && be) ? 1 : "b"; flex_slh_acom c2 end}>
  | <[while be@lbe do c end]> =>
      if lbe
      then (* Selective SLH -- tracking speculation, but not masking *)
        <{while be do "b" := be ? "b" : 1; flex_slh_acom c end;
           "b" := be ? 1 : "b"}>
      else (* Ultimate SLH -- tracking speculation and also masking *)
        <{while "b" = 0 && be do "b" := ("b" = 0 && be) ? "b" : 1; flex_slh_acom c end;
           "b" := ("b" = 0 && be) ? 1 : "b"}>
  | <[x@@lx <- a[[i@li]]]> =>
    if li
    then (* Selective SLH -- mask the value of public loads *)
      if lx then <{x <- a[[i]]; x := ("b" = 1) ? 0 : x}>
            else <{x <- a[[i]]}>
    else (* Ultimate SLH -- mask private address of load *)
      <{x <- a[[("b" = 1) ? 0 : i]] }>
  | <[a[i@li] <- e]> =>
    if li
    then (* Selective SLH *)
      <{a[i] <- e}> (* <- Doing nothing here okay for Spectre v1,
         but problematic for return address or code pointer overwrites *)
        (* !!! For fixed-size arrays can also do `mod size` to keep things in bound *)
    else (* Ultimate SLH *)
      <{a[("b" = 1) ? 0 : i] <- e}>
  end)%string.

QuickChick (forAll (sized gen_com) (fun c =>
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  let '(P',PA',ac) := static_tracking P PA public c in
  check_speculative_noninterference P PA P' PA' c (flex_slh_acom ac))))).

QuickChick (forAll (sized gen_com) (fun c =>
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  let '(_,_,ac) := static_tracking P PA public c in
  check_relative_security P PA c (flex_slh_acom ac))))).

QuickChick (forAll (sized gen_com) (fun c =>
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  let '(_,_,ac) := static_tracking P PA public c in
  forAll gen_state (fun s1 =>
  forAll (gen_pub_equiv P s1) (fun s2 => (* <- extra assumption *)
  check_ideal_misspeculated_unwinding (flex_slh_acom ac) s1 s2)))))).
