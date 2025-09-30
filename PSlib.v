Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation.
From Coq Require Import String.
From SECF Require Import ListMaps.
Require Import Coq.Classes.EquivDec.

(** ** Type system for cryptographic constant-time programming *)

(* Imported straight from TestingStateIFC.v, so don't bother testing them. *)

(* TERSE: HIDEFROMHTML *)
Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.
Definition pub_arrs := total_map label.

Notation apply := ListMaps.apply.

Definition fold_extra {A : Type} {B : Type} (f : A -> list B -> B -> list B -> A) (l : list B) (v : A) : A :=
  let fix aux (processed : list B) (incoming : list B) (acc : A) :=
    match incoming with
    | [] => acc
    | h::t =>
        let new_acc := f acc processed h t in
        aux (processed ++ [h]) t new_acc
    end
  in aux [] l v.

#[export] Instance shrinkTotalMap {X : Type} `{Shrink X}: Shrink (total_map X) :=
  {shrink := fun '(d, m) =>
      (* Shrinking the default value *)
      (List.map (fun d' => (d', m)) (shrink d)) ++
      (* Shrinking an entry in the map *)
      (List.map
         (fun m' => (d, m'))
         (fold_extra (fun acc before '(k, v) after =>
            let modified_entry := List.map (fun v' =>
                before ++ [(k, v')] ++ after
              ) (shrink v) in

            modified_entry ++ acc
         ) m [])
      ) ++
      (* Removing an entry in the map *)
      (List.map
         (fun m' => (d, m'))
         (fold_extra (fun acc before '(k, v) after =>
            (before ++ after) :: acc
         ) m [])
      )
  }.

Definition pub_equiv (P : total_map label) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, apply P x = true -> apply s1 x = apply s2 x.

Definition pub_equivb (P : total_map label) {X:Type} `{EqDec X} (s1 s2 : total_map X) : bool :=
  match P, s1, s2 with
  | (dP,mP), (d1,m1), (d2,m2) =>
      if dP
      then forallb (fun x => if apply P x
                             then (apply s1 x) ==b (apply s2 x) else true)
                   (union (map_dom mP) (union (map_dom m1) (map_dom m2)))
           && (d1 ==b d2)
      else forallb (fun x => if apply P x
                             then (apply s1 x) ==b (apply s2 x) else true)
                   (map_dom mP)
  end.

Inductive Forall3 {A B C} (P : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons x y z l k k' :
    P x y z -> Forall3 P l k k' -> Forall3 P (x :: l) (y :: k) (z :: k').

Definition pub_equiv_list (P: list label) {X:Type} (m1 m2: list X) :=
  Forall3 (fun (a:label) (b:X) (c:X) => if a then b = c else True) P m1 m2.

Fixpoint forallb3 {A B C} (P : A -> B -> C -> bool) (a: list A) (b: list B) (c: list C) : bool :=
  match a, b, c with
  | [], [], [] => true
  | hdp::tlp, hd1::tl1, hd2::tl2 => (P hdp hd1 hd2) && (forallb3 P tlp tl1 tl2)
  | _, _, _ => false
  end.

Definition pub_equiv_listb (P: list label) {X:Type} `{EqDec X} (m1 m2: list X) :=
  forallb3 (fun (a:label) (b:X) (c:X) => if a then (b ==b c) else true) P m1 m2.

Definition gen_pub_equiv (P : total_map label) {X: Type} `{Gen X} (s: total_map X) : G (total_map X) :=
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map X)) (c : string * X) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if apply P k then ret v else arbitrary);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

Definition gen_pub_vars : G pub_vars :=
  default <- arbitrary;;
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret (
    "X0" !-> x0; "X1" !-> x1;
    "X2" !-> x2; "X3" !-> x3;
    "X4" !-> x4; "X5" !-> x5;
    _ !-> default
  ) % string.

Definition gen_state : G (total_map nat) :=
  d <- arbitrary;;
  v0 <- arbitrary;;
  v1 <- arbitrary;;
  v2 <- arbitrary;;
  v3 <- arbitrary;;
  v4 <- arbitrary;;
  v5 <- arbitrary;;
  ret (d, [("X0",v0); ("X1",v1); ("X2",v2);
           ("X3",v3); ("X4",v4); ("X5",v5)]) % string.

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

Inductive val : Type :=
  | N (n:nat)
  | FP (l:nat). (* <- NEW: function pointer to procedure at label [l] *)

Derive (Arbitrary, Shrink) for val.

#[export] Instance showVal : Show val :=
  {show :=fun v => 
      match v with
      | N n => show n
      | FP l => ("&" ++ show l)%string
      end
  }.

Definition val_eqb (v1 v2: val) : bool :=
  match v1, v2 with
  | N n1, N n2 => Nat.eqb n1 n2
  | FP l1, FP l2 => Nat.eqb l1 l2
  | _, _ => false
  end.

Notation "x =v y" := (val_eqb x y) (at level 50).

Lemma val_eqb_spec:
  forall v1 v2, val_eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros. split; intros.
  - destruct v1, v2; simpl in *; try discriminate.
    + rewrite Nat.eqb_eq in H. auto.
    + rewrite Nat.eqb_eq in H. auto.
  - subst. destruct v2; simpl; auto; eapply Nat.eqb_refl.
Qed.

Lemma val_eqb_spec':
  forall v1 v2, val_eqb v1 v2 = false <-> v1 <> v2.
Proof.
  intros. split; intros.
  - red. intros. rewrite <- val_eqb_spec in H0.
    rewrite H in H0. discriminate.
  - destruct v1, v2; simpl in *; auto.
    + rewrite Nat.eqb_neq. red. intros. subst.
      apply H. auto.
    + rewrite Nat.eqb_neq. red. intros. subst.
      apply H. auto.
Qed.

Instance EqDec_val : EqDec val eq.
Proof.
  red. intros.
  destruct (val_eqb x y) eqn:Heqb.
  - rewrite val_eqb_spec in Heqb. subst.
    left. reflexivity.
  - rewrite val_eqb_spec' in Heqb.
    right. red. intros.
    inversion H. subst. eapply Heqb; auto.
Defined.

Definition gen_pub_mem : G (list label) :=
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret ( [x0; x1; x2; x3; x4; x5]
  ) % string.

Definition gen_mem : G (list val) :=
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret ( [x0; x1; x2; x3; x4; x5]
  ) % string.

Fixpoint _gen_pub_mem_equiv (P : list label) {X: Type} `{Gen X} (m: list X) : G (list X) :=
  match P, m with
  | [], [] => ret []
  | hdp::tlp, hdm::tlm =>
      hd <- (if hdp then ret hdm else arbitrary);;
      tl <-_gen_pub_mem_equiv tlp tlm;;
      ret (hd::tl)
  | _, _ => ret [] (* unreachable *)
  end.

Fixpoint gen_pub_mem_equiv (P : list label) {X: Type} `{Gen X} (m: list X) : G (list X) :=
  if (Datatypes.length P =? Datatypes.length m)
  then _gen_pub_mem_equiv P m
  else ret [].

QuickChick (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

Definition shrink_pub_equiv_reg (P : total_map label) (s : total_map val) : total_map val -> list (total_map val) :=
  fun '(d, m) =>
    (* We can only shrink the default value iif nothing secret uses it.
       If the default for P is "secret", then we can always find a variable not in m that is secret.
       Otherwise, we can shrink if all public values in P are explicit in s *)
    let can_shrink_default := (
      let '(default_visiblity, visiblities) := P in

      if default_visiblity
      then false
      else
        let public_variables := List.filter (fun x =>
          apply P x
        ) (map_dom visiblities) in

        forallb (fun v => List.existsb (fun '(v', _) => String.eqb v v') m) public_variables
    ) in

    let secret_entries_shrunk := (List.map
         (fun m' => (d, m'))
         (fold_extra (fun acc before '(k, v) after =>
            let modified_entry := if apply P k
              then []
              else List.map (fun v' =>
                  before ++ [(k, v')] ++ after
                ) (shrink v) in

            modified_entry ++ acc
         ) m [])
      ) in

    (* We can only remove secret entries or public entries that have
       the same value as the default value *)
    let entries_removed := List.map
        (fun m' => (d, m'))
        (fold_extra (fun acc before '(k, v) after =>
           let replacement :=
             if negb (apply P k) || (v =v d)
             then before ++ after (* secret or same value as default *)
             else before ++ (k, v) :: after in

           replacement :: acc
        ) m []) in

    if can_shrink_default
    then (List.map (fun d' => (d', m)) (shrink d)) ++ (secret_entries_shrunk ++ entries_removed)
    else secret_entries_shrunk ++ entries_removed.

Fixpoint remove_one_secret (P: list label) {X: Type} (s: list X) : list (list X) :=
    match P, s with
    | [], [] => []
    | hp::tp, hr::tr =>
        let removed_one_items := (remove_one_secret tp tr) in
        let add_hd := List.map (fun tl => hr :: tl) removed_one_items in
        if hp
        then add_hd
        else tr :: removed_one_items
    | _, _ => [] (* unreachable *)
    end.

Definition shrink_pub_equiv_mem (P: list label) (s: list val)
  : list val -> list (list val) :=
  fun s' =>
    if negb (Datatypes.length P =? Datatypes.length s')%nat then []
    else
      (
        let secret_values_shrunk :=
          (fix secret_values_shrunk_aux (P: list label) (rs: list val) :=
             match P, rs with
             | [], [] => []
             | hp::tp, hr::tr =>
                 if hp
                 then (let shrunk_tl := secret_values_shrunk_aux tp tr in
                       List.map (fun tl => hr :: tl) shrunk_tl)
                 else (let shrunk_hd := shrink hr in
                       List.map (fun hd => hd :: tr) shrunk_hd)
             | _, _ => [] (* unreachable *)
             end) P s' in
        let secret_items_shrunk :=
          remove_one_secret P s' in
        secret_values_shrunk ++ secret_items_shrunk

      ).
