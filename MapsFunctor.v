From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From SECF Require Import Maps.
From SECF Require Import ListMaps.

Import ListNotations.
Set Default Goal Selector "!".

Module Type TMap.
  Parameter t: Type -> Type.
  Parameter init: forall {A: Type}, A -> t A.
  Parameter t_apply: forall {A: Type}, t A -> string -> A.
  Parameter t_update: forall {A: Type}, t A -> string -> A -> t A.

  Axiom t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.

  Axiom t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.

End TMap.

(* Total Map From SF *)
Module TotalMap <: TMap.
  Definition t := Maps.total_map.
  Definition init := @Maps.t_empty.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := Maps.t_update m i v.

  Lemma t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.
  Proof. eapply Maps.t_update_eq. Qed.

  Lemma t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. eapply Maps.t_update_neq. Qed.

End TotalMap.

(* ListMaps *)
Module ListTotalMap <: TMap.
  Definition t := ListMaps.total_map.
  Definition init := @ListMaps.t_empty.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := ListMaps.apply m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := ListMaps.t_update m i v.

  Lemma t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.
  Proof. intros. rewrite ListMaps.t_update_eq. auto. Qed.

  Lemma t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. intros. rewrite ListMaps.t_update_neq; auto. Qed.

End ListTotalMap.

