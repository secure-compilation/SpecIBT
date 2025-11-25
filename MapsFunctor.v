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
End TMap.

(* Total Map From SF *)
Module TotalMap <: TMap.
  Definition t := Maps.total_map.
  Definition init := @Maps.t_empty.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := Maps.t_update m i v.
End TotalMap.

(* ListMaps *)
Module ListTotalMap <: TMap.
  Definition t := ListMaps.total_map.
  Definition init := @ListMaps.t_empty.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := ListMaps.apply m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := ListMaps.t_update m i v.
End ListTotalMap.

