From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
From SECF Require Import Maps.
From SECF Require Import ListMaps.

Import ListNotations.
Set Default Goal Selector "!".

(* Map functor from CompCert *)

Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Parameter t: Type -> Type.
  Parameter init: forall (A: Type), A -> t A.
  Parameter get: forall (A: Type), elt -> t A -> A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.

  (* Axiom gi: *)
  (*   forall (A: Type) (i: elt) (x: A), get A i (init A x) = x. *)
  (* Axiom gss: *)
  (*   forall (A: Type) (i: elt) (x: A) (m: t A), get A i (set A i x m) = x. *)
  (* Axiom gso: *)
  (*   forall (A: Type) (i j: elt) (x: A) (m: t A), *)
  (*   i <> j -> get A i (set A j x m) = get A i m. *)
  (* Axiom gsspec: *)
  (*   forall (A: Type) (i j: elt) (x: A) (m: t A), *)
  (*   get A i (set A j x m) = if elt_eq i j then x else get A i m. *)
  (* Axiom gsident: *)
  (*   forall (A: Type) (i j: elt) (m: t A), get A j (set A i (get A i m) m) = get A j m. *)

  Parameter map: forall (A B: Type), (A -> B) -> t A -> t B.

  (* Axiom gmap: *)
  (*   forall (A B: Type) (f: A -> B) (i: elt) (m: t A), *)
  (*   get B i (map A B f m) = f(get A i m). *)
End MAP.

(* Total Map From SF *)
Module TotalMap <: MAP.
  Definition elt:= string.
  Definition elt_eq : forall (a b: elt), {a = b} + {a <> b}.
  Proof. eapply string_dec. Defined.

  Definition t := Maps.total_map.
  Definition init := @Maps.t_empty.
  Definition get {A: Type} (i: elt) (m: t A) : A := m i.
  Definition set {A: Type} (i: elt) (v: A) (m: t A) := Maps.t_update m i v.

  Definition map {A B: Type} (f: A -> B) (m: t A) : t B :=
    fun x => f (m x).

End TotalMap.

Module ListTotalMap <: MAP.
  Definition elt:= string.
  Definition elt_eq : forall (a b: elt), {a = b} + {a <> b}.
  Proof. eapply string_dec. Defined.

  Definition t := ListMaps.total_map.
  Definition init := @ListMaps.t_empty.
  Definition get {A: Type} (i: elt) (m: t A) : A := ListMaps.apply m i.
  Definition set {A: Type} (i: elt) (v: A) (m: t A) := ListMaps.t_update m i v.

  Definition map {A B: Type} (f: A -> B) (m: t A) : t B := @lm_map A B f m.

End ListTotalMap.

