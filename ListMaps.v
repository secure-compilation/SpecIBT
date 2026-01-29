From Stdlib Require Import Strings.String.
From Stdlib Require Import List. Import ListNotations.
From QuickChick Require Import QuickChick Tactics.

Definition Map A := list (string * A).

Fixpoint map_get {A} (m : Map A) x : option A :=
  match m with
  | [] => None
  | (k, v) :: m' => if x = k ? then Some v else map_get m' x
  end.
Definition map_set {A} (m:Map A) (x:string) (v:A) : Map A := (x, v) :: m.

Fixpoint map_dom {A} (m:Map A) : list string :=
  match m with
  | [] => []
  | (k', v) :: m' => if existsb (fun p => String.eqb k' (fst p)) m'
                     then map_dom m'
                     else k' :: map_dom m'
  end.

Fixpoint union (dom1 dom2 : list string) : list string :=
  match dom1 with
  | [] => dom2
  | x :: dom1' => if existsb (String.eqb x) dom2
                  then union dom1' dom2
                  else x :: (union dom1' dom2)
  end.

Definition total_map (X:Type) : Type := X * Map X.

Definition t_empty {A : Type} (d : A) : total_map A :=
  (d, []).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  match m with
  | (d, lm) => (d, map_set lm x v)
  end.

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(* We can no longer just use function application for map lookups,
   instead we define a combinator for this: *)
Definition apply {A:Type} (m : total_map A) (x:string) : A := 
  match m with
  | (d, lm) => match map_get lm x with
               | Some v => v
               | None => d
               end
  end.

Definition lm_map {A B: Type} (f: A -> B) (m: total_map A) : total_map B :=
  let '(d, sl) := m in
  let '(kl, vl) := split sl in
  (f d, combine kl (List.map f vl)).

From SECF Require Import sflib.

Lemma t_update_eq : forall {A : Type} (m : total_map A) x v,
  apply (t_update m x v) x = v.
Proof. i. ginduction m. ii. unfold apply. ss. des_ifs. Qed.

Lemma t_update_neq : forall {A : Type} (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  apply (t_update m x1 v) x2 = apply m x2.
Proof. i. ginduction m. ii. unfold apply. ss. des_ifs. Qed.
