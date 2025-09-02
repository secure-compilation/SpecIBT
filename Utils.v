From Coq Require Import List. Import ListNotations.

(* Tail recursive append to prevent stack overflows when testing *)
Fixpoint rev_append {A:Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1 => rev_append l1 (x :: l2)
  end.
Definition rev {A : Type} (l : list A) := rev_append l [].
Definition app {A:Type} (l1:list A) := rev_append (rev l1).
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Fixpoint upd {A:Type} (i:nat) (ns:list A) (n:A) : list A :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', n' :: ns' => n' :: upd i' ns' n
  | _, _ => ns
  end.

Lemma upd_length : forall {A:Type} (l:list A) i a,
  length (upd i l a) = length l.
Proof.
  induction l; destruct i; auto.
  intros. simpl. now f_equal.
Qed.

Definition add_index {a:Type} (xs:list a) : list (nat * a) :=
  combine (seq 0 (length xs)) xs.
