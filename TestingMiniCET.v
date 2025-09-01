(** * Testing MiniCET *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation.
From Coq Require Import String.

From SECF Require Import ListMaps.

Inductive binop : Type :=
  | BinPlus
  | BinMinus
  | BinMult
  | BinEq
  | BinLe
  | BinAnd
  | BinImpl.

Definition not_zero (n : nat) : bool := negb (n =? 0).
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition eval_binop_nat (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => if n1 =? n2 then 1 else 0
  | BinLe => if n1 <=? n2 then 1 else 0
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp)
  | ACTIf (b : exp) (e1 e2 : exp)
  | AAddr (l : nat). (* <- NEW: function pointer for procedure at label [l] *)

(** We encode all the previous arithmetic and boolean operations: *)

Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr e1 e2 := BImpl (BNot e1) e2.
Definition BEq := ABin BinEq.
Definition BNeq e1 e2 := BNot (BEq e1 e2).
Definition BLe := ABin BinLe.
Definition BGt e1 e2 := BNot (BLe e1 e2).
Definition BLt e1 e2 := BGt e2 e1.

Hint Unfold eval_binop_nat : core.
Hint Unfold APlus AMinus AMult : core.
Hint Unfold BTrue BFalse : core.
Hint Unfold BAnd BImpl BNot BOr BEq BNeq BLe BGt BLt : core.

(** The notations we use for expressions are the same as in Imp,
    except the notation for [be?e1:e2] which is new: *)
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.

(* HIDE: BCP: Again, these notations are in flux in PLF... *)
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "'&' l"   := (AAddr l) (in custom com at level 75, right associativity).

Open Scope com_scope.

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2)
                 (in custom com at level 20, no associativity).

Definition reg := total_map nat.
Definition mem := total_map (list nat).

Inductive val : Type :=
  | N (n:nat)
  | FP (l:nat).

Definition eval_binop (o:binop) (v1 v2 : val) : option val :=
  match v1, v2 with
  | N n1, N n2 => Some (N (eval_binop_nat o n1 n2))
  | FP l1, FP l2 =>
      match o with
      | BinEq => Some (N (if l1 =? l2 then 1 else 0))
      | _ => None
      end
  | _, _ => None
  end.

Fixpoint eval (st : reg) (e: exp) : option val :=
  match e with
  | ANum n => ret (N n)
  | AId x => ret (N (apply st x))
  | ABin b e1 e2 =>
      v1 <- eval st e1;;
      v2 <- eval st e2;;
      eval_binop b v1 v2
  | <{b ? e1 : e2}> =>
      v1 <- eval st b;;
      match v1 with
      | N n1 => if not_zero n1 then eval st e1 else eval st e2
      | _ => None
      end
  | <{&l}> => ret (FP l)
  end.
