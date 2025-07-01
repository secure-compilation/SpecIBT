(** * SpecCT: Speculative Constant-Time *)

(* TERSE: HIDEFROMHTML *)
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
(* TERSE: /HIDEFROMHTML *)

(** * Cryptographic constant-time *)

(** Cryptographic constant-time (CCT) is a software countermeasure
    against cache-based timing attacks, a class of side-channel
    attacks that exploit the latency between cache hits and cache
    misses to retrieve cryptographic keys and other secrets. In
    addition to ensuring program counter security, CCT requires
    programmers to not perform memory accesses depending on secrets.

    To model this we first extend the Imp language with arrays. We
    need such an extension, since otherwise variable accesses in the
    original Imp map to memory operations at constant locations, which
    thus cannot depend on secrets, so CCT trivially holds for all
    programs in Imp. Array indices on the other hand are computed at
    runtime, which leads to accessing memory addresses that can depend
    on secrets, making CCT non-trivial for Imp with arrays. *)

(** ** Constant-time conditional *)

(** But first, we extend the arithmetic expressions of Imp with an [b ? e1 : e2]
    conditional that executes in constant time (for instance using a special
    constant-time conditional move instruction). This constant-time conditional
    makes arithmetic and boolean expressions mutually inductive. *)

Inductive var_id : Type := Var (name : string) : var_id.
Inductive arr_id : Type := Arr (name : string) : arr_id.

Coercion Var : string >-> var_id.
Coercion Arr : string >-> arr_id.
Definition var_id_to_string (v : var_id) : string :=
  let '(Var name) := v in name.
Definition arr_id_to_string (v : arr_id) : string :=
  let '(Arr name) := v in name.
Coercion var_id_to_string : var_id >-> string.
Coercion arr_id_to_string : arr_id >-> string.

#[export] Instance showVarId : Show var_id :=
  {show := fun '(Var name) => name}.
#[export] Instance showArrId : Show arr_id :=
  {show := fun '(Arr name) => name}.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : var_id)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ACTIf (b:bexp) (a1 a2:aexp) (* <--- NEW *)
with bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Scheme aexp_bexp_ind := Induction for aexp Sort Prop
with bexp_aexp_ind := Induction for bexp Sort Prop.
Combined Scheme aexp_bexp_mutind from aexp_bexp_ind,bexp_aexp_ind.

(** ** Typing Constant-time conditional *)

(** Typing of arithmetic and boolean expressions also becomes mutually inductive. *)

(** [[[
        P|-b- be \IN l   P |-a- a1 \IN l1    P |-a- a2 \IN l2
        ----------------------------------------------------- (T_CTIf)
                 P |-a- be?a1:a2 \IN join l (join l1 l2)
]]]
*)

(* TERSE: HIDEFROMHTML *)
Open Scope string_scope.
(* Variable names *)
Definition W : var_id := "W".
Definition X : var_id := "X".
Definition Y : var_id := "Y".
Definition Z : var_id := "Z".

(* Array names *)
Definition A : arr_id := "A".
Definition B : arr_id := "B".
Definition C : arr_id := "C".
Close Scope string_scope.

Coercion AId : var_id >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

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
Notation "be '?' a1 ':' a2"  := (ACTIf be a1 a2)
                 (in custom com at level 20, no associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.
(* TERSE: /HIDEFROMHTML *)

(* Deriving Show for both aexp and bexp. *)
Fixpoint show_aexp (a:aexp) : string :=
  let fix show_aexp (a : aexp) := match a with
  | AId i => show i
  | ANum n => show n
  | <{x + y}> => "(" ++ show_aexp x ++ " + " ++ show_aexp y ++ ")"
  | <{x - y}> => "(" ++ show_aexp x ++ " - " ++ show_aexp y ++ ")"
  | <{x * y}> => "(" ++ show_aexp x ++ " * " ++ show_aexp y ++ ")"
  | <{ b ? t : f }> => "(" ++ show_bexp b ++ " ? " ++ show_aexp t ++ " : " ++ show_aexp f ++ ")"
  end % string in show_aexp a
with show_bexp (a:bexp) : string :=
  match a with
  | <{true}> => "true" % string
  | <{false}> => "false" % string
  | <{x <= y}> => "(" ++ show_aexp x ++ " <= " ++ show_aexp y ++ ")"
  | <{x > y}> => "(" ++ show_aexp x ++ " > " ++ show_aexp y ++ ")"
  | <{x = y}> => "(" ++ show_aexp x ++ " = " ++ show_aexp y ++ ")"
  | <{x <> y}> => "(" ++ show_aexp x ++ " <> " ++ show_aexp y ++ ")"
  | <{~x}> => "(~ " ++ show_bexp x ++ ")"
  | <{x && y}> => "(" ++ show_bexp x ++ " && " ++ show_bexp y ++ ")"
  end.

(* I don't think doing mutual definitions of Instances is possible :'( *)

#[export] Instance showAexp : Show aexp :=
  {show := show_aexp }.
#[export] Instance showBexp : Show bexp :=
  {show := show_bexp }.

#[export] Instance genVarId : Gen var_id :=
  {arbitrary := (
    n <- freq [(10, ret 0);
               (9, ret 1);
               (8, ret 2);
               (4, ret 3);
               (2, ret 4);
               (1, ret 5)];;
    ret (Var ("X" ++ show n)) % string
  )}.
#[export] Instance genArrId : Gen arr_id :=
  {arbitrary := (
    n <- freq [(5, ret 0);
             (3, ret 1);
             (1, ret 2)];;
    ret (Arr ("A" ++ show n)) % string
  )}.

Definition shrink_name (name : string) : list string :=
  let prefix := substring 0 1 name in
  match get 1 name with
  | Some a =>
      let as_nat := nat_of_ascii a - nat_of_ascii "0" in
      match as_nat with
      | S n => [prefix ++ show (S n / 2); prefix ++ show (S n - 1)]
      | 0 => []
      end
  | None => []
  end % string.

#[export] Instance shrinkVarId : Shrink var_id :=
  {shrink := fun '(Var name) => List.map (fun name => Var name) (shrink_name name)}.
#[export] Instance shrinkArrId : Shrink arr_id :=
  {shrink := fun '(Arr name) => List.map (fun name => Arr name) (shrink_name name)}.

(* QuickChick does not support mutual inductive types. *)
(* Derive Arbitrary for aexp and bexp. *)
Fixpoint arbitrarySized_impl_bexp (size : nat) : G bexp :=
  match size with
  | 0 => oneOf [
        returnGen <{ true }>;
        returnGen <{ false }>
      ]
  | S size' =>
      freq [
        (1,returnGen <{ true }>);
        (1,returnGen <{ false }>);
        (4,thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 = a2 }>
        ));
        (4,thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 <> a2 }>
        ));
        (4,thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 <= a2 }>
        ));
        (4,thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 > a2 }>
        ));
        (4,thunkGen (fun _ =>
          b <- arbitrarySized_impl_bexp size';;
          returnGen <{ ~b }>
        ));
        (4,thunkGen (fun _ =>
          b1 <- arbitrarySized_impl_bexp size';;
          b2 <- arbitrarySized_impl_bexp size';;
          returnGen <{ b1 && b2 }>
        ))
      ]
  end
with arbitrarySized_impl_aexp (size : nat) : G aexp :=
  match size with
  | 0 =>
      oneOf [
        (n <- arbitrary;;
         returnGen (ANum n));
        (v <- arbitrary;;
         returnGen (AId v))
      ]
  | S size' =>
      oneOf [
        (n <- arbitrary;;
         returnGen (ANum n));
        (v <- arbitrary;;
         returnGen (AId v));
        thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 + a2 }>
        );
        thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 - a2 }>
        );
        thunkGen (fun _ =>
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ a1 * a2 }>
        );
        thunkGen (fun _ =>
          be <- arbitrarySized_impl_bexp size';;
          a1 <- arbitrarySized_impl_aexp size';;
          a2 <- arbitrarySized_impl_aexp size';;
          returnGen <{ be ? a1 : a2 }>
        )
      ]
  end.

#[export] Instance genSizedAexp : GenSized aexp :=
  {| arbitrarySized := arbitrarySized_impl_aexp |}.
#[export] Instance genSizedBexp : GenSized bexp :=
  {| arbitrarySized := arbitrarySized_impl_bexp |}.

(* Derive Shrink for aexp and bexp. *)
Fixpoint shrink_impl_bexp (b : bexp) : list bexp :=
  match b with
  | <{ a1 = a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk = a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 = shrunk }>) (shrink_impl_aexp a2))
  | <{ a1 <> a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk <> a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 <> shrunk }>) (shrink_impl_aexp a2))
  | <{ a1 <= a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk <= a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 <= shrunk }>) (shrink_impl_aexp a2))
  | <{ a1 > a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk > a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 > shrunk }>) (shrink_impl_aexp a2))
  | <{ ~ b1 }> =>
      [b1] ++
      (map (fun shrunk : bexp => <{ ~ shrunk }>) (shrink_impl_bexp b1))
  | <{ b1 && b2 }> =>
      [b1; b2] ++
      (map (fun shrunk : bexp => <{ shrunk && b2 }>) (shrink_impl_bexp b1)) ++
      (map (fun shrunk : bexp => <{ b1 && shrunk }>) (shrink_impl_bexp b2))
  | _ => []
  end
with shrink_impl_aexp (a : aexp) : list aexp :=
  match a with
  | ANum n => map (fun n => ANum n) (shrink n)
  | AId v => map (fun v => AId v) (shrink v)
  | <{ a1 + a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk + a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 + shrunk }>) (shrink_impl_aexp a2))
  | <{ a1 - a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk - a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 - shrunk }>) (shrink_impl_aexp a2))
  | <{ a1 * a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk * a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ a1 * shrunk }>) (shrink_impl_aexp a2))
  | <{ be ? a1 : a2 }> =>
      (map (fun shrunk : bexp => <{ shrunk ? a1 : a2 }>) (shrink_impl_bexp be)) ++
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ be ? shrunk : a2 }>) (shrink_impl_aexp a1)) ++
      (map (fun shrunk : aexp => <{ be ? a1 : shrunk }>) (shrink_impl_aexp a2))
  end.

#[export] Instance shrinkAexp : Shrink aexp :=
  {| shrink := shrink_impl_aexp |}.
#[export] Instance shrinkBexp : Shrink bexp :=
  {| shrink := shrink_impl_bexp |}.

(** ** Now back to adding arrays *)

Inductive com : Type :=
  | Skip
  | Asgn (x : var_id) (e : aexp)
  | Seq (c1 c2 : com)
  | If (be : bexp) (c1 c2 : com)
  | While (be : bexp) (c : com)
  | ARead (x : var_id) (a : arr_id) (i : aexp) (* <--- NEW *)
  | AWrite (a : arr_id) (i : aexp) (e : aexp)  (* <--- NEW *).

(* HIDE: CH: Wanted to take a:aexp and compute the accessed array, but
   our maps only have string keys, so had to settle with a:string for
   now. Seems this still fine though. *)

(* HIDE: CH: One alternative (also pointed out by Sven Argo) is that if
   we generalize/duplicate our map library beyond strings we can just
   make memory a single big array of numbers indexed by dynamically
   computed numbers. This would be a lower-level variant of Imp and
   one advantage over the variant with arrays is that our state would
   be a single map, not two. One advantage of the array variant is
   that we can use our existing variables as registers that can be
   accessed without triggering observable events, so our
   noninterference for expressions doesn't change, which is good.  *)

(* HIDE: CH: Maybe a good way to get the best of both worlds would
   be to use a type system to combine the two states into one, yet to
   keep accessing the arrays only with the special ARead and AWrite
   operations above. This would make this part of the chapter depend
   on types, while currently we managed to avoid that dependency, at
   the cost of duplicating the state. If avoiding the dependency is
   important we could dynamically prevent nat vs array type confusion
   for now and only return later to prevent it using static typing? *)

(* TERSE: HIDEFROMHTML *)

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

Notation "'skip'"  :=
  Skip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (Asgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (Seq x y)
    (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (in custom com at level 89, x custom com at level 99,
     y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (While x y)
    (in custom com at level 89, x custom com at level 99, y at level 99) : com_scope.

(* HIDE *)
Check <{{ skip }}>.
Check <{{ (skip ; skip) ; skip }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Definition func (c : com) : com := <{{ c ; skip }}>.
Check <{{ skip; func <{{ skip }}> }}>.
Definition func2 (c1 c2 : com) : com := <{{ c1 ; c2 }}>.
Check <{{ skip ; func2 <{{skip}}> <{{skip}}> }}>.
Check <{ true && ~(false && true) }>.
Check <{{ if true then skip else skip end }}>.
Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>.
Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>.
(* /HIDE *)

Notation "x '<-' a '[[' i ']]'"  :=
  (ARead x a i)
     (in custom com at level 0, x constr at level 0,
      a at level 85, i custom com at level 85, no associativity) : com_scope.
Notation "a '[' i ']'  '<-' e"  :=
  (AWrite a i e)
     (in custom com at level 0, a constr at level 0,
      i custom com at level 0, e custom com at level 85,
         no associativity) : com_scope.

#[export] Instance showCom : Show com :=
  {show :=
      (let fix showComRec (a:com) : string :=
         match a with
         | <{skip}> => "skip"
         | <{x := y}> => "(" ++ show x ++ " := " ++ show y ++ ")"
         | <{x ; y}> => "(" ++ showComRec x ++ " ; " ++ showComRec y ++ ")"
         | <{if x then y else z end}> => "(if " ++ show x ++
                                        " then " ++ showComRec y ++
                                        " else " ++ showComRec z ++ " end)"
         | <{while x do y end}> => "(while " ++ show x ++ " do "
                                            ++ showComRec y ++ " end)"
         | <{ x <- a[[ i ]] }> => "(" ++ show x ++ " <- " ++ show a ++ "[[" ++ show i ++ "]])"
         | <{ a[ i ] <- e }> => "(" ++ show a ++ "[" ++ show i ++ "] <- " ++ show e ++ ")"
         end
       in showComRec)%string
  }.

(* TODO: thunk these too if they aren't by default. *)
Derive Arbitrary for com.

(* As was the case in TestingStaticIFC, let's which to maps that are lists of pairs *)
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

(* Like List.fold_left, but also gives the list before and after *)
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

(* Now that we have these maps, use them to define how programs execute *)
Definition state := total_map nat.
Definition astate := total_map (list nat).

Definition gen_state : G state :=
  d <- arbitrary;;
  v0 <- arbitrary;;
  v1 <- arbitrary;;
  v2 <- arbitrary;;
  v3 <- arbitrary;;
  v4 <- arbitrary;;
  v5 <- arbitrary;;
  ret (d, [("X0",v0); ("X1",v1); ("X2",v2);
           ("X3",v3); ("X4",v4); ("X5",v5)]) % string.

Definition gen_astate : G astate :=
  d <- arbitrary;;
  v0 <- arbitrary;;
  v1 <- arbitrary;;
  v2 <- arbitrary;;
  ret (d, [("A0",v0); ("A1",v1); ("A2",v2)]) % string.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => apply st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  | <{b ? a1 : a2}> => if beval st b then aeval st a1
          (* ^- NEW -> *)            else aeval st a2
  end
with beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Fixpoint upd (i:nat) (ns:list nat) (n:nat) : list nat :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', _ :: ns' => upd i' ns' n
  | _, _ => ns
  end.
(* TERSE: /HIDEFROMHTML *)

(** ** Observations *)

Inductive observation : Type :=
  | OBranch (b : bool)
  | OARead (a : string) (i : nat)
  | OAWrite (a : string) (i : nat).

Definition obs := list observation.

Definition observation_eqb (os1 : observation) (os2 : observation) : bool :=
  match os1, os2 with
  | OBranch b, OBranch b' => Bool.eqb b b'
  | OARead a i, OARead a' i' => (String.eqb a a') && (i =? i')
  | OAWrite a i, OAWrite a' i' => (String.eqb a a') && (i =? i')
  | _, _ => false
  end.
Definition obs_eqb (o1 : obs) (o2 : obs) : bool :=
  forallb (fun '(os1, os2) => observation_eqb os1 os2) (List.combine o1 o2).

(** We define an instrumented big-step operational semantics based on these
   observations. *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation
         "'<(' st , ast ')>' '=[' c ']=>' '<(' stt , astt , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive cteval : com -> state -> astate -> state -> astate -> obs -> Prop :=
  | CTE_Skip : forall st ast,
      <(st , ast)> =[ skip ]=> <(st, ast, [])>
  | CTE_Asgn  : forall st ast e n x,
      aeval st e = n ->
      <(st, ast)> =[ x := e ]=> <(x !-> n; st, ast, [])>
  | CTE_Seq : forall c1 c2 st ast st' ast' st'' ast'' os1 os2,
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)>  ->
      <(st', ast')> =[ c2 ]=> <(st'', ast'', os2)> ->
      <(st, ast)>  =[ c1 ; c2 ]=> <(st'', ast'', os1++os2)>
  | CTE_IfTrue : forall st ast st' ast' b c1 c2 os1,
      beval st b = true ->
      <(st, ast)> =[ c1 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', OBranch true::os1)>
  | CTE_IfFalse : forall st ast st' ast' b c1 c2 os1,
      beval st b = false ->
      <(st, ast)> =[ c2 ]=> <(st', ast', os1)> ->
      <(st, ast)> =[ if b then c1 else c2 end]=> <(st', ast', OBranch false::os1)>
  | CTE_While : forall b st ast st' ast' os c,
      <(st,ast)> =[ if b then c; while b do c end else skip end ]=>
        <(st', ast', os)> -> (* <^- Nice trick; from small-step semantics *)
      <(st,ast)> =[ while b do c end ]=> <(st', ast', os)>
  | CTE_ARead : forall st ast x a ie i,
      aeval st ie = i ->
      i < Datatypes.length (apply ast a) % nat ->
      <(st, ast)> =[ x <- a[[ie]] ]=> <(x !-> nth i (apply ast a) 0; st, ast, [OARead a i])>
  | CTE_Write : forall st ast a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < Datatypes.length (apply ast a) ->
      <(st, ast)> =[ a[ie] <- e ]=> <(st, a !-> upd i (apply ast a) n; ast, [OAWrite a i])>

  where "<( st , ast )> =[ c ]=> <( stt , astt , os )>" := (cteval c st ast stt astt os).
(* TERSE: /HIDEFROMHTML *)

Module CTInterpreter.

(* Interpreter for constant time *)
Definition input_st : Type := state * astate.
Inductive output_st (A : Type): Type :=
  | ROutOfFuel : output_st A
  | ROutOfBounds : output_st A
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
        | ROk _ value os1 ist'  => match evaluate B (f value) ist' with
            | ROk _ value os2 ist'' => ROk B value (os1 ++ os2) ist''
            | ret => ret
            end
        | ROutOfBounds _ => ROutOfBounds B
        | ROutOfFuel _ => ROutOfFuel B
        end
      )
   }.

(* specialized operators *)
Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _) := ist in
    evaluate _ (ret (apply st name)) ist
  ).
Definition get_arr (name : string): evaluator (list nat) :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, ast) := ist in
    evaluate _ (ret (apply ast name)) ist
  ).
Definition set_var (name : string) (value : nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast) := ist in
    let new_st := (name !-> value ; st) in
    evaluate _ finish (new_st, ast)
  ).
Definition set_arr (name : string) (value : list nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast) := ist in
    let new_ast := (name !-> value ; ast) in
    evaluate _ finish (st, new_ast)
  ).
Definition eval_aexp (a : aexp) : evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _) := ist in
    let v := aeval st a in
    evaluate _ (ret v) ist
  ).
Definition eval_bexp (b : bexp) : evaluator bool :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _) := ist in
    let v := beval st b in
    evaluate _ (ret v) ist
  ).
Definition raise_out_of_bounds : interpreter :=
  mkEvaluator _ (fun _ =>
    ROutOfBounds _
  ).
Definition raise_out_of_fuel : interpreter :=
  mkEvaluator _ (fun _ =>
    ROutOfFuel _
  ).
Definition observe (o : observation) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROk _ tt [o] ist
  ).

Fixpoint cteval_engine_aux (f : nat) (c : com) : interpreter :=
  match f with
  | O => raise_out_of_fuel
  | S f =>

  match c with
  | <{ skip }> =>
      finish
  | <{ x := e }> =>
      v <- eval_aexp e;;
      set_var x v
  | <{ c1 ; c2 }> =>
      cteval_engine_aux f c1;;
      cteval_engine_aux f c2
  | <{ if b then ct else cf end }> =>
      condition <- eval_bexp b;;
      let next_c := if Bool.eqb condition true then ct else cf in

      observe (OBranch condition);;
      cteval_engine_aux f next_c
  | <{ while be do c end }> =>
    cteval_engine_aux f <{
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
        set_var x (nth i l 0)
      else
        (* If we're not speculating, then it's just a program error *)
        raise_out_of_bounds
  | <{ a[ie] <- e }> =>
      n <- eval_aexp e;;
      i <- eval_aexp ie;;
      l <- get_arr a;;

      if (i <? List.length l) then
        observe (OAWrite a i);;
        set_arr a (upd i l n)
      else
        (* If we're not speculating, then it's just a program error *)
        raise_out_of_bounds
  end
  end.
End CTInterpreter.

Definition cteval_engine (f : nat) (c : com) (st : state) (ast : astate) : option (state * astate * obs) :=
  let ist := (st, ast) in
  match CTInterpreter.evaluate _ (CTInterpreter.cteval_engine_aux f c) ist with
  | CTInterpreter.ROk _ _ os (st', ast') => Some (st', ast', os)
  | _ => None
  end.

(** ** Type system for cryptographic constant-time programming *)

(* Imported straight from TestingStateIFC.v, so don't bother testing them. *)

(* TERSE: HIDEFROMHTML *)
Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.
Definition pub_arrs := total_map label.

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

Definition gen_pub_arrs : G pub_vars :=
  default <- arbitrary;;
  a0 <- arbitrary;;
  a1 <- arbitrary;;
  a2 <- arbitrary;;
  ret (
    "A0" !-> a0; "A1" !-> a1;
    "A2" !-> a2;
    _ !-> default
  ) % string.

(* Returns a variable which has the label l in P *)
Definition gen_var_with_label (P : pub_vars) (l: label) : G (option var_id) :=
  let '(d, m) := P in
  let all_variables := union (map_dom m) ["X0"; "X1"; "X2"; "X3"; "X4"] % string in
  let variables_in_l := List.filter (fun v => Bool.eqb (apply P v) l) all_variables in

  oneOf_
    (ret None)
    (List.map (fun v => ret (Some (Var v))) variables_in_l).

QuickChick (forAll gen_pub_vars (fun (P : pub_vars) =>
    forAll (gen_var_with_label P public) (fun v => match v with
      | Some v => apply P v
      | None => true
      end
  ))).
QuickChick (forAll gen_pub_vars (fun (P : pub_vars) =>
    forAll (gen_var_with_label P secret) (fun v => match v with
      | Some v => negb (apply P v)
      | None => true
      end
  ))).

(* Returns an array A0..A2 which has the label l in P *)
Definition gen_arr_with_label (P : pub_vars) (l: label) : G (option arr_id) :=
  let '(d, m) := P in
  let all_variables := union (map_dom m) ["A0"; "A1"; "A2"] % string in
  let variables_in_l := List.filter (fun v => Bool.eqb (apply P v) l) all_variables in

  oneOf_
    (ret None)
    (List.map (fun v => ret (Some (Arr v))) variables_in_l).

Definition pub_equiv (P : total_map label) {X:Type} (s1 s2 : total_map X) :=
  forall x:string, apply P x = true -> apply s1 x = apply s2 x.

(* TODO: It would be cool to automatically derive this for any total_map X,
   where boolean equality for X is decidable *)
Definition pub_equivb (P : total_map label) (s1 s2 : state) : bool :=
  match P, s1, s2 with
  | (dP,mP), (d1,m1), (d2,m2) =>
      if dP
      then forallb (fun x => if apply P x
                             then apply s1 x =? apply s2 x else true)
                   (union (map_dom mP) (union (map_dom m1) (map_dom m2)))
           && (d1 =? d2)
      else forallb (fun x => if apply P x
                             then apply s1 x =? apply s2 x else true)
                   (map_dom mP)
  end.
Definition pub_equivb_astate (P : total_map label) (a1 a2 : astate) : bool :=
  match P, a1, a2 with
  | (dP,mP), (d1,m1), (d2,m2) =>
      if dP
      then forallb (fun x => if apply P x
                             then forallb (fun '(a, b) => a =? b) (List.combine (apply a1 x) (apply a2 x))
                             else true)
                   (union (map_dom mP) (union (map_dom m1) (map_dom m2)))
           && (forallb (fun '(a, b) => a =? b) (List.combine d1 d2))
      else forallb (fun x => if apply P x
                             then forallb (fun '(a, b) => a =? b) (List.combine (apply a1 x) (apply a2 x)) else true)
                   (map_dom mP)
  end.

(* TODO: do the proof. (looks hard) *)
(* #[export] Instance decPubEquiv P (s1 s2 : state) : Dec (pub_equiv P s1 s2). *)
(* Proof. dec_eq. Defined. *)

Definition gen_pub_equiv (P : total_map label) {X: Type} `{Gen X} (s: total_map X) : G (total_map X) :=
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map X)) (c : string * X) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if apply P k then ret v else arbitrary);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

(* TODO: it would be cool to unify these two shrinkers. *)
Definition shrink_pub_equiv_state (P : total_map label) (s : state) : state -> list state :=
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
             if negb (apply P k) || (v =? d)
             then before ++ after (* public or same value as default *)
             else before ++ (k, v) :: after in

           replacement :: acc
        ) m []) in

    if can_shrink_default
    then (List.map (fun d' => (d', m)) (shrink d)) ++ (secret_entries_shrunk ++ entries_removed)
    else secret_entries_shrunk ++ entries_removed.
Definition shrink_pub_equiv_astate (P : total_map label) (a : astate) : astate -> list astate :=
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
             if negb (apply P k) || (forallb (fun '(x1, x2) => x1 =? x2) (List.combine v d))
             then before ++ after (* public or same value as default *)
             else before ++ (k, v) :: after in

           replacement :: acc
        ) m []) in

    if can_shrink_default
    then (List.map (fun d' => (d', m)) (shrink d)) ++ (secret_entries_shrunk ++ entries_removed)
    else secret_entries_shrunk ++ entries_removed.

QuickChick (forAll gen_pub_vars (fun P =>

    forAll gen_state (fun s =>
    forAll (gen_pub_equiv P s) (fun s' =>

    let shrunk := shrink_pub_equiv_state P s s' in
    printTestCase ((show shrunk) ++ nl) (
      forallb (fun s'' => pub_equivb P s s'') shrunk
    )
  )))).
QuickChick (forAll gen_pub_vars (fun P =>

    forAll gen_astate (fun a =>
    forAll (gen_pub_equiv P a) (fun a' =>

    let shrunk := shrink_pub_equiv_astate P a a' in
    printTestCase ((show shrunk) ++ nl) (
      forallb (fun a'' => pub_equivb_astate P a a'') shrunk
    )
  )))).

Lemma pub_equiv_refl : forall {X:Type} (P : total_map label) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall {X:Type} (P : total_map label) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof. unfold pub_equiv. intros X P s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall {X:Type} (P : total_map label) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof.
  unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
  rewrite H12; try rewrite H23; auto.
Qed.

Definition join (l1 l2 : label) : label := l1 && l2.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

(* Generates a variable X such that `can_flow l1 (P X) = true` *)
Definition gen_can_flow (P : pub_vars) (l1 : label) : G (option var_id) :=
  if l1 then
    (* Public source. Can flow anywhere. *)
    X <- arbitrary;;
    ret (Some X)
  else
    (* Secret source. Can only flow in secret variables. *)
    gen_var_with_label P secret.

Reserved Notation "P '|-a-' a \IN l" (at level 40).
Reserved Notation "P '|-b-' b \IN l" (at level 40).

Inductive aexp_has_label (P:pub_vars) : aexp -> label -> Prop :=
  | T_Num : forall n,
       P |-a- (ANum n) \IN public
  | T_Id : forall X,
       P |-a- (AId X) \IN (apply P X)
  | T_Plus : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 + a2 }> \IN (join l1 l2)
  | T_Minus : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 - a2 }> \IN (join l1 l2)
  | T_Mult : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ a1 * a2 }> \IN (join l1 l2)
  | T_CTIf : forall be l a1 l1 a2 l2,
       P |-b- be \IN l ->
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-a- <{ be ? a1 : a2 }> \IN (join l (join l1 l2))

where "P '|-a-' a '\IN' l" := (aexp_has_label P a l)

with bexp_has_label (P:pub_vars) : bexp -> label -> Prop :=
  | T_True :
       P |-b- <{ true }> \IN public
  | T_False :
       P |-b- <{ false }> \IN public
  | T_Eq : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 = a2 }> \IN (join l1 l2)
  | T_Neq : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 <> a2 }> \IN (join l1 l2)
  | T_Le : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 <= a2 }> \IN (join l1 l2)
  | T_Gt : forall a1 l1 a2 l2,
       P |-a- a1 \IN l1 ->
       P |-a- a2 \IN l2 ->
       P |-b- <{ a1 > a2 }> \IN (join l1 l2)
  | T_Not : forall b l,
       P |-b- b \IN l ->
       P |-b- <{ ~b }> \IN l
  | T_And : forall b1 l1 b2 l2,
       P |-b- b1 \IN l1 ->
       P |-b- b2 \IN l2 ->
       P |-b- <{ b1 && b2 }> \IN (join l1 l2)

where "P '|-b-' b '\IN' l" := (bexp_has_label P b l).

Scheme aexp_bexp_has_label_ind := Induction for aexp_has_label Sort Prop
with bexp_aexp_has_label_ind := Induction for bexp_has_label Sort Prop.
Combined Scheme aexp_bexp_has_label_mutind
  from aexp_bexp_has_label_ind, bexp_aexp_has_label_ind.

(* TODO: it would be cool to derive it automatically, like that: *)
(* Derive ArbitrarySizedSuchThat for (fun a => aexp_has_label P a l). *)

(* To implement Gen, we can combine a sized generator and sized *)
Fixpoint gen_public_aexp_sized (P : pub_vars) (size : nat) : G aexp :=
  match size with
    | 0 =>
        n <- arbitrary;;
        let num := ret (ANum n) in

        X <- gen_var_with_label P public;;
        let var := match X with
          | Some X => [ret (AId X)]
          | None => []
          end in

        oneOf_ num (num::var)
    | S size' =>
        n <- arbitrary;;
        let num := ret (ANum n) in

        X <- gen_var_with_label P public;;
        let var := match X with
          | Some X => [ret (AId X)]
          | None => []
          end in

        let possibilities := (num :: var) ++ [
          thunkGen (fun _ =>
            a1 <- gen_public_aexp_sized P size';;
            a2 <- gen_public_aexp_sized P size';;
            ret <{ a1 + a2 }>
          );
          thunkGen (fun _ =>
            a1 <- gen_public_aexp_sized P size';;
            a2 <- gen_public_aexp_sized P size';;
            ret <{ a1 - a2 }>
          );
          thunkGen (fun _ =>
            a1 <- gen_public_aexp_sized P size';;
            a2 <- gen_public_aexp_sized P size';;
            ret <{ a1 * a2 }>
          );
          thunkGen (fun _ =>
            be <- gen_public_bexp_sized P size';;
            a1 <- gen_public_aexp_sized P size';;
            a2 <- gen_public_aexp_sized P size';;
            ret <{ be ? a1 : a2 }>
          )
        ] in

        oneOf_ num possibilities
    end
with gen_public_bexp_sized (P : pub_vars) (size : nat) : G bexp :=
  match size with
    | 0 =>
        oneOf [
          ret <{ true }>;
          ret <{ false }>
        ]
    | S size' =>
        oneOf_ (ret <{ true }>) [
          ret <{ true }>;
          ret <{ false }>;
          (a1 <- gen_public_aexp_sized P size';;
           a2 <- gen_public_aexp_sized P size';;
           ret <{ a1 = a2 }>);
          (a1 <- gen_public_aexp_sized P size';;
           a2 <- gen_public_aexp_sized P size';;
           ret <{ a1 <> a2 }>);
          (a1 <- gen_public_aexp_sized P size';;
           a2 <- gen_public_aexp_sized P size';;
           ret <{ a1 <= a2 }>);
          (a1 <- gen_public_aexp_sized P size';;
           a2 <- gen_public_aexp_sized P size';;
           ret <{ a1 > a2 }>);
          (b <- gen_public_bexp_sized P size';;
           ret <{ ~b }>);
          (b1 <- gen_public_bexp_sized P size';;
           b2 <- gen_public_bexp_sized P size';;
           ret <{ b1 && b2 }>)
        ]
  end.

Fixpoint gen_secret_aexp_sized_nofail (dummy : var_id) (secret_variables : list var_id) (size : nat) : G aexp :=
  match size with
  | 0 =>
      X <- elems_ dummy secret_variables;;
      ret (AId X)
  | S size' =>
      (* secret *)
      oneOf [
        thunkGen (fun _ =>
          X <- elems_ dummy secret_variables;;
          ret (AId X)
        );
        thunkGen (fun _ =>
          a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          ret <{ a1 + a2 }>
        );
        thunkGen (fun _ =>
          a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          ret <{ a1 - a2 }>
        );
        thunkGen (fun _ =>
          a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          ret <{ a1 * a2 }>
        );
        thunkGen (fun _ =>
          be <- gen_secret_bexp_sized_nofail dummy secret_variables size';;
          a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
          ret <{ be ? a1 : a2 }>
        )
      ]
    end
with gen_secret_bexp_sized_nofail (dummy : var_id) (secret_variables : list var_id) (size : nat) : G bexp :=
  match size with
    | 0 => (* Cheat so that we don't have to return None *)
        oneOf [
          thunkGen (fun _ =>
            x1 <- elems_ dummy secret_variables;;
            x2 <- elems_ dummy secret_variables;;
            ret <{ (AId x1) <= (AId x2) }>
          );
          thunkGen (fun _ =>
            x1 <- elems_ dummy secret_variables;;
            x2 <- elems_ dummy secret_variables;;
            ret <{ (AId x1) > (AId x2) }>
          );
          thunkGen (fun _ =>
            x1 <- elems_ dummy secret_variables;;
            x2 <- elems_ dummy secret_variables;;
            ret <{ (AId x1) = (AId x2) }>
          );
          thunkGen (fun _ =>
            x1 <- elems_ dummy secret_variables;;
            x2 <- elems_ dummy secret_variables;;
            ret <{ (AId x1) <> (AId x2) }>
          )
        ]
    | S size' =>
        oneOf [
          thunkGen (fun _ =>
            a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            ret <{ a1 <= a2 }>
          );
          thunkGen (fun _ =>
            a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            ret <{ a1 > a2 }>
          );
          thunkGen (fun _ =>
            a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            ret <{ a1 = a2 }>
          );
          thunkGen (fun _ =>
            a1 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            a2 <- gen_secret_aexp_sized_nofail dummy secret_variables size';;
            ret <{ a1 <> a2 }>
          );
          thunkGen (fun _ =>
            b <- gen_secret_bexp_sized_nofail dummy secret_variables size';;
            ret <{ ~b }>
          );
          thunkGen (fun _ =>
            b1 <- gen_secret_bexp_sized_nofail dummy secret_variables size';;
            b2 <- gen_secret_bexp_sized_nofail dummy secret_variables size';;
            ret <{ b1 && b2 }>
          )
        ]
  end.
(* CH: This is not really needed *)
Definition gen_secret_aexp_sized (P : pub_vars) (size : nat) : G (option aexp) :=
  let all_variables := union (map_dom (snd P)) ["X0"; "X1"; "X2"; "X3"; "X4"] % string in
  let secret_variables := List.filter (fun v => negb (apply P v)) all_variables in
  let secret_variables := List.map (fun v => Var v) secret_variables in

  match secret_variables with
  | [] => ret None
  | dummy::_ =>
      a <- gen_secret_aexp_sized_nofail dummy secret_variables size;;
      ret (Some a)
  end.
Definition gen_secret_bexp_sized (P : pub_vars) (size : nat) : G (option bexp) :=
  let all_variables := union (map_dom (snd P)) ["X0"; "X1"; "X2"; "X3"; "X4"] % string in
  let secret_variables := List.filter (fun v => negb (apply P v)) all_variables in
  let secret_variables := List.map (fun v => Var v) secret_variables in

  match secret_variables with
  | [] => ret None
  | dummy::_ =>
      b <- gen_secret_bexp_sized_nofail dummy secret_variables size;;
      ret (Some b)
  end.

QuickChick (forAll gen_pub_vars (fun P => 
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll (gen_public_aexp_sized P 3) (fun a =>
      (aeval s1 a) =? (aeval s2 a)
  ))))).

QuickChick (forAll gen_pub_vars (fun P => 
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll (gen_public_bexp_sized P 3) (fun b =>
      Bool.eqb (beval s1 b) (beval s2 b)
  ))))).

Fixpoint label_of_aexp (P : pub_vars) (a : aexp) : label := match a with
  | ANum _ => public
  | AId v => apply P v
  | <{ a1 + a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ a1 - a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ be ? a1 : a2 }> => join (label_of_bexp P be) (join (label_of_aexp P a1) (label_of_aexp P a2))
end
with label_of_bexp (P : pub_vars) (b : bexp) : label := match b with
  | <{ a1 = a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ a1 <> a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ a1 <= a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  | <{ true }> => public
  | <{ false }> => public
end.

QuickChick (forAll gen_pub_vars (fun P =>
  forAll (sized (gen_public_aexp_sized P)) (fun a =>
    Bool.eqb (label_of_aexp P a) public
  ))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAllMaybe (gen_secret_aexp_sized P 3) (fun a =>
    Bool.eqb (label_of_aexp P a) secret
  ))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAll (gen_public_bexp_sized P 3) (fun b =>
    Bool.eqb (label_of_bexp P b) public
  ))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAllMaybe (gen_secret_bexp_sized P 3) (fun b =>
    Bool.eqb (label_of_bexp P b) secret
  ))).

Definition shrink_var_preserve_label (P : pub_vars) (v : var_id) : list var_id :=
  let '(Var v) := v in

  let fix get_first_var_with_label (n : nat) : option var_id :=
    let var := ("X" ++ (String (ascii_of_nat n) EmptyString)) % string in
    if Bool.eqb (apply P var) (apply P v)
    then Some (Var var)
    else (match n with
      | O => None
      | S n => get_first_var_with_label n
      end
    )
  in

  (* Assume v is of the form Xn *)
  match get 1 v with
  | Some c => match nat_of_ascii c - nat_of_ascii "0" with
      | 0 => []
      | S pred => match get_first_var_with_label pred with
        | None => []
        | Some v => [v]
        end
      end
  | None => []
  end.
Definition shrink_arr_preserve_label (P : pub_vars) (v : arr_id) : list arr_id :=
  let '(Arr v) := v in

  let fix get_first_arr_with_label (n : nat) : option arr_id :=
    let arr := ("A" ++ (String (ascii_of_nat n) EmptyString)) % string in
    if Bool.eqb (apply P arr) (apply P v)
    then Some (Arr arr)
    else (match n with
      | O => None
      | S n => get_first_arr_with_label n
      end
    )
  in

  (* Assume v is of the form An *)
  match get 1 v with
  | Some c => match nat_of_ascii c - nat_of_ascii "0" with
      | 0 => []
      | S pred => match get_first_arr_with_label pred with
        | None => []
        | Some v => [v]
        end
      end
  | None => []
  end.
QuickChick (forAll gen_pub_vars (fun P =>
    forAll arbitrary (fun (X : var_id) =>

    let l := apply P X in

    forallb (fun '(Var X') => Bool.eqb (apply P X') l) (shrink_var_preserve_label P X)
  ))).
QuickChick (
    forAll gen_pub_arrs (fun PA =>
    forAll arbitrary (fun (a : var_id) =>
    let l := apply PA a in

    forallb (fun '(Arr a') => Bool.eqb (apply PA a') l) (shrink_arr_preserve_label PA a)
  ))).

(* Shrinker that preserve the label of aexp/bexp *)
Fixpoint shrink_bexp_with_label (P : pub_vars) (l : label) (b : bexp) : list bexp :=
  match b with
  | <{ a1 = a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk = a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 = shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ a1 <> a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk <> a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 <> shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ a1 <= a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk <= a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 <= shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ a1 > a2 }> =>
      (map (fun shrunk : aexp => <{ shrunk > a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 > shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ ~ b1 }> =>
      [b1] ++
      (map (fun shrunk : bexp => <{ ~ shrunk }>) (shrink_bexp_with_label P l b1))
  | <{ b1 && b2 }> =>
      [b1; b2] ++
      (map (fun shrunk : bexp => <{ shrunk && b2 }>) (shrink_bexp_with_label P l b1)) ++
      (map (fun shrunk : bexp => <{ b1 && shrunk }>) (shrink_bexp_with_label P l b2))
  | _ => []
  end
with shrink_aexp_with_label (P : pub_vars) (l : label) (a : aexp) : list aexp :=
  match a with
  | ANum n => map (fun n => ANum n) (shrink n)
  | AId v => map (fun v => AId v) (shrink_var_preserve_label P v)
  | <{ a1 + a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk + a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 + shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ a1 - a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk - a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 - shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ a1 * a2 }> =>
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ shrunk * a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ a1 * shrunk }>) (shrink_aexp_with_label P l a2))
  | <{ be ? a1 : a2 }> =>
      (map (fun shrunk : bexp => <{ shrunk ? a1 : a2 }>) (shrink_bexp_with_label P l be)) ++
      [a1; a2] ++
      (map (fun shrunk : aexp => <{ be ? shrunk : a2 }>) (shrink_aexp_with_label P l a1)) ++
      (map (fun shrunk : aexp => <{ be ? a1 : shrunk }>) (shrink_aexp_with_label P l a2))
  end.

QuickChick (forAll gen_pub_vars (fun P =>
  forAll (sized (gen_public_aexp_sized P)) (fun a =>
  let candidates := shrink_aexp_with_label P public a in

  printTestCase ((show candidates) ++ nl)

  (forallb (fun a' => Bool.eqb (label_of_aexp P a') public) candidates)
))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAll (sized (gen_public_bexp_sized P)) (fun b =>
  let candidates := shrink_bexp_with_label P public b in

  printTestCase ((show candidates) ++ nl)

  (forallb (fun b' => Bool.eqb (label_of_bexp P b') public) candidates)
))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAllMaybe (gen_secret_aexp_sized P 3) (fun a =>
  let candidates := shrink_aexp_with_label P secret a in

  printTestCase ((show candidates) ++ nl)

  (forallb (fun a' => Bool.eqb (label_of_aexp P a') secret) candidates)
))).
QuickChick (forAll gen_pub_vars (fun P =>
  forAllMaybe (gen_secret_bexp_sized P 3) (fun b =>
  let candidates := shrink_bexp_with_label P secret b in

  printTestCase ((show candidates) ++ nl)

  (forallb (fun b' => Bool.eqb (label_of_bexp P b') secret) candidates)
))).

Theorem noninterferent_aexp_bexp : forall P s1 s2,
  pub_equiv P s1 s2 ->
  (forall a l, P |-a- a \IN l ->
   l = public -> aeval s1 a = aeval s2 a) /\
  (forall b l, P |-b- b \IN l ->
   l = public -> beval s1 b = beval s2 b).
Proof.
  intros P s1 s2 Heq. apply (aexp_bexp_has_label_mutind P);
    simpl; intros;
    (repeat match goal with
    | [Heql : join _ _ = public |- _] =>
      let G1 := fresh "G1" in
      let G2 := fresh "G2" in
      destruct (join_public Heql) as [G1 G2];
      rewrite G1 in *; rewrite G2 in *
    end); try reflexivity; eauto; firstorder;
    (repeat match goal with
    | [IH : aeval s1 ?a = aeval s2 ?a |- _] => rewrite IH
    end);
    (repeat match goal with
    | [IH : beval s1 ?b = beval s2 ?b |- _] => rewrite IH
    end); reflexivity.
Qed.

Theorem noninterferent_aexp : forall {P s1 s2 a},
  pub_equiv P s1 s2 ->
  P |-a- a \IN public ->
  aeval s1 a = aeval s2 a.
Proof.
  intros P s1 s2 a Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

Theorem noninterferent_bexp : forall {P s1 s2 b},
  pub_equiv P s1 s2 ->
  P |-b- b \IN public ->
  beval s1 b = beval s2 b.
Proof.
  intros P s1 s2 b Heq Ht. remember public as l.
  generalize dependent Heql. generalize dependent l.
  apply noninterferent_aexp_bexp. assumption.
Qed.

(* Counterexample: PC well typed programs aren't secure with respect to
                   constant time execution. *)
Fixpoint gen_pc_well_typed_sized (P : pub_vars) (PA : pub_arrs) (size : nat) : G com :=
  let skip := ret <{ skip }> in
  let base_ctors := [
    (* Skip *)
    skip;

    (* Assignments *)
    thunkGen (fun _ =>
      X <- (genVarId).(arbitrary);;
      let l := apply P X in
      a <- (if l then gen_public_aexp_sized P 2 else arbitrary);;
      ret <{ X := a }>
    );

    (* Array writes *)
    thunkGen (fun _ =>
      a <- (genArrId).(arbitrary);;
      i <- arbitrary;;
      let l := apply PA a in
      e <- match l with
        | false => arbitrary
        | true => gen_public_aexp_sized P 2
        end;;
      ret <{ a[i] <- e }>
    );

    (* Array reads
       We sometimes return `skip` in order not to backtrack. *)
    thunkGen (fun _ =>
      x <- (genVarId).(arbitrary);;
      let l := apply P x in
      i <- arbitrary;;
      a <- match l with
        | true => gen_arr_with_label PA public
        | false => (a <- arbitrary;; ret (Some a))
        end;;
      match a with
      | None => ret <{ skip }>
      | Some a => ret <{ x <- a[[i]] }>
      end
    )
  ] in

  match size with
  | O => oneOf_ skip base_ctors
  | S size' =>
      let recursive_ctors := [
        thunkGen (fun _ =>
          c1 <- gen_pc_well_typed_sized P PA size';;
          c2 <- gen_pc_well_typed_sized P PA size';;
          ret <{ c1; c2 }>
        );

        thunkGen (fun _ =>
          b <- gen_public_bexp_sized P 2;;
          c1 <- gen_pc_well_typed_sized P PA size';;
          c2 <- gen_pc_well_typed_sized P PA size';;
          ret <{ if b then c1 else c2 end }>
        );

        thunkGen (fun _ =>
          b <- gen_public_bexp_sized P 2;;
          c <- gen_pc_well_typed_sized P PA size';;
          ret <{ while b do c end }>
        )
      ] in

      oneOf_ skip (recursive_ctors ++ base_ctors)
  end.

(* Given a pub_arrs, returns a new pub_arrs that is publicly equivalent
   and where all arrays have the same length.
   This is often desirable not to find trivial counterexamples where one execution
   crashes because of an out-of-bounds access, while the second execution succeeds. *)
Definition gen_pub_equiv_and_same_length (PA : pub_arrs) (a : astate) : G astate :=
  let fix gen_same_length (l : list nat) : G (list nat) :=
    match l with
    | _::q => q' <- gen_same_length q;;
        x <- arbitrary;;
        ret (x::q')
    | [] => ret []
    end in

  let '(d, m) := a in
  new_m <- List.fold_left (fun (acc : G (Map (list nat))) (c : string * (list nat)) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if apply PA k
      then ret v
      else gen_same_length v);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

(* TODO: shrinking *)
QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (sized (gen_pc_well_typed_sized P PA)) (fun c =>

    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv_and_same_length P a1) (fun a2 =>

    let r1 := cteval_engine 1000 c s1 a1 in
    let r2 := cteval_engine 1000 c s2 a2 in
    match (r1, r2) with
    | (Some (s1', a1', os1'), Some (s2', a2', os2')) =>
        checker (obs_eqb os1' os2')
    | _ => (* discard *)
        checker tt
    end
  )))))))).

(* TERSE: /HIDEFROMHTML *)

(** [[[
                         ------------------                 (CT_Skip)
                         P !! PA |-ct- skip

             P |-a- a \IN l    can_flow l (P X) = true
             -----------------------------------------      (CT_Asgn)
                       P !! PA |-ct- X := a

               P !! PA |-ct- c1    P !! PA |-ct- c2
               ------------------------------------          (CT_Seq)
                       P !! PA |-ct- c1;c2

  P |-b- b \IN public    P !! PA |-ct- c1    P !! PA |-ct- c2
  ----------------------------------------------------------- (CT_If)
               P !! PA |-ct- if b then c1 else c2

                  P |-b- b \IN public    P |-ct- c
                  --------------------------------         (CT_While)
                  P !! PA |-ct- while b then c end

      P |-a- i \IN public   can_flow (PA a) (P x) = true
      --------------------------------------------------   (CT_ARead)
                  P !! PA |-ct- x <- a[[i]]

P |-a- i \IN public   P |-a- e \IN l   can_flow l (PA a) = true
--------------------------------------------------------------- (CT_AWrite)
                   P !! PA |-ct- a[i] <- e
]]]
*)

(* TERSE: HIDEFROMHTML *)
(* ';;' conflicted with QuickChick's monadic magic operators, changed it to !! *)
Reserved Notation "P '!!' PA '|-ct-' c" (at level 40).

Inductive ct_well_typed (P:pub_vars) (PA:pub_arrs) : com -> Prop :=
  | CT_Skip :
      P !! PA |-ct- <{{ skip }}>
  | CT_Asgn : forall X a l,
      P |-a- a \IN l ->
      can_flow l (apply P X) = true ->
      P !! PA |-ct- <{{ X := a }}>
  | CT_Seq : forall c1 c2,
      P !! PA |-ct- c1 ->
      P !! PA |-ct- c2 ->
      P !! PA |-ct- <{{ c1 ; c2 }}>
  | CT_If : forall be c1 c2,
      P |-b- be \IN public ->
      P !! PA |-ct- c1 ->
      P !! PA |-ct- c2 ->
      P !! PA |-ct- <{{ if be then c1 else c2 end }}>
  | CT_While : forall be c1,
      P |-b- be \IN public ->
      P !! PA |-ct- c1 ->
      P !! PA |-ct- <{{ while be do c1 end }}>
  | CT_ARead : forall x a i,
      P |-a- i \IN public ->
      can_flow (apply PA a) (apply P x) = true ->
      P !! PA |-ct- <{{ x <- a[[i]] }}>
  | CT_AWrite : forall a i e l,
      P |-a- i \IN public ->
      P |-a- e \IN l ->
      can_flow l (apply PA a) = true ->
      P !! PA |-ct- <{{ a[i] <- e }}>

where "P !! PA '|-ct-' c" := (ct_well_typed P PA c).
(* TERSE: /HIDEFROMHTML *)

Fixpoint gen_ct_well_typed_sized (P : pub_vars) (PA : pub_arrs) (size : nat) : G com :=
  let skip := ret <{ skip }> in
  let base_ctors := [
    (* Skip *)
    skip;

    (* Assignments *)
    thunkGen (fun _ =>
      X <- (genVarId).(arbitrary);;
      let l := apply P X in
      a <- (if l then gen_public_aexp_sized P 2 else arbitrary);;
      ret <{ X := a }>
    );

    (* Array writes *)
    thunkGen (fun _ =>
      a <- (genArrId).(arbitrary);;
      i <- gen_public_aexp_sized P 2;;
      let l := apply PA a in
      e <- match l with
        | false => arbitrary
        | true => gen_public_aexp_sized P 2
        end;;
      ret <{ a[i] <- e }>
    );

    (* Array reads
       We sometimes return `skip` in order not to backtrack. *)
    thunkGen (fun _ =>
      x <- (genVarId).(arbitrary);;
      let l := apply P x in
      i <- gen_public_aexp_sized P 2;;
      a <- match l with
        | true => gen_arr_with_label PA public
        | false => (a <- arbitrary;; ret (Some a))
        end;;
      match a with
      | None => ret <{ skip }>
      | Some a => ret <{ x <- a[[i]] }>
      end
    )
  ] in

  match size with
  | O => oneOf_ skip base_ctors
  | S size' =>
      let recursive_ctors := [
        thunkGen (fun _ =>
          c1 <- gen_ct_well_typed_sized P PA size';;
          c2 <- gen_ct_well_typed_sized P PA size';;
          ret <{ c1; c2 }>
        );

        thunkGen (fun _ =>
          b <- gen_public_bexp_sized P 2;;
          c1 <- gen_ct_well_typed_sized P PA size';;
          c2 <- gen_ct_well_typed_sized P PA size';;
          ret <{ if b then c1 else c2 end }>
        );

        thunkGen (fun _ =>
          b <- gen_public_bexp_sized P 2;;
          c <- gen_ct_well_typed_sized P PA size';;
          ret <{ while b do c end }>
        )
      ] in

      oneOf_ skip (recursive_ctors ++ base_ctors)
  end.

Fixpoint shrink_ct_well_typed (P : pub_vars) (PA : pub_arrs) (c : com) : list com :=
  match c with
    | <{{ skip }}> => []
    | <{{ x := e }}> =>
        let l := label_of_aexp P e in

        (* when shrinking the variable, we have to preserve: can_flow l (P x) *)
        (map (fun shrunk : var_id => <{{ shrunk := e }}>) (match l with
          | true => shrink x (* public and secret are possible *)
          | false => shrink_var_preserve_label P x (* only secret (if e is secret, and x is too) *)
          end)) ++
        (* preserve P |-a- e \in l *)
        (map (fun shrunk : aexp => <{{ x := shrunk }}>) (shrink_aexp_with_label P l e))
    | <{{ c1; c2 }}> =>
        [c1; c2] ++
        (map (fun shrunk : com => <{{ shrunk; c2 }}>) (shrink_ct_well_typed P PA c1)) ++
        (map (fun shrunk : com => <{{ c1; shrunk }}>) (shrink_ct_well_typed P PA c2))
    | <{{ if be then c1 else c2 end }}> =>
        [c1; c2] ++
        (map (fun shrunk : bexp => <{{ if shrunk then c1 else c2 end }}>) (shrink_bexp_with_label P public be)) ++
        (map (fun shrunk : com => <{{ if be then shrunk else c2 end }}>) (shrink_ct_well_typed P PA c1)) ++
        (map (fun shrunk : com => <{{ if be then c1 else shrunk end }}>) (shrink_ct_well_typed P PA c2))
    | <{{ while be do c end }}> =>
        [c] ++
        (map (fun shrunk : bexp => <{{ while shrunk do c end }}>) (shrink_bexp_with_label P public be)) ++
        (map (fun shrunk : com => <{{ while be do shrunk end }}>) (shrink_ct_well_typed P PA c))
    | <{{ x <- a [[i]] }}> =>
        (* preserve can_flow (PA a) (P x) = true *)
        (map (fun shrunk : var_id => <{{ shrunk <- a [[i]] }}>) (match apply PA a with
          | true => shrink x (* secret and public are possible *)
          | false => shrink_var_preserve_label P x (* only secret (if a is secret, then x is too) *)
          end)) ++
        (* preserve can_flow (PA a) (P x) = true *)
        (map (fun shrunk : arr_id => <{{ x <- shrunk [[i]] }}>) (match apply P x with
          | true => shrink_arr_preserve_label PA a (* only public *)
          | false => shrink a (* secret and public are possible *)
          end)) ++
        (* preserve P |-a- i \in public *)
        (map (fun shrunk : aexp => <{{ x <- a [[shrunk]] }}>) (shrink_aexp_with_label P public i))
    | <{{ a [ie] <- e }}> =>
        let l := label_of_aexp P e in

        (* preserve can_flow l (PA a) *)
        (map (fun shrunk : arr_id => <{{ shrunk [ie] <- e }}>) (match l with
          | true => shrink a (* secret and public are possible *)
          | false => shrink_arr_preserve_label PA a (* only private *)
          end)) ++
        (* preserve P |-a- ie \in public *)
        (map (fun shrunk : aexp => <{{ a [shrunk] <- e }}>) (shrink_aexp_with_label P public ie)) ++
        (* preserve P |-a- e \in l *)
        (map (fun shrunk : aexp => <{{ a [ie] <- shrunk }}>) (shrink_aexp_with_label P l e))
  end.

Fixpoint ct_typechecker (P PA:pub_vars) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (label_of_aexp P a) (apply P X)
  | <{ c1 ; c2 }> => ct_typechecker P PA c1 && ct_typechecker P PA c2
  | <{ if b then c1 else c2 end }> =>
      label_of_bexp P b && ct_typechecker P PA c1 && ct_typechecker P PA c2
  | <{ while b do c1 end }> =>
      label_of_bexp P b && ct_typechecker P PA c1
  | <{{ x <- a[[i]] }}> =>
      label_of_aexp P i && can_flow (apply PA a) (apply P x)
  | <{{ a[i] <- e }}> =>
      label_of_aexp P i && can_flow (label_of_aexp P e) (apply PA a)
  end.

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed_sized P PA 3) (fun c =>
  ct_typechecker P PA c)))).

QuickChick (
  forAll gen_pub_vars (fun P =>
  forAll gen_pub_arrs (fun PA =>
  forAll (gen_ct_well_typed_sized P PA 3)  (fun c =>
  (forallb (ct_typechecker P PA) (shrink_ct_well_typed P PA c)))))).

(** ** Final theorems: noninterference and constant-time security *)

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (gen_ct_well_typed_sized P PA 3) (fun c =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv PA a1) (fun a2 =>
      let r1 := cteval_engine 1000 c s1 a1 in
      let r2 := cteval_engine 1000 c s2 a2 in
      match (r1, r2) with
      | (Some (s1', a1', os1), Some (s2', a2', os2)) =>
          checker ((pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2'))
      | _ => (* discard *)
          checker tt
      end
  )))))))).

Theorem ct_well_typed_noninterferent :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2,
    P !! PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1)> =[ c ]=> <(s1', a1', os1)> ->
    <(s2, a2)> =[ c ]=> <(s2', a2', os2)> ->
    pub_equiv P s1' s2' /\ pub_equiv PA a1' a2'.
(* FOLD *)
Proof.
  Admitted.
  (* TODO: update the proof below (the definitions have changed because of the switch
           to list-based maps) *)
  (*
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - split; auto.
  - split; auto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      eapply noninterferent_aexp; eauto.
      subst. rewrite Hy in H11.
      unfold can_flow in H11. simpl in H11.
      destruct l; try discriminate. auto.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - edestruct IHHeval1_2; eauto.
    + eapply IHHeval1_1; eauto.
    + eapply IHHeval1_1; eauto.
  - eapply IHHeval1; eauto.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto. now destruct (PA a).
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - (* NEW CASE: AWrite *)
    split; eauto.
    erewrite noninterferent_aexp; eauto.
    intros y Hy.
    destruct (String.eqb_spec a y) as [Hay | Hay].
    + rewrite Hay. do 2 rewrite t_update_eq.
      subst. rewrite Hy in *.
      rewrite Haeq; eauto.
      erewrite (noninterferent_aexp Heq); eauto. now destruct l.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hay).
      apply Haeq. apply Hy.
Qed.*)
(* /FOLD *)

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (gen_ct_well_typed_sized P PA 3) (fun c =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv PA a1) (fun a2 =>
      let r1 := cteval_engine 1000 c s1 a1 in
      let r2 := cteval_engine 1000 c s2 a2 in
      match (r1, r2) with
      | (Some (s1', a1', os1), Some (s2', a2', os2)) =>
          checker (obs_eqb os1 os2)
      | _ => (* discard *)
          checker tt
      end
  )))))))).

Theorem ct_well_typed_ct_secure :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2,
    P !! PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1)> =[ c ]=> <(s1', a1', os1)> ->
    <(s2, a2)> =[ c ]=> <(s2', a2', os2)> ->
    os1 = os2.
(* FOLD *)
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' os1 os2
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2.
  induction Heval1; intros os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
    + eapply ct_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption | eassumption ];
        eassumption.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - rewrite (noninterferent_bexp Heq H13) in H.
    rewrite H in H8. discriminate H8.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* NEW CASE: ARead *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* NEW CASE: AWrite *)
    f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.
(* /FOLD *)

(** * Speculative constant-time *)

(** This part is based on the "Spectre Declassified" paper from IEEE SP 2023,
    just in simplified form. *)

(** The observations are the same as above, so we can just reuse them. *)

Print observation.

(** We additionally add adversary provided directions to our semantics, which
    control speculation behavior. *)

Inductive direction :=
  | DStep
  | DForce
  | DLoad (a : string) (i : nat)
  | DStore (a : string) (i : nat).

Definition dirs := list direction.

Reserved Notation
         "'<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive spec_eval : com -> state -> astate -> bool -> dirs ->
                             state -> astate -> bool -> obs -> Prop :=
  | Spec_Skip : forall st ast b,
      <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Spec_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Spec_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Spec_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, b, ds)> =[ match beval st be with
                       | true => c1
                       | false => c2 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Spec_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      <(st, ast, true, ds)> =[ match beval st be with
                       | true => c2 (* <-- branches swapped *)
                       | false => c1 end ]=> <(st', ast', b', os1)> ->
      <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Spec_While : forall be st ast b ds st' ast' b' os c,
      <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Spec_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < List.length (apply ast a) ->
      <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i (apply ast a) 0; st, ast, b, [OARead a i])>
  | Spec_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= List.length (apply ast a) ->
      i' < List.length (apply ast a') ->
      <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> nth i' (apply ast a') 0; st, ast, true, [OARead a i])>
  | Spec_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < List.length (apply ast a) ->
      <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (apply ast a) n; ast, b, [OAWrite a i])>
  | Spec_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= List.length (apply ast a) ->
      i' < List.length (apply ast a') ->
      <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (apply ast a') n; ast, true, [OAWrite a i])>

  where "<( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (spec_eval c st ast b ds stt astt bb os).

Module SpecCTInterpreter.

(* Interpreter for speculative constant time *)
Definition input_st : Type := state * astate * bool * dirs.
Inductive output_st (A : Type): Type :=
  | ROutOfFuel : output_st A
  | ROutOfBounds : output_st A
  | RInvalidDirection : output_st A
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
        | ROk _ value os1 ist'  => match evaluate B (f value) ist' with
            | ROk _ value os2 ist'' => ROk B value (os1 ++ os2) ist''
            | ret => ret
            end
        | ROutOfBounds _ => ROutOfBounds B
        | RInvalidDirection _ => RInvalidDirection B
        | ROutOfFuel _ => ROutOfFuel B
        end
      )
   }.

(* specialized operators *)
Definition finish : interpreter := ret tt.

Definition get_var (name : string): evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    evaluate _ (ret (apply st name)) ist
  ).
Definition get_arr (name : string): evaluator (list nat) :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, ast, _, _) := ist in
    evaluate _ (ret (apply ast name)) ist
  ).
Definition set_var (name : string) (value : nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, b, ds) := ist in
    let new_st := (name !-> value ; st) in
    evaluate _ finish (new_st, ast, b, ds)
  ).
Definition set_arr (name : string) (value : list nat) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, b, ds) := ist in
    let new_ast := (name !-> value ; ast) in
    evaluate _ finish (st, new_ast, b, ds)
  ).
Definition start_speculating : interpreter :=
  mkEvaluator _ (fun (ist : input_st) => 
    let '(st, ast, _, ds) := ist in
    evaluate _ finish (st, ast, true, ds)
  ).
Definition is_speculating : evaluator bool :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(_, _, b, _) := ist in
    evaluate _ (ret b) ist
  ).
Definition eval_aexp (a : aexp) : evaluator nat :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    let v := aeval st a in
    evaluate _ (ret v) ist
  ).
Definition eval_bexp (b : bexp) : evaluator bool :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, _, _, _) := ist in
    let v := beval st b in
    evaluate _ (ret v) ist
  ).
Definition raise_invalid_direction : interpreter :=
  mkEvaluator _ (fun _ =>
    RInvalidDirection _
  ).
Definition raise_out_of_bounds : interpreter :=
  mkEvaluator _ (fun _ =>
    ROutOfBounds _
  ).
Definition raise_out_of_fuel : interpreter :=
  mkEvaluator _ (fun _ =>
    ROutOfFuel _
  ).
Definition observe (o : observation) : interpreter :=
  mkEvaluator _ (fun (ist : input_st) =>
    ROk _ tt [o] ist
  ).
Definition fetch_direction : evaluator direction :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(st, ast, b, ds) := ist in
    match ds with
    | dir::ds' =>
        let new_ist := (st, ast, b, ds') in
        evaluate _ (ret dir) new_ist
    | [] => RInvalidDirection _
    end
  ).

Fixpoint spec_eval_engine_aux (f : nat) (c : com) : interpreter :=
  match f with
  | O => raise_out_of_fuel
  | S f =>

  match c with
  | <{ skip }> =>
      finish
  | <{ x := e }> =>
      v <- eval_aexp e;;
      set_var x v
  | <{ c1 ; c2 }> =>
      spec_eval_engine_aux f c1;;
      spec_eval_engine_aux f c2
  | <{ if b then ct else cf end }> =>
      condition <- eval_bexp b;;
      dir <- fetch_direction;;
      match dir with
      | DStep =>
          (* normal execution... *)
          (* TODO: why can't I just use 'if condition then ct else cf end'? *)
          let next_c := if Bool.eqb condition true then ct else cf in

          observe (OBranch condition);;
          spec_eval_engine_aux f next_c
      | DForce =>
          (* branches swapped! *)
          let next_c := if condition then cf else ct in

          start_speculating;;

          observe (OBranch condition);;
          spec_eval_engine_aux f next_c
      | _ => raise_invalid_direction
      end
  | <{ while be do c end }> =>
    spec_eval_engine_aux f <{
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
      b <- is_speculating;;
      dir <- fetch_direction;;
      match dir with
      | DStep =>
          if (i <? List.length l) then
            observe (OARead a i);;
            set_var x (nth i l 0)
          else if Bool.eqb b true then (* TODO: get rid of Bool.eqb *)
            (* If we're speculating, then DStep is an invalid direction *)
            raise_invalid_direction
          else
            (* If we're not speculating, then it's just a program error *)
            raise_out_of_bounds
      | DLoad a' i' =>
          l' <- get_arr a';;

          (* The normal read must be out of bounds *)
          if negb (i <? List.length l) &&
             (* The index the attacker provides must be in bound *)
             (i' <? List.length l') &&
             (* Only allowed when speculating *)
             b then
            observe (OARead a i);;
            set_var x (nth i' l' 0)
          else
            raise_invalid_direction
      | _ => raise_invalid_direction
      end
  | <{ a[ie] <- e }> =>
      n <- eval_aexp e;;
      i <- eval_aexp ie;;
      l <- get_arr a;;
      b <- is_speculating;;
      dir <- fetch_direction;;
      match dir with
      | DStep =>
          if (i <? List.length l) then
            observe (OAWrite a i);;
            set_arr a (upd i l n)
          else if Bool.eqb b true then (* TODO: get rid of Bool.eqb *)
            (* If we're speculating, then DStep is an invalid direction *)
            raise_invalid_direction
          else
            (* If we're not speculating, then it's just a program error *)
            raise_out_of_bounds
      | DStore a' i' =>
          l' <- get_arr a';;

          (* The normal read must be out of bounds *)
          if negb (i <? List.length l) &&
               (* The index the attacker provides must be in bound *)
               (i' <? List.length l') &&
               (* Only allowed when speculating *)
               b then
            observe (OAWrite a i);;
            set_arr a' (upd i' l' n)
          else
            raise_invalid_direction
        | _ => raise_invalid_direction
      end
  end
  end.

(* Having access to the program and the direction, we should be able to always guess
   the amount of gas needed. *)
Fixpoint program_size (c : com) : nat :=
  match c with
  | <{ if be then c1 else c2 end }> => S ((program_size c1) + (program_size c2))
  | <{ c1 ; c2 }> => S ((program_size c1) + (program_size c2))
  | <{ while be do c end }> => S (program_size c)
  | _ => 1
  end.
Definition compute_gas (c : com) (ds : dirs) : nat :=
  (S (Datatypes.length ds)) * (program_size c).

Theorem cannot_run_out_of_fuel :
  forall c st ast b ds f,
    f >= (compute_gas c ds) -> evaluate _ (spec_eval_engine_aux f c) (st, ast, b, ds) <> ROutOfFuel unit.
Proof.
Admitted.

End SpecCTInterpreter.

Definition spec_eval_engine (c : com) (st : state) (ast : astate) (b : bool) (ds : dirs) : option (state * astate * bool * obs) :=
  let ist := (st, ast, b, ds) in
  match SpecCTInterpreter.evaluate _ (SpecCTInterpreter.spec_eval_engine_aux (SpecCTInterpreter.compute_gas c ds) c) ist with
  | SpecCTInterpreter.ROk _ _ obs ist => let '(st, ast, b, _) := ist in
      Some (st, ast, b, obs)
  | _ => None
  end.
(* In addition, checks that we provided exactly enough directions *)
Definition spec_eval_engine_strict (c : com) (st : state) (ast : astate) (b : bool) (ds : dirs) : option (state * astate * bool * obs) :=
  let ist := (st, ast, b, ds) in
  match SpecCTInterpreter.evaluate _ (SpecCTInterpreter.spec_eval_engine_aux (SpecCTInterpreter.compute_gas c ds) c) ist with
  | SpecCTInterpreter.ROk _ _ obs ist => let '(ct, ast, b, ds) := ist in
      match ds with
      | [] => Some (st, ast, b, obs)
      | _ => None
      end
  | _ => None
  end.

(* Simple tests *)
Eval compute in
  (spec_eval_engine <{
      skip
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false []).
Eval compute in
  (spec_eval_engine <{
      X := 10
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false []).
Eval compute in
  (spec_eval_engine <{
      X := 10;
      Y := 3
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false []).
Eval compute in
  (spec_eval_engine <{
      if true then X := 15
      else X := 13
      end
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false [DStep]).
Eval compute in
  (spec_eval_engine <{
      if true then
        if false then skip
        else skip
        end
      else skip
      end
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false [DStep; DStep]).
Eval compute in
  (spec_eval_engine <{
      if true then X := 15
      else X := 13
      end
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false [DForce]).
Eval compute in
  (spec_eval_engine <{
      while false do X := X + 1 end
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (_ !-> []) false [DForce; DStep]).
Eval compute in
  (spec_eval_engine <{
      while Y > 0 do
        X := X + 1;
        Y := Y - 1
      end
    }> (X !-> 0 ; Y !-> 2; _ !-> 0) (_ !-> []) false [DStep; DStep; DStep]).
Eval compute in
  (spec_eval_engine <{
      while Y > 0 do
        X := X + 1;
        Y := Y - 1
      end
    }> (X !-> 0 ; Y !-> 2; _ !-> 0) (_ !-> []) true [DStep; DForce]).
Eval compute in
  (spec_eval_engine <{
      X <- A [[1]]
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) false [DStep]).
Eval compute in
  (spec_eval_engine <{
      X <- A [[1]]
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) true [DStep]).
Eval compute in
  (spec_eval_engine <{
      X <- A [[1]]
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) true [DLoad A 0]).
Eval compute in
  (spec_eval_engine <{
      X <- A [[5]]
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) true [DLoad A 0]).
Eval compute in
  (spec_eval_engine <{
      A [0] <- 10
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) false [DStep]).
Eval compute in
  (spec_eval_engine <{
      A [5] <- 100
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; _ !-> []) false [DStep]).
Eval compute in
  (spec_eval_engine <{
      A [5] <- 100
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; B !-> [1] ; _ !-> []) false [DStore B 0]).
Eval compute in
  (spec_eval_engine <{
      A [5] <- 100
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; B !-> [] ; _ !-> []) true [DStore B 0]).
Eval compute in
  (spec_eval_engine <{
      A [5] <- 100
    }> (X !-> 0 ; Y !-> 1; _ !-> 0) (A !-> [8;7;9] ; B !-> [1] ; _ !-> []) true [DStore B 0]).

(** Testing that the interpreter is correct *)
(* n < m. Reimplementing it since 'lt n m' is actually 'le (S n) m',
   and poor QuickChick can't deal with 'S n'. *)
Definition gen_nat_lt (m : nat) : G (option nat) :=
  match m with
  | 0 => returnGen None
  | S m =>
      n <- choose (0, m);;
      returnGen (Some n)
  end.

Definition gen_arr_not_nil (ast : astate) : G (option arr_id) :=
  let '(d, m) := ast in
  let arr_not_empty : list string := List.filter (fun a =>
    match apply ast a with
    | [] => false
    | _ => true
    end) (map_dom m) in

  match d with
  | [] => elems_ None (List.map (fun (x : string) => Some (Arr x)) arr_not_empty)
  | _ =>
      let not_empty_as_default : list string := List.filter (fun a =>
        negb (List.existsb (fun x => String.eqb x a) (map_dom m))
      ) ["A0"; "A1"; "A2"] % string in
      elems_ None (List.map (fun x => Some (Arr x)) (arr_not_empty ++ not_empty_as_default))
  end.

(* Returns (ds, st', ast', b', os) such that <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> *)
Fixpoint gen_spec_eval_sized (c : com) (st : state) (ast : astate) (b : bool) (size : nat): G (option (dirs * state * astate * bool * obs)) :=
  match c with
  | <{ skip }> =>
    let ds := [] in
    let st' := st in
    let ast' := ast in
    let b' := b in
    let os := [] in
    returnGen (Some (ds, st', ast', b', os))
  | <{ x := e }> =>
    let n := aeval st e in

    let ds := [] in
    let st' := (x !-> n; st) in
    let ast' := ast in
    let b' := b in
    let os := [] in
    returnGen (Some (ds, st', ast', b', os))
  | <{ x <- a[[ie]] }> =>
    let i := aeval st ie in

    if i <? List.length (apply ast a)
    then
      let ds := [DStep] in
      let st' := (x !-> nth i (apply ast a) 0; st) in
      let ast' := ast in
      let b' := b in
      let os := [OARead a i] in
      returnGen (Some (ds, st', ast', b', os))
    else (* i >= List.length (apply ast a) *)
    if b then
      bindOpt (gen_arr_not_nil ast) (fun a' => (* prioritize generating a non-empty array *)
      bindOpt (gen_nat_lt (List.length (apply ast a'))) (fun i' =>

      let ds := [DLoad a' i'] in
      let st' := (x !-> nth i' (apply ast a') 0; st) in
      let ast' := ast in
      let b' := true in
      let os := [OARead a i] in
      returnGen (Some (ds, st', ast', b', os))
      ))
    else returnGen None
  | <{ a[ie] <- e }> =>
    let i := aeval st ie in
    let n := aeval st e in

    if i <? List.length (apply ast a)
    then
      let ds := [DStep] in
      let st' := st in
      let ast' := (a !-> upd i (apply ast a) n; ast) in
      let b' := b in
      let os := [OAWrite a i] in
      returnGen (Some (ds, st', ast', b', os))
    else (* i >= List.length (apply ast a) *)
    if b then
      bindOpt (gen_arr_not_nil ast) (fun a' => (* prioritize generating a non-empty array *)
      bindOpt (gen_nat_lt (List.length (apply ast a'))) (fun i' =>

      let ds := [DStore a' i'] in
      let st' := st in
      let ast' := (a' !-> upd i' (apply ast a') n; ast) in
      let b' := true in
      let os := [OAWrite a i] in
      returnGen (Some (ds, st', ast', b', os))
      ))
    else returnGen None
  | _ =>
    match size with
    | O => returnGen None
    | S size =>
        match c with
        | <{ c1 ; c2 }> =>
            bindOpt (gen_spec_eval_sized c1 st ast b size) (fun '(ds1, st', ast', b', os1) =>
            bindOpt (gen_spec_eval_sized c2 st' ast' b' size) (fun '(ds2, st'', ast'', b'', os2) =>
            returnGen (Some (ds1 ++ ds2, st'', ast'', b'', os1 ++ os2))
            ))
        | <{ if be then c1 else c2 end }> =>
            dir <- elems [DStep; DForce];;

            match dir with
            | DStep =>
                let condition := beval st be in
                let next_c := if condition then c1 else c2 in
                bindOpt (gen_spec_eval_sized next_c st ast b size) (fun '(ds, st', ast', b', os) =>
                returnGen (Some (DStep::ds, st', ast', b', (OBranch condition)::os))
                )
            | DForce =>
                let condition := beval st be in
                let next_c := if condition then c2 else c1 in
                bindOpt (gen_spec_eval_sized next_c st ast true size) (fun '(ds, st', ast', b', os) =>
                returnGen (Some (DForce::ds, st', ast', b', (OBranch condition)::os))
                )
            | _ => returnGen None
            end
        | <{ while be do c end }> =>
            gen_spec_eval_sized <{ if be then c; while be do c end else skip end }> st ast b size
        | _ => returnGen None
        end
    end
  end.

Definition total_map_beq (a:Type) (a_beq:a->a->bool) (m1 m2 : total_map a) :=
  match m1, m2 with
  | (d1,lm1), (d2,lm2) => a_beq d1 d2 &&
      forallb (fun x => a_beq (apply m1 x) (apply m2 x))
              (union (map_dom lm1) (map_dom lm2))
  end.

Definition state_eqb := total_map_beq nat Nat.eqb.
Definition astate_eqb := total_map_beq (list nat) (fun l1 l2 =>
    forallb (fun '(i1, i2) => Nat.eqb i1 i2) (List.combine l1 l2)
  ).

#[export] Instance showdirection : Show direction :=
  {show := (fun dir =>
      match dir with
      | DStep => "step"
      | DForce => "force"
      | DLoad a i => "load " ++ a ++ " " ++ (show i)
      | DStore a i => "store " ++ a ++ " " ++ (show i)
      end % string)
   }.
#[export] Instance showobservation : Show observation :=
  {show := (fun o =>
      match o with
      | OBranch b => "branch " ++ (show b)
      | OARead a i => "aread " ++ a ++ " " ++ (show i)
      | OAWrite a i => "awrite " ++ a ++ " " ++ (show i)
      end % string)
   }.

QuickChick (forAll (arbitrarySized 2) (fun c =>
    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>
    forAll arbitrary (fun b =>
    forAllMaybe (gen_spec_eval_sized c st ast b 3) (fun '(ds, st', ast', b', os) =>
      printTestCase ((show ds) ++ nl) (
      match spec_eval_engine c st ast b ds with
      | Some (st_, ast_, b_, os_) =>
          (state_eqb st' st_) &&
          (astate_eqb ast' ast_) &&
          (Bool.eqb b_ b') &&
          obs_eqb os os_
      | None => false
      end)
  )))))).

(* HIDE: This semantics already lost one property of Imp, which is only
   nonterminating executions don't produce a final state. Now if the input
   directions don't match what the program expects we also get stuck, which for
   our big-step semantics can't be distinguished from nontermination. This is
   probably not a problem, but just wanted to mention it. *)

(** HIDE: Without fences the speculation bit [b] is just a form of instrumentation
    that doesn't affect the semantics, except adding more stuckness for the [_U] rules. *)

(* LATER: Could also add fences, but they are not needed for SLH. They would add
   a bit of complexity to the big-step semantics, since they behave like a halt
   instruction that prematurely ends execution, which means adding at least one
   more rule for sequencing (basically an error monad, but with a (halt) bit of
   cleverness we can probably avoid extra rules for if and while, since we're
   just threading through things). We likely don't want to treat this stuckness
   as not producing a final state though, since a stuck fence should be final
   state in their small-step semantics (actually they messed that up,
   see next point). *)

(* LATER: Could prove this semantics equivalent to the small-step one from the
   two IEEE SP 2023 papers. The fact that their rule [Seq-Skip] requires a step
   seems wrong if first command in the sequence is already skip. Also the way
   they define final results seem wrong for stuck fences, and that would either
   need to be fixed to include stuck fences deep inside or to bubble up stuck
   fences to the top (error monad, see prev point). *)

(* HIDE: Other fixes we did are to their ideal semantics where in (Ideal_ARead)
   we are allowing mis-speculated in-bound reads and where we removed
   (Ideal_ARead_Prot), by merging it with the other two rules and producing the
   correct direction and removed harmful preconditions in both cases. *)

(* HIDE: One design decision here is to neither consume DSteps not to generate
   dummy observations for skip and (register) assignment commands. This leads to
   simpler proofs (e.g. no need for erasure) and it also seems sensible: it's
   not like a skip takes the same time as an assignment anyway, so making these
   things observable with the same dummy event seems anyway questionable! *)

(* LATER: Could add the declassify construct from Spectre Declassified, but for
   now trying to keep things simple. If we add that then the RNI notion of
   Definition 2 relies on the small-step semantics to stop at the first force
   directive. Doing that with a big-step semantics seems trickier. We could
   build a version that halts early on the first force? *)

(* Let's find example programs that satisfy the cryptographic constant-time
   discipline ([ct_well_typed]), but that are insecure wrt the speculative
   semantics above.  For instance, one can write secrets to public arrays using
   Spec_Write_U, and one can read to public registers from secret Spec_ARead_U.
   Could look both into simple examples exploiting the semantics, and also into
   more realistic examples that one can also exploit in practice.

   b - secret array of size n >= 1
   a - public array of size n >= 1
   p - public variable

   Realistic example:
   i := 0;
   while i < n do
     p := p + a[i];
     i := i + 1;
   end

   Simple but not so realistic example
   (safe+secure without speculation, but unsafe+insecure with speculation):
   if false then p := a[n] else skip
*)

Definition forAllShrinkNonDet {A prop : Type} {_ : Checkable prop} `{Show A}
           (n : nat) (gen : G A) (shrinker : A -> list A) (pf : A -> prop) : Checker :=
  let repeated_shrinker (x : A) : list A :=
    List.concat (List.repeat (shrinker x) n) in
  bindGen gen (fun x : A =>
                 shrinking repeated_shrinker x (fun x' =>
                                         printTestCase (show x' ++ newline) (pf x'))).

(* TODO: 100 isn't enough, but increasing it leads to too many performance problems.
         forAllShrinkNonDet needs to be changed to be more efficient. *)
QuickChick (forAllShrinkNonDet 100 gen_pub_vars shrink (fun P =>
    forAllShrinkNonDet 100 gen_pub_arrs shrink (fun PA =>
    forAllShrinkNonDet 100 (gen_ct_well_typed_sized P PA 3) (shrink_ct_well_typed P PA) (fun c =>

    forAll arbitrary (fun b =>

    forAllShrinkNonDet 100 gen_state shrink (fun s1 =>
    forAllShrinkNonDet 100 (gen_pub_equiv P s1) (shrink_pub_equiv_state P s1) (fun s2 =>
    forAllShrinkNonDet 100 gen_astate shrink (fun a1 =>
    forAllShrinkNonDet 100 (gen_pub_equiv PA a1) (shrink_pub_equiv_astate P a1) (fun a2 =>

    forAllMaybe (gen_spec_eval_sized c s1 a1 b 3) (fun '(ds, s1', a1', b1', os1) =>
      match spec_eval_engine c s2 a2 b ds with
      | Some (s2', a2', b2', os2') =>
          (pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2')
      | _ => false
      end
  )))))))))).

(* Typical example found:
     c = A0[X0] <- 4
     non-speculative execution.
     st1 = ( "X0" !-> 1 ; _ !-> 0) ; ast1 = ( _ !-> [0; 0])
     st2 = ( "X0" !-> 1 ; _ !-> 0) ; ast2 = ( _ !-> [])
     ds = [DStep]

  The second execution crashed since A0[X0] is out of bounds. It's not very interesting as
  seeing this is the result of adding finite-length arrays to the model, not speculative execution.

  To fix this, we'll enforce that both execution successfuly terminate.
   *)

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>
    forAll (gen_ct_well_typed_sized P PA 3) (fun c =>

    forAll arbitrary (fun b =>

    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv PA a1) (fun a2 =>

    forAllMaybe (gen_spec_eval_sized c s1 a1 b 3) (fun '(ds, s1', a1', b1', os1) =>
      match spec_eval_engine c s2 a2 b ds with
      | Some (s2', a2', b2', os2') =>
          (pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2')
      | _ => true (* <---- changed! *)
      end
  )))))))))).

(* Second type of counterexamples found:
      c = A2[2] <- X1
    st1 = (X1 !-> 0) ; ast1 (A0 !-> [0])
    st2 = (X1 !-> 3) ; ast2 (A0 !-> [0])
    speculative execution. A2 secret ; X1 secret ; A0 public
    ds = [DStore A0 0]

    -> in the output of the first execution,  A0 = [0]
       in the output of the second execution, A0 = [3]
    That's a real example, cool !

    But it requires us to be initially speculating.
    Let's try to force it to find something that's initially not speculating.
  *)

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>

    forAll (gen_ct_well_typed_sized P PA 2) (fun c =>

    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv PA a1) (fun a2 =>

    let b := false in (* <---- changed ! *)

    forAllMaybe (gen_spec_eval_sized c s1 a1 b 1000) (fun '(ds, s1', a1', b1', os1) =>
      match spec_eval_engine c s2 a2 b ds with
      | Some (s2', a2', b2', os2') =>
          (pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2')
      | _ => true (* <---- changed! *)
      end
    )
  )))))))).

(* CH: This one works on my machine
QuickChick (forAllShrinkNonDet 200 gen_pub_vars shrink (fun P =>
    forAllShrinkNonDet 200 gen_pub_arrs shrink (fun PA =>
    forAllShrinkNonDet 200 (gen_ct_well_typed_sized P PA 3) (shrink_ct_well_typed P PA) (fun c =>

    forAllShrinkNonDet 200 gen_state shrink (fun s1 =>
    forAllShrinkNonDet 200 (gen_pub_equiv P s1) (shrink_pub_equiv_state P s1) (fun s2 =>
    forAllShrinkNonDet 200 gen_astate shrink (fun a1 =>
    forAllShrinkNonDet 200 (gen_pub_equiv PA a1) (shrink_pub_equiv_astate P a1) (fun a2 =>

    let b := false in (* <---- changed ! *)

    forAllMaybe (gen_spec_eval_sized c s1 a1 b 3) (fun '(ds, s1', a1', b1', os1) =>
      match spec_eval_engine c s2 a2 b ds with
      | Some (s2', a2', b2', os2') =>
          (pub_equivb P s1' s2') && (pub_equivb_astate PA a1' a2')
      | _ => true
      end
  ))))))))).
*)

(* Now, it finds counterexamples such as:
    c = A2[2] <- X1
    st1 = (X1 !-> 0) ; ast1 (A0 !-> [0])
    st2 = (X1 !-> 3) ; ast2 (A0 !-> [0])
    speculative execution. A2 secret ; X1 secret ; A0 public
    ds = [DForce; DStore A0 0]

    Cool!
  *)

(* HIDE: Just to warm up formalized the first lemma in the Spectre Declassified
   paper: Lemma 1: structural properties of execution *)

Lemma speculation_bit_monotonic : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = true ->
  b' = true.
Proof. intros c s a b ds s' a' b' os Heval Hb. induction Heval; eauto. Qed.

QuickChick (forAll (arbitrarySized 3) (fun c =>
    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>
    forAllMaybe (gen_spec_eval_sized c st ast true 100) (fun '(ds, st', ast', b', os) =>
      b'
  ))))).

(* HIDE: This one is weaker for big-step semantics, but it's still helpful below *)
Lemma speculation_needs_force : forall c s a b ds s' a' b' os,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Definition direction_eqb (d1 : direction) (d2 : direction) : bool :=
  match d1, d2 with
  | DStep, DStep => true
  | DForce, DForce => true
  | DLoad a i, DLoad a' i' => (String.eqb a a') && (i =? i')
  | DStore a i, DStore a' i' => (String.eqb a a') && (i =? i')
  | _, _ => false
  end.

(* TODO: Way too many discards to be able to test this. *)
QuickChick (forAll (arbitrarySized 3) (fun c =>
    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>
    forAllMaybe (gen_spec_eval_sized c st ast false 100) (fun '(ds, st', ast', b', os) =>
      implication b' (
        existsb (fun dir => direction_eqb dir DForce) ds
      )
  ))))).

(* HIDE: Also this one is weaker for big-step semantics *)
Lemma unsafe_access_needs_speculation : forall c s a b ds s' a' b' os ax i,
  <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  In (DLoad ax i) ds \/ In (DStore ax i) ds ->
  b = true \/ In DForce ds.
Proof.
  intros c s a b ds s' a' b' os ax i Heval Hin.
  induction Heval; simpl in *; try tauto; try (firstorder; discriminate).
  - destruct Hin as [Hin | Hin].
    + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_introl _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_introl _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          (* slightly more interesting case, the rest very boring *)
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
    + (* very symmetric, mostly copy paste *)
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * specialize (IHHeval1 (or_intror _ Hin)). destruct IHHeval1; try tauto.
        right. apply in_or_app. tauto.
      * specialize (IHHeval2 (or_intror _ Hin)). destruct IHHeval2; try tauto.
        { destruct b eqn:Eq; try tauto.
          right. apply speculation_needs_force in Heval1; [| reflexivity|assumption].
          apply in_or_app. tauto. }
        { right. apply in_or_app. tauto. }
Qed.

(* TODO: Way too many discards to test this. *)
QuickChick (forAll arbitrary (fun c =>
    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>
    forAll arbitrary (fun b =>
    forAllMaybe (gen_spec_eval_sized c st ast b 5) (fun '(ds, st', ast', b', os) =>
      implication
        ((existsb (fun dir => match dir with DLoad _ _ => true | _ => false end) ds) ||
         (existsb (fun dir => match dir with DStore _ _ => true | _ => false end) ds))
        ((existsb (fun dir => direction_eqb dir DForce) ds) || b)
  )))))).

(** We can recover sequential execution from [spec_eval] if there is no
    speculation, so all directives are [DStep] and speculation flag starts [false]. *)

Definition seq_spec_eval (c:com) (s:state) (a:astate)
    (s':state) (a':astate) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    <(s, a, false, ds)> =[ c ]=> <(s', a', false, os)>.

(* Way too many discards to test this *)
QuickChick (forAll (arbitrarySized 3) (fun c =>
    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>
    forAllMaybe (gen_spec_eval_sized c st ast false 100) (fun '(ds, st', ast', b', os) =>
      let contains_only_steps := List.forallb (fun x => direction_eqb x DStep) ds in
      implication contains_only_steps (negb b')
  ))))).

(* LATER: We should be able to prove that [cteval] and [seq_spec_eval] coincide, so
   by [ct_well_typed_ct_secure] also directly get their Lemma 2. *)

(** ** Speculative constant-time security definition *)

Definition spec_ct_secure :=
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds,
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    <(s1, a1, false, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    <(s2, a2, false, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.

(** Selective SLH transformation that we will show enforces speculative
    constant-time security. *)

Fixpoint sel_slh (P:pub_vars) (c:com) :=
  (match c with
  | <{{skip}}> => <{{skip}}>
  | <{{x := e}}> => <{{x := e}}>
  | <{{c1; c2}}> => <{{ sel_slh P c1; sel_slh P c2}}>
  | <{{if be then c1 else c2 end}}> =>
      <{{if be then "b" := (be ? "b" : 1); sel_slh P c1
               else "b" := (be ? 1 : "b"); sel_slh P c2 end}}>
  | <{{while be do c end}}> =>
      <{{while be do "b" := (be ? "b" : 1); sel_slh P c end;
         "b" := (be ? 1 : "b")}}>
  | <{{x <- a[[i]]}}> =>
      if apply P x then <{{x <- a[[i]]; x := ("b" = 1) ? 0 : x}}>
                   else <{{x <- a[[i]]}}>
  | <{{a[i] <- e}}> => <{{a[i] <- e}}>
  end)%string.

(** To prove this transformation secure, Spectre Declassified uses an idealized semantics *)

Reserved Notation
         "P '|-' '<(' st , ast , b , ds ')>' '=[' c ']=>' '<(' stt , astt , bb , os ')>'"
         (at level 40, c custom com at level 99,
          st constr, ast constr, stt constr, astt constr at next level).

Inductive ideal_eval (P:pub_vars) :
    com -> state -> astate -> bool -> dirs ->
           state -> astate -> bool -> obs -> Prop :=
  | Ideal_Skip : forall st ast b,
      P |- <(st, ast, b, [])> =[ skip ]=> <(st, ast, b, [])>
  | Ideal_Asgn  : forall st ast b e n x,
      aeval st e = n ->
      P |- <(st, ast, b, [])> =[ x := e ]=> <(x !-> n; st, ast, b, [])>
  | Ideal_Seq : forall c1 c2 st ast b st' ast' b' st'' ast'' b'' os1 os2 ds1 ds2,
      P |- <(st, ast, b, ds1)> =[ c1 ]=> <(st', ast', b', os1)>  ->
      P |- <(st', ast', b', ds2)> =[ c2 ]=> <(st'', ast'', b'', os2)> ->
      P |- <(st, ast, b, ds1++ds2)>  =[ c1 ; c2 ]=> <(st'', ast'', b'', os1++os2)>
  | Ideal_If : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, b, ds)> =[ match beval st be with
                                 | true => c1
                                 | false => c2 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DStep :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Ideal_If_F : forall st ast b st' ast' b' be c1 c2 os1 ds,
      P |- <(st, ast, true, ds)> =[ match beval st be with
                                    | true => c2 (* <-- branches swapped *)
                                    | false => c1 end ]=> <(st', ast', b', os1)> ->
      P |- <(st, ast, b, DForce :: ds)> =[ if be then c1 else c2 end ]=>
        <(st', ast', b', OBranch (beval st be)::os1)>
  | Ideal_While : forall be st ast b ds st' ast' b' os c,
      P |- <(st, ast, b, ds)> =[ if be then c; while be do c end else skip end ]=>
        <(st', ast', b', os)> ->
      P |- <(st, ast, b, ds)> =[ while be do c end ]=> <(st', ast', b', os)>
  | Ideal_ARead : forall st ast b x a ie i,
      aeval st ie = i ->
      i < Datatypes.length (apply ast a) ->
      P |- <(st, ast, b, [DStep])> =[ x <- a[[ie]] ]=>
        <(x !-> if b && apply P x then 0 else nth i (apply ast a) 0; st, ast, b, [OARead a i])>
  | Ideal_ARead_U : forall st ast x a ie i a' i',
      aeval st ie = i ->
      i >= Datatypes.length (apply ast a) ->
      i' < Datatypes.length (apply ast a') ->
      P |- <(st, ast, true, [DLoad a' i'])> =[ x <- a[[ie]] ]=>
        <(x !-> if apply P x then 0 else nth i' (apply ast a') 0; st, ast, true, [OARead a i])>
  | Ideal_Write : forall st ast b a ie i e n,
      aeval st e = n ->
      aeval st ie = i ->
      i < Datatypes.length (apply ast a) ->
      P |- <(st, ast, b, [DStep])> =[ a[ie] <- e ]=>
        <(st, a !-> upd i (apply ast a) n; ast, b, [OAWrite a i])>
  | Ideal_Write_U : forall st ast a ie i e n a' i',
      aeval st e = n ->
      aeval st ie = i ->
      i >= Datatypes.length (apply ast a) ->
      i' < Datatypes.length (apply ast a') ->
      P |- <(st, ast, true, [DStore a' i'])> =[ a[ie] <- e ]=>
        <(st, a' !-> upd i' (apply ast a') n; ast, true, [OAWrite a i])>

  where "P |- <( st , ast , b , ds )> =[ c ]=> <( stt , astt , bb , os )>" :=
    (ideal_eval P c st ast b ds stt astt bb os).

(* We show that on sequential executions this is equivalent to [seq_spec_eval] *)

Lemma seq_eval_ideal_eval_ind1 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof.
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Ideal_Seq.
    * apply IHspec_eval1; eauto using in_or_app.
    * apply IHspec_eval2; eauto using in_or_app.
  - simpl in Hds; eauto.
  - simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - admit. (* TODO: the proof is slightly broken because of the introduction of apply, fix it *)
Admitted.

Lemma speculation_needs_force_ideal : forall P c s a b ds s' a' b' os,
  P |- <(s, a, b, ds)> =[ c ]=> <(s', a', b', os)> ->
  b = false ->
  b' = true ->
  In DForce ds.
Proof.
  intros P c s a b ds s' a' b' os Heval Hb Hb'.
  induction Heval; subst; simpl; eauto; try discriminate.
  apply in_or_app. destruct b'; eauto.
Qed.

Lemma seq_eval_ideal_eval_ind2 : forall P c s a b ds s' a' b' os,
  (forall d : direction, In d ds -> d = DStep) ->
  P |- <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )> ->
  b = false ->
  b' = false ->
  <( s, a, b, ds )> =[ c ]=> <( s', a', b', os )>.
Proof. (* proof really the same as gen1 *)
  intros P c s a b ds s' a' b' os Hds H Eb Eb'.
  induction H; try constructor; eauto.
  - assert(b' = false).
    { destruct b' eqn:Eqb'; [| reflexivity].
      apply speculation_needs_force_ideal in H; try tauto.
      assert (contra : DForce = DStep).
      { apply Hds. apply in_or_app. left. assumption. }
      inversion contra. }
    eapply Spec_Seq.
    * apply IHideal_eval1; eauto using in_or_app.
    * apply IHideal_eval2; eauto using in_or_app.
  - simpl in Hds; eauto.
  - simpl in Hds.
    assert (contra : DForce = DStep). { apply Hds. left. reflexivity. }
    inversion contra.
  - admit. (* TODO: the proof is slightly broken because of the introduction of apply, fix it *)
Admitted.

(* HIDE: This is Lemma 3 from Spectre Declassified *)

Definition seq_ideal_eval (P:pub_vars) (c:com) (s:state) (a:astate)
    (s':state) (a':astate) (os:obs) : Prop :=
  exists ds, (forall d, In d ds -> d = DStep) /\
    P |- <(s, a, false, ds)> =[ c ]=> <(s', a', false, os)>.

Lemma seq_spec_eval_ideal_eval : forall P c s a s' a' os,
  seq_spec_eval c s a s' a' os <->
  seq_ideal_eval P c s a s' a' os.
Proof.
  intros P c s a s' a' os. unfold seq_spec_eval, seq_ideal_eval.
  split; intros [ds [Hds H] ]; exists ds; (split; [ apply Hds |]).
  - apply seq_eval_ideal_eval_ind1; eauto.
  - eapply seq_eval_ideal_eval_ind2; eauto.
Qed.

(** Let's now prove that the idealized semantics does enforce speculative constant-time *)

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, xs ++ zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof. 
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) ->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3 H.
  - auto.
  - simpl in H; apply prefix_cons in H. apply IH in H. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  ds1 ++ ds2 = ds1' ++ ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof. 
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

Ltac split4 := split; [|split; [| split] ].

Lemma pub_equiv_update_public : forall P {A:Type} (t1 t2 : total_map A) (X :string) (a1 a2 :A),
  pub_equiv P t1 t2 ->
  apply P X = public ->
  a1 = a2 ->
  pub_equiv P (X!-> a1; t1) (X!-> a2; t2).
Proof.
  intros P A t1 t2 X a1 a2 Hequiv Hpub Ha1a2 x Hx.
  destruct (String.eqb_spec X x) as [Heq | Hneq].
  - subst. admit. (* do 2 rewrite t_update_eq. reflexivity.*)
    (* TODO: fix the proof *)
  - admit. (* do 2 (rewrite t_update_neq;[| auto]). eapply Hequiv; eauto. *)
    (* TODO: fix the proof *)
Admitted. 

Lemma pub_equiv_update_secret : forall P {A:Type} (t1 t2 : total_map A) (X :string) (a1 a2 :A),
  pub_equiv P t1 t2 ->
  apply P X = secret ->
  pub_equiv P (X!-> a1; t1) (X!-> a2; t2).
Proof.
  intros P A t1 t2 X a1 a2 Hequiv Hsec x Hx.
  destruct (String.eqb_spec X x) as [Heq | Hneq].
  - subst. rewrite Hsec in Hx. discriminate.
  - admit. (* do 2 (rewrite t_update_neq;[| auto]). eapply Hequiv; eauto. *)
    (* TODO: fix the proof *)
Admitted.

Lemma ct_well_typed_ideal_noninterferent_general :
  forall P PA c st1 st2 ast1 ast2 b st1' st2' ast1' ast2' b1' b2' os1 os2 ds1 ds2,
    P !! PA |-ct- c ->
    pub_equiv P st1 st2 ->
    (b = false -> pub_equiv PA ast1 ast2) ->
    (prefix ds1 ds2 \/ prefix ds2 ds1) -> (* <- interesting generalization *)
    P |- <(st1, ast1, b, ds1)> =[ c ]=> <(st1', ast1', b1', os1)> ->
    P |- <(st2, ast2, b, ds2)> =[ c ]=> <(st2', ast2', b2', os2)> ->
    pub_equiv P st1' st2' /\ b1' = b2' /\
      (b1' = false -> pub_equiv PA ast1' ast2') /\
      ds1 = ds2.  (* <- interesting generalization *)
Proof.
  (* TODO: fix the proof *)
(*
  intros P PA c st1 st2 ast1 ast2 b st1' st2' ast1' ast2' b1' b2' os1 os2 ds1 ds2
    Hwt Heq Haeq Hds Heval1 Heval2.
  generalize dependent st2'. generalize dependent st2.
  generalize dependent ast2'. generalize dependent ast2.
  generalize dependent os2. generalize dependent b2'.
  generalize dependent ds2.
  induction Heval1; intros ds2X Hds b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - (* Skip *) auto.
  - (* Asgn *) split4; auto.
    destruct (P x) eqn:EqPx.
    + eapply pub_equiv_update_public; eauto. 
      eapply noninterferent_aexp; eauto. 
      destruct l; [auto | simpl in H14; discriminate].
    + eapply pub_equiv_update_secret; eauto. 
  - (* Seq *) 
    assert (Hds1: prefix ds1 ds0 \/ prefix ds0 ds1).
    { destruct Hds as [Hds | Hds]; apply prefix_app in Hds; tauto. }
    assert (ds1 = ds0). 
    { eapply IHHeval1_1; eassumption. } subst.
    assert (Hds2: prefix ds2 ds3 \/ prefix ds3 ds2).
    { destruct Hds as [Hds | Hds]; apply prefix_append_front in Hds; tauto. }
    (* SOONER: proofs above and below can be better integrated *)
    specialize (IHHeval1_1 H13 _ Hds1 _ _ _ Haeq _ _ Heq _ H1).
    destruct IHHeval1_1 as [ IH12eq [IH12b [IH12eqa _] ] ]. subst.
    specialize (IHHeval1_2 H14 _ Hds2 _ _ _ IH12eqa _ _ IH12eq _ H10).
    firstorder; subst; reflexivity.
  - (* If *)
    assert(G : P !! PA |-ct- (if beval st be then c1 else c2)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + specialize (IHHeval1 G _ Gds _ _ _ Haeq _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* IF; contra *) 
    apply prefix_or_heads in Hds; inversion Hds.
  - (* IF; contra *)
     apply prefix_or_heads in Hds; inversion Hds.
  - (* If_F; analog to If *)
    assert(G : P !! PA |-ct- (if beval st be then c2 else c1)).
    { destruct (beval st be); assumption. }
    assert(Gds : prefix ds ds0 \/ prefix ds0 ds).
    { destruct Hds as [Hds | Hds]; apply prefix_cons in Hds; tauto. }
    erewrite noninterferent_bexp in H10.
    + assert(GG: true = false -> pub_equiv PA ast a2). (* <- only difference *)
      { intro Hc. discriminate. }
      specialize (IHHeval1 G _ Gds _ _ _ GG _ _ Heq _ H10).
      firstorder; congruence.
    + apply pub_equiv_sym. eassumption.
    + eassumption.
  - (* While *) eapply IHHeval1; try eassumption. repeat constructor; eassumption.
  - (* ARead *) split4; eauto.
    destruct (P x) eqn:EqPx.
    + eapply pub_equiv_update_public; eauto.
      eapply noninterferent_aexp in Heq; eauto. rewrite Heq.
      unfold can_flow in H17; eapply orb_true_iff in H17.
      destruct H17 as [Ha | Contra]; [| simpl in Contra; discriminate].
      apply Haeq in Ha; [| reflexivity]. rewrite Ha. reflexivity.
    + eapply pub_equiv_update_secret; eauto.
  - (* ARead_U *) split4; eauto.
    + destruct (P x) eqn:EqPx.
      * discriminate H6.
      * eapply pub_equiv_update_secret; eauto.  
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
  - (* ARead contra *) rewrite H in *. discriminate.
  - (* Aread contra *) rewrite H in *. discriminate.
  - (* ARead_Prot *) split4; eauto.
    + destruct (P x) eqn:EqPx.
      * eapply pub_equiv_update_public; eauto.
      * discriminate H6.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity. 
  - (* Write *) split4; eauto. intro Hb2'.
    destruct (PA a) eqn:EqPAa.
    + eapply pub_equiv_update_public; eauto.
      destruct l eqn:Eql.
      * eapply noninterferent_aexp in H19, H20; eauto. rewrite H19, H20.
        apply Haeq in Hb2'. apply Hb2' in EqPAa. rewrite EqPAa. reflexivity.
      * simpl in H21. discriminate.  
    + eapply pub_equiv_update_secret; eauto.
  - (* Write contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* Write contra *) apply prefix_or_heads in Hds. inversion Hds.
  - (* Write_U contra *) split4; eauto.
    + intro contra. discriminate contra.
    + apply prefix_or_heads in Hds. inversion Hds. reflexivity.
Qed.*)
Admitted.

Lemma ct_well_typed_ideal_noninterferent :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P !! PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    pub_equiv P s1' s2' /\ b1' = b2' /\ (b1' = false -> pub_equiv PA a1' a2').
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  eapply ct_well_typed_ideal_noninterferent_general in Heval2; eauto; try tauto.
  left. apply prefix_refl.
Qed.

(** This corollary (used below) also follows from [noninterferent_general] *)
Corollary aux : forall P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2',
  ds2 ++ ds2' = ds1 ++ ds1' ->
  P !! PA |-ct- c ->
  pub_equiv P s1 s2 ->
  (b = false -> pub_equiv PA a1 a2) ->
  P |- <(s1, a1, b, ds1)> =[ c ]=> <(st1, ast1, b1, os1)>  ->
  P |- <(s2, a2, b, ds2)> =[ c ]=> <(st2, ast2, b2, os2)> ->
  ds1 = ds2 /\ ds1' = ds2'.
Proof.
  intros P PA s1 s2 a1 a2 b ds1 ds2 c st1 st2 ast1 ast2 b1 b2 os1 os2 ds1' ds2'
    Hds Hwt Heq Haeq Heval1 Heval2.
  pose proof Hds as H.
  symmetry in H.
  apply app_eq_prefix in H.
  eapply ct_well_typed_ideal_noninterferent_general in H;
    [ | | | | apply Heval1 | apply Heval2]; try eassumption.
  - destruct H as [ _ [ _ [ _ H] ] ]. subst. split; [reflexivity|].
    apply app_inv_head in Hds. congruence.
Qed.

Theorem ideal_spec_ct_secure :
  forall P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P !! PA |-ct- c ->
    pub_equiv P s1 s2 ->
    (b = false -> pub_equiv PA a1 a2) ->
    P |- <(s1, a1, b, ds)> =[ c ]=> <(s1', a1', b1', os1)> ->
    P |- <(s2, a2, b, ds)> =[ c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c s1 s2 a1 a2 b s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent a2'. generalize dependent a2.
  generalize dependent os2. generalize dependent b2'.
  induction Heval1; intros b2' os2' a2 Haeq a2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - (* seq *) eapply aux in H1; [| | | | apply Heval1_1 | apply H5 ]; eauto.
    destruct H1 as [H1 H1']. subst.
    assert(NI1 : pub_equiv P st' st'0 /\ b' = b'0 /\ (b' = false -> pub_equiv PA ast' ast'0)).
    { eapply ct_well_typed_ideal_noninterferent; [ | | | eassumption | eassumption]; eauto. }
    destruct NI1 as [NI1eq [NIb NIaeq] ]. subst.
    erewrite IHHeval1_2; [erewrite IHHeval1_1 | | | |];
      try reflexivity; try eassumption.
  - f_equal.
    + f_equal. eapply noninterferent_bexp; eassumption.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      erewrite noninterferent_bexp; eassumption.
  - f_equal.
    + f_equal. eapply noninterferent_bexp; eassumption.
    + eapply IHHeval1; try eassumption; try (destruct (beval st be); eassumption).
      * intro contra. discriminate contra.
      * erewrite noninterferent_bexp; eassumption.
  - eapply IHHeval1; eauto. repeat constructor; eassumption.
  - (* ARead *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* ARead_U *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
  - (* AWrite_U *) f_equal. f_equal. eapply noninterferent_aexp; eassumption.
Qed.

(** We now prove that the idealized semantics is equivalent to [sel_slh]
    transformation (Lemma 6 and the more precise Lemma 7). *)

(** All results about [sel_slh] below assume that the original [c] doesn't
    already use the variable ["b"] needed by the [sel_slh] translation. *)

Fixpoint a_unused (x:string) (a:aexp) : Prop :=
  match a with
  | ANum n      => True
  | AId y       => y <> x
  | <{a1 + a2}>
  | <{a1 - a2}>
  | <{a1 * a2}> => a_unused x a1 /\ a_unused x a2
  | <{b ? a1 : a2}> => b_unused x b /\ a_unused x a1 /\ a_unused x a2
  end
with b_unused (x:string) (b:bexp) : Prop :=
  match b with
  | <{true}>
  | <{false}>     => True
  | <{a1 = a2}>
  | <{a1 <> a2}>
  | <{a1 <= a2}>
  | <{a1 > a2}>   => a_unused x a1 /\ a_unused x a2
  | <{~ b1}>      => b_unused x b1
  | <{b1 && b2}>  => b_unused x b1 /\ b_unused x b2
  end.

Fixpoint unused (x:string) (c:com) : Prop :=
  match c with
  | <{{skip}}> => True
  | <{{y := e}}> => y <> x /\ a_unused x e
  | <{{c1; c2}}> => unused x c1 /\ unused x c2
  | <{{if be then c1 else c2 end}}> =>
      b_unused x be /\ unused x c1 /\ unused x c2
  | <{{while be do c end}}> => b_unused x be /\ unused x c
  | <{{y <- a[[i]]}}> => y <> x /\ a_unused x i
  | <{{a[i] <- e}}> => a_unused x i /\ a_unused x e
  end.

(** To simplify some proofs we also restrict to while-free programs for now. *)

(* SOONER: Even something as simple as [sel_slh_flag] below turns out to be hard
   for while loops, since it has the flavour of backwards compiler
   correctness. For backwards compiler correctness with while we probably need
   to use a small-step semantics and a simulation direction flipping trick? *)

Fixpoint no_while (c:com) : Prop :=
  match c with
  | <{{while _ do _ end}}> => False
  | <{{if _ then c1 else c2 end}}>
  | <{{c1; c2}}> => no_while c1 /\ no_while c2
  | _ => True
  end.

(** As a warm-up we prove that [sel_slh] properly updates the variable "b". *)

(** We start with a failed syntactic generalization *)

Lemma sel_slh_flag_gen : forall cc P s a (b:bool) ds s' a' (b':bool) os,
  <(s, a, b, ds)> =[ cc ]=> <(s', a', b', os)> ->
  forall sc,
    cc = sel_slh P sc ->
    unused "b" sc ->
    apply s "b" = (if b then 1 else 0) ->
    apply s' "b" = (if b' then 1 else 0).
Proof.
  intros cc P s a b ds s' a' b' os H. induction H; intros sc Heq Hunused Hsb. Focus 6.
  - (* No chance to prove the following to instantiate the IH:
       <{{ if be then c; while be do c end else skip end }}> = sel_slh P sc *)
Abort.

(** Maybe a more semantic generalization? *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall s a b ds s' a' b' os,
        (<(s, a, b, ds)> =[ c1 ]=> <(s', a', b', os)>)
    <-> (<(s, a, b, ds)> =[ c2 ]=> <(s', a', b', os)>).

Lemma cequiv_refl : forall c,
  cequiv c c.
Admitted.

Lemma cequiv_trans : forall c1 c2 c3,
  cequiv c1 c2 ->
  cequiv c2 c3 ->
  cequiv c1 c3.
Admitted.

Lemma cequiv_while_step : forall be c,
  cequiv <{{if be then c; while be do c end else skip end}}>
         <{{while be do c end}}>.
Admitted.

Lemma sel_slh_flag_gen : forall cc P s a (b:bool) ds s' a' (b':bool) os,
  <(s, a, b, ds)> =[ cc ]=> <(s', a', b', os)> ->
  forall sc,
    cequiv cc (sel_slh P sc) ->
    unused "b" sc ->
    apply s "b" = (if b then 1 else 0) ->
    apply s' "b" = (if b' then 1 else 0).
Proof.
  intros cc P s a b ds s' a' b' os H. induction H; intros sc Hequiv Hunused Hsb. 
  (* While case now provable *)
  Focus 6.
  eapply IHspec_eval; eauto. eapply cequiv_trans; eauto. apply cequiv_while_step.
  (* But the Seq case is now problematic *)
  Focus 3.
Admitted.

Lemma sel_slh_flag : forall sc P st ast (b:bool) ds st' ast' (b':bool) os,
  unused "b" sc ->
  apply st "b" = (if b then 1 else 0) ->
  <(st, ast, b, ds)> =[ sel_slh P sc ]=> <(st', ast', b', os)> ->
  apply st' "b" = (if b' then 1 else 0).
Proof.
  intros c P s a b ds s' a' b' os Hunused Hsb Heval.
  eapply sel_slh_flag_gen; eauto. apply cequiv_refl.
Abort.

Lemma sel_slh_flag : forall c P s a (b:bool) ds s' a' (b':bool) os,
  unused "b" c ->
  no_while c ->
  apply s "b" = (if b then 1 else 0) ->
  <(s, a, b, ds)> =[ sel_slh P c ]=> <(s', a', b', os)> ->
  apply s' "b" = (if b' then 1 else 0).
Proof.
  (* TODO: fix the proof that broke resulting of the switch to list-based maps *)
(*
  induction c; intros P s aa bb ds s' a' b' os Hunused Hnowhile Hsb Heval;
    simpl in *; try (inversion Heval; subst; now eauto).
  - inversion Heval; subst. rewrite t_update_neq; tauto.
  - inversion Heval; subst.
    eapply IHc2; try tauto; [|eassumption].
    eapply IHc1; try tauto; eassumption.
  - inversion Heval; subst; eauto.
    { destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
      + eapply IHc1; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. assumption.
      + eapply IHc2; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. assumption. }
    { destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
      + eapply IHc2; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. reflexivity.
      + eapply IHc1; try tauto; [|eassumption].
        simpl. rewrite Eqbe. rewrite t_update_eq. reflexivity. }
  - destruct (P x) eqn:Heq.
    + inversion Heval; inversion H10; subst.
      rewrite t_update_neq; try tauto.
      inversion H1; subst; rewrite t_update_neq; tauto.
    + inversion Heval; subst; rewrite t_update_neq; try tauto.
Qed.*)
Admitted.

(** We now prove that [sel_slh] implies the ideal semantics. *)

(* HIDE: no longer used in [sel_slh_ideal], but maybe still useful (TBD) *)
Lemma ideal_unused_same : forall P st ast b ds c st' ast' b' os X,
  unused X c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  apply st' X = apply st X.
Proof.
  (* TODO: fix the proof *)
(*
  intros P st ast b ds c st' ast' b' os X Hu Heval.
  induction Heval; simpl in Hu; try reflexivity; try (rewrite t_update_neq; tauto).
  - (* Seq *) rewrite IHHeval2; [| tauto]. rewrite IHHeval1; [| tauto]. reflexivity.
  - (* If *) destruct ( beval st be)  eqn:Dbe.
    + apply IHHeval; tauto.
    + apply IHHeval; tauto.
  - (* If_F *) destruct ( beval st be)  eqn:Dbe.
    + apply IHHeval; tauto.
    + apply IHHeval; tauto. 
  - (* While *) apply IHHeval. simpl. tauto.
Qed.*)
Admitted.

Lemma aeval_beval_unused_update : forall X st n, 
  (forall ae, a_unused X ae -> 
    aeval (X !-> n; st) ae = aeval st ae) /\
  (forall be, b_unused X be -> 
    beval (X !-> n; st) be = beval st be).
Proof. 
  intros X st n. apply aexp_bexp_mutind; intros;
  simpl in *; try reflexivity;
  try (
    rewrite H; [| tauto]; rewrite H0; [| tauto]; reflexivity
  ).
  - admit. (* rewrite t_update_neq; eauto. *)
    (* TODO: fix the proof *)
  - rewrite H; [| tauto]. rewrite H0; [| tauto]. rewrite H1; [| tauto].
    reflexivity.
  - rewrite H; auto.
Admitted.

Lemma aeval_unused_update : forall X st ae n,
  a_unused X ae ->
  aeval (X !-> n; st) ae = aeval st ae.
Proof. intros X st ae n. apply aeval_beval_unused_update. Qed.

Lemma beval_unused_update : forall X st be n,
  b_unused X be ->
  beval (X !-> n; st) be = beval st be.
  Proof. intros X st be n. apply aeval_beval_unused_update. Qed.

Lemma ideal_unused_update_rev_gen : forall P st ast b ds c st' ast' b' os X n,
  unused X c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  P |- <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os X n Hu H.
  induction H; simpl in Hu.
  - (* Skip *) econstructor.
  - (* Asgn *) 
    admit.
    (*rewrite t_update_permute; [| tauto].
    econstructor. rewrite aeval_unused_update; tauto. *)
    (* TODO *)
  - (* Seq *)
    econstructor. 
    + apply IHideal_eval1; tauto.
    + apply IHideal_eval2; tauto.
  - (* If *) 
    rewrite <- beval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite beval_unused_update; [ | tauto].
    destruct ( beval st be) eqn:D; apply IHideal_eval; tauto.
  - (* If_F *)
    rewrite <- beval_unused_update with (X:=X) (n:=n); [| tauto].
    econstructor.
    rewrite beval_unused_update; [ | tauto].
    destruct ( beval st be) eqn:D; apply IHideal_eval; tauto.
  - (* While *)
    econstructor. apply IHideal_eval. simpl; tauto.
  - (* ARead *)
    (* TODO: fix the proof *)
    admit.
    (* rewrite t_update_permute; [| tauto]. econstructor; [ | assumption].
    rewrite aeval_unused_update; tauto. *)
  - (* ARead_U *)
    (* TODO: fix the proof *)
    admit.
    (* rewrite t_update_permute; [| tauto]. econstructor; try assumption.
    rewrite aeval_unused_update; tauto. *)
  - (* AWrite *)
    econstructor; try assumption.
    + rewrite aeval_unused_update; tauto.
    + rewrite aeval_unused_update; tauto.
  - (* AWrite_U *)
    econstructor; try assumption.
    + rewrite aeval_unused_update; tauto.
    + rewrite aeval_unused_update; tauto.
Admitted.

Lemma ideal_unused_update_rev : forall P s a b ds c s' a' b' os x X,
  unused x c ->
  P |- <(s, a, b, ds)> =[ c ]=> <(x !-> apply s x; s', a', b', os)> ->
  P |- <(x !-> X; s, a, b, ds)> =[ c ]=> <(x !-> X; s', a', b', os)>.
Proof.
  intros P s a b ds c s' a' b' os x X Hu H.
  eapply ideal_unused_update_rev_gen in H; [| eassumption].
  admit.
  (* TODO: fix the proof *)
  (* rewrite t_update_shadow in H. eassumption.*)
Admitted.

Lemma ideal_unused_update : forall P st ast b ds c st' ast' b' os X n,
  unused X c ->
  P |- <(X !-> n; st, ast, b, ds)> =[ c ]=> <(X !-> n; st', ast', b', os)> ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(X !-> apply st X; st', ast', b', os)>.
Proof.
  intros P st ast b ds c st' ast' b' os X n Hu Heval.
  eapply ideal_unused_update_rev_gen with (X:=X) (n:=(apply st X)) in Heval; [| assumption].
  admit.
  (* TODO: fix the proof *)
  (* do 2 rewrite t_update_shadow in Heval. rewrite t_update_same in Heval. assumption.*)
Admitted.

Lemma sel_slh_ideal : forall c P s a (b:bool) ds s' a' (b':bool) os,
  unused "b" c ->
  no_while c ->
  apply s "b" = (if b then 1 else 0) ->
  <(s, a, b, ds)> =[ sel_slh P c ]=> <(s', a', b', os)> ->
  P |- <(s, a, b, ds)> =[ c ]=> <("b" !-> apply s "b"; s', a', b', os)>.
Proof.
  admit.

  (* TODO: fix the proof *)
(*  induction c; intros P s aa bb ds s' a' b' os Hunused Hnowhile Hsb Heval;
    simpl in *; inversion Heval; subst.
  - rewrite t_update_same. constructor.
  - rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor. reflexivity.
  - (* seq *) econstructor.
    + apply IHc1; try tauto; eassumption.
    + apply ideal_unused_update_rev; try tauto.
      eapply IHc2; try tauto.
      apply sel_slh_flag in H1; tauto.
  - destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst.
    + eapply IHc1 in H11; try tauto.
      * replace (OBranch true) with (OBranch (beval s be)) by now rewrite <- Eqbe.
        simpl. eapply Ideal_If. rewrite Eqbe.
        simpl in H11. rewrite Eqbe in H11. rewrite t_update_same in H11.
        apply H11.
      * rewrite t_update_eq. simpl. rewrite Eqbe. assumption.
    + eapply IHc2 in H11; try tauto.
      * replace (OBranch false) with (OBranch (beval s be)) by now rewrite <- Eqbe.
        simpl. eapply Ideal_If. rewrite Eqbe.
        simpl in H11. rewrite Eqbe in H11. rewrite t_update_same in H11.
        apply H11.
      * rewrite t_update_eq. simpl. rewrite Eqbe. assumption.
  - (* Ideal_If_F *)
    destruct (beval s be) eqn:Eqbe; inversion H10; inversion H1; subst; simpl in *;
      rewrite Eqbe in H11.
    + replace (OBranch true) with (OBranch (beval s be)) by now rewrite <- Eqbe.
      eapply Ideal_If_F. rewrite Eqbe.
      eapply IHc2 in H11; try tauto. rewrite t_update_eq in H11.
      eapply ideal_unused_update in H11; tauto.
    + replace (OBranch false) with (OBranch (beval s be)) by now rewrite <- Eqbe.
      eapply Ideal_If_F. rewrite Eqbe.
      eapply IHc1 in H11; try tauto. rewrite t_update_eq in H11.
      eapply ideal_unused_update in H11; tauto.
  - tauto.
  - destruct (P x) eqn:Heq; discriminate.
  - destruct (P x) eqn:Heq; discriminate.
  - destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    inversion H1; clear H1; subst. repeat rewrite <- app_nil_end in *.
    inversion H0; clear H0; subst; simpl in *.
    * rewrite t_update_neq; [| tauto]. rewrite Hsb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      rewrite t_update_eq. simpl.
      rewrite <- Hsb at 1. rewrite t_update_same.
      constructor; tauto.
    * rewrite t_update_neq; [| tauto]. rewrite Hsb.
      rewrite t_update_shadow. rewrite t_update_permute; [| tauto].
      simpl. rewrite <- Hsb at 1. rewrite t_update_same. apply Ideal_ARead_Prot; tauto.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor; tauto.
  - (* same *)
    destruct (P x) eqn:Heq; try discriminate H. inversion H; clear H; subst.
    rewrite t_update_permute; [| tauto]. rewrite t_update_same.
    constructor; tauto.
  - destruct (P x) eqn:Heq; discriminate H.
  - destruct (P x) eqn:Heq; discriminate H.
  - rewrite t_update_same. constructor; tauto.
  - rewrite t_update_same. constructor; tauto.
Qed.*)
Admitted.

(** Finally, we use this to prove spec_ct for sel_slh. *)

Theorem sel_slh_spec_ct_secure :
  forall P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds,
    P !! PA |-ct- c ->
    pub_equiv P s1 s2 ->
    pub_equiv PA a1 a2 ->
    unused "b" c ->
    no_while c ->
    apply s1 "b" = 0 ->
    apply s2 "b" = 0 ->
    <(s1, a1, false, ds)> =[ sel_slh P c ]=> <(s1', a1', b1', os1)> ->
    <(s2, a2, false, ds)> =[ sel_slh P c ]=> <(s2', a2', b2', os2)> ->
    os1 = os2.
Proof.
  intros P PA c s1 s2 a1 a2 s1' s2' a1' a2' b1' b2' os1 os2 ds
    Hwt Heq Haeq Hunused Hnowhile Hs1b Hs2b Heval1 Heval2.
  eapply sel_slh_ideal in Heval1; try assumption.
  eapply sel_slh_ideal in Heval2; try assumption.
  eapply ideal_spec_ct_secure; eauto.
Qed.

(* Test that spec_ct holds for sel_slh *)
QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_pub_arrs (fun PA =>

    forAll (gen_ct_well_typed_sized P PA 3) (fun c =>
    let hardened := sel_slh P c in

    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
    let s1 := ("b" !-> 0; s1) in
    let s2 := ("b" !-> 0; s2) in

    forAll gen_astate (fun a1 =>
    forAll (gen_pub_equiv_and_same_length PA a1) (fun a2 =>

    forAllMaybe (gen_spec_eval_sized hardened s1 a1 false 100) (fun '(ds, s1', a1', b', os1) =>
      match spec_eval_engine hardened s2 a2 false ds with
      | Some (s2', a2', b'', os2) => checker (
          obs_eqb os1 os2
        )
      | None => checker tt (* If the second execution crashes, this isn't a counterexample *)
      end
    ))))))))).

(* HIDE: The less useful for security direction of the idealized semantics being
   equivalent to [sel_slh]; easier to prove even for while (forwards compiler
   correctness). *)

Lemma spec_seq_assoc3 : forall st ast b ds c1 c2 c3 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2); c3 ]=> <( st', ast', b', os )>.
Proof. 
  intros st ast b ds c1 c2 c3 st' ast' b' os Heval.
  inversion Heval; subst; clear Heval. inversion H10; subst; clear H10.
  do 2 rewrite app_assoc. econstructor; [| eassumption].
  econstructor; eassumption.
Qed.

Lemma spec_seq_assoc4 : forall st ast b ds c1 c2 c3 c4 st' ast' b' os,
  <( st, ast, b, ds )> =[ c1; c2; c3; c4 ]=> <( st', ast', b', os )> ->
  <( st, ast, b, ds )> =[ (c1; c2; c3); c4 ]=> <( st', ast', b', os )>.
Proof. 
  intros st ast b ds c1 c2 c3 c4 st' ast' b' os Heval.
  inversion Heval; subst; clear Heval. inversion H10; subst; clear H10. inversion H12; subst; clear H12.
  do 4 rewrite app_assoc. econstructor; [| eassumption].
  do 2 rewrite <- app_assoc. econstructor; [eassumption |].
  econstructor; eassumption.
Qed.

Lemma spec_seq_skip_r : forall st ast b ds c st' ast' b' os,
  <(st, ast, b, ds)> =[ c; skip ]=> <(st', ast', b', os)> ->
  <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)>.
Proof.
  intros st ast b ds c st' ast' b' os Heval.
  rewrite <- (app_nil_r ds) in Heval; rewrite <- (app_nil_r os) in Heval.
  inversion Heval; inversion H10; subst.
  do 2 rewrite app_nil_r in H1; do 2 rewrite app_nil_r in H5; subst.
  assumption.
Qed.

Lemma ideal_sel_slh : forall P st ast b ds c st' ast' b' os,
  unused "b" c ->
  P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> ->
  <("b" !-> (if b then 1 else 0); st, ast, b, ds)> =[ sel_slh P c ]=>
    <("b" !-> (if b' then 1 else 0); st', ast', b', os)>.
Proof.
  admit.
  (* TODO: fix the proof *)
(*  intros P st ast b ds c st' ast' b' os Hunused Heval.
  induction Heval; simpl in *.
  - (* Skip *) constructor.
  - (* Asgn *)
    rewrite t_update_permute; [| tauto].
    econstructor. rewrite aeval_unused_update; tauto.
  - (* Seq *) 
    econstructor.
      + eapply IHHeval1. tauto.
      + eapply IHHeval2. tauto.
  - (* If *) 
    replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + (* true *) 
      rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      econstructor.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
    + (* false ; provable in the same way as the true case *)
      rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_same. apply IHHeval. tauto.
  - (* If_f ; provable in the same way as the If case *)
    replace (beval st be) with (beval ("b" !-> (if b then 1 else 0); st) be)
      by (apply beval_unused_update; tauto).
    apply Spec_If_F. rewrite beval_unused_update; [| tauto].
    destruct (beval st be) eqn:Eqbeval.
    + rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
    + rewrite <- (app_nil_l ds); rewrite <- (app_nil_l os1).
      eapply Spec_Seq.
      * apply Spec_Asgn. reflexivity.
      * simpl. rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        rewrite t_update_shadow. apply IHHeval. tauto.
  - (* While (most difficult case) *)
    assert(G : b_unused "b" be /\
      (unused "b" c /\ b_unused "b" be /\ unused "b" c) /\ True) by tauto.
    specialize (IHHeval G). clear G.
    inversion IHHeval; clear IHHeval; subst. 
    + (* no misspeculation in while execution (Spec_If) *)
      rewrite beval_unused_update in H10; [ | tauto].
      destruct (beval st be) eqn:Eqbeval.
      * (* true *)
        apply spec_seq_assoc4 in H10.
        inversion H10; subst.
        do 2 rewrite app_comm_cons.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc3. assumption.
      * (* false *)
        eapply spec_seq_skip_r in H10. inversion H10; subst.
        rewrite <- (app_nil_r [OBranch _ ]). rewrite <- (app_nil_r [DStep]). rewrite H6.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply Spec_Skip.
    + (* mispeculation in while execution (Spec_If_f) ; 
         provable analog to the no misspeculation case *)
      rewrite beval_unused_update in H10; [ | tauto].
      destruct (beval st be) eqn:Eqbeval.
      * (* true *)
        eapply spec_seq_skip_r in H10. inversion H10; subst.
        rewrite <- (app_nil_r [OBranch _ ]). rewrite <- (app_nil_r [DForce]). rewrite H6.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If_F.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply Spec_Skip.
      * (* false *)
        apply spec_seq_assoc4 in H10.
        inversion H10; subst.
        do 2 rewrite app_comm_cons.
        eapply Spec_Seq; [| eassumption].
        apply Spec_While. eapply Spec_If_F.
        rewrite beval_unused_update; [| tauto]. rewrite Eqbeval.
        apply spec_seq_assoc3. assumption.
  - (* ARead *)
    rewrite t_update_permute; [| tauto].
    destruct (P x) eqn:EqPx.
    * (* public *)
      rewrite <- (app_nil_r [DStep]); rewrite <- (app_nil_r [OARead _ _]).
      eapply Spec_Seq.
      { apply Spec_ARead; [| tauto]. rewrite aeval_unused_update; tauto. }
      { assert (G : (x !-> nth i (ast a) 0; "b" !-> 0; st) =
                    (x !-> aeval (x !-> nth i (ast a) 0; "b" !-> 0; st)
                                 <{{("b" = 1) ? 0 : x}}>;
                    x !-> nth i (ast a) 0; "b" !-> 0; st)).
        { simpl. rewrite t_update_neq; [|tauto]. rewrite t_update_eq. simpl.
          rewrite t_update_same. reflexivity. }
        rewrite G at 2. apply Spec_Asgn. reflexivity. }
    * (* secret *)
      apply Spec_ARead; [| tauto]. rewrite aeval_unused_update; tauto.
  - (* ARead_U *)
    rewrite H. unfold secret. rewrite t_update_permute; [| tauto].
    apply Spec_ARead_U; try tauto. rewrite aeval_unused_update; tauto.
  - (* ARead_Prot *)
    rewrite H. unfold public.
    rewrite <- (app_nil_r [DLoad _ _]); rewrite <- (app_nil_r [OARead _ _]). 
    eapply Spec_Seq.
    + apply Spec_ARead_U; try tauto. rewrite aeval_unused_update; tauto.
    + assert (G : ("b" !-> 1; x !-> 0; st) =
                  (x !-> aeval (x !-> nth i' (ast a') 0; "b" !-> 1; st)
                               <{{("b" = 1) ? 0 : x}}>;
                   x !-> nth i' (ast a') 0; "b" !-> 1; st)).
      { simpl. rewrite t_update_neq; [|tauto]. rewrite t_update_eq. simpl.
        rewrite t_update_permute; [| tauto]. rewrite t_update_shadow. reflexivity. }
      rewrite G. simpl. apply Spec_Asgn. reflexivity.
  - (* AWrite *) constructor; try rewrite aeval_unused_update; tauto.
  - (*AWrite_U *) constructor; try rewrite aeval_unused_update; tauto.
Qed. *)
Admitted.

(* Returns (ds, st', ast', b', os) such that P |- <(st, ast, b, ds)> =[ c ]=> <(st', ast', b', os)> *)
Fixpoint gen_ideal_eval_sized (P : pub_vars) (c : com) (st : state) (ast : astate) (b : bool) (size : nat): G (option (dirs * state * astate * bool * obs)) :=
  match c with
  | <{ skip }> =>
    let ds := [] in
    let st' := st in
    let ast' := ast in
    let b' := b in
    let os := [] in
    returnGen (Some (ds, st', ast', b', os))
  | <{ x := e }> =>
    let n := aeval st e in

    let ds := [] in
    let st' := (x !-> n; st) in
    let ast' := ast in
    let b' := b in
    let os := [] in
    returnGen (Some (ds, st', ast', b', os))
  | <{ x <- a[[ie]] }> =>
    let i := aeval st ie in

    if i <? List.length (apply ast a)
    then
      let ds := [DStep] in
      let st' := (x !-> if b && apply P x then 0 else nth i (apply ast a) 0; st) in
      let ast' := ast in
      let b' := b in
      let os := [OARead a i] in
      returnGen (Some (ds, st', ast', b', os))
    else (* i >= List.length (apply ast a) *)
    if b then
      bindOpt (gen_arr_not_nil ast) (fun a' => (* prioritize generating a non-empty array *)
      bindOpt (gen_nat_lt (List.length (apply ast a'))) (fun i' =>

      let ds := [DLoad a' i'] in
      let st' := (x !-> if apply P x then 0 else nth i' (apply ast a') 0; st) in
      let ast' := ast in
      let b' := true in
      let os := [OARead a i] in
      returnGen (Some (ds, st', ast', b', os))
      ))
    else returnGen None
  | <{ a[ie] <- e }> =>
    let i := aeval st ie in
    let n := aeval st e in

    if i <? List.length (apply ast a)
    then
      let ds := [DStep] in
      let st' := st in
      let ast' := (a !-> upd i (apply ast a) n; ast) in
      let b' := b in
      let os := [OAWrite a i] in
      returnGen (Some (ds, st', ast', b', os))
    else (* i >= List.length (apply ast a) *)
    if b then
      bindOpt (gen_arr_not_nil ast) (fun a' => (* prioritize generating a non-empty array *)
      bindOpt (gen_nat_lt (List.length (apply ast a'))) (fun i' =>

      let ds := [DStore a' i'] in
      let st' := st in
      let ast' := (a' !-> upd i' (apply ast a') n; ast) in
      let b' := true in
      let os := [OAWrite a i] in
      returnGen (Some (ds, st', ast', b', os))
      ))
    else returnGen None
  | _ =>
    match size with
    | O => returnGen None
    | S size =>
        match c with
        | <{ c1 ; c2 }> =>
            bindOpt (gen_ideal_eval_sized P c1 st ast b size) (fun '(ds1, st', ast', b', os1) =>
            bindOpt (gen_ideal_eval_sized P c2 st' ast' b' size) (fun '(ds2, st'', ast'', b'', os2) =>
            returnGen (Some (ds1 ++ ds2, st'', ast'', b'', os1 ++ os2))
            ))
        | <{ if be then c1 else c2 end }> =>
            dir <- elems [DStep; DForce];;

            match dir with
            | DStep =>
                let condition := beval st be in
                let next_c := if condition then c1 else c2 in
                bindOpt (gen_ideal_eval_sized P next_c st ast b size) (fun '(ds, st', ast', b', os) =>
                returnGen (Some (DStep::ds, st', ast', b', (OBranch condition)::os))
                )
            | DForce =>
                let condition := beval st be in
                let next_c := if condition then c2 else c1 in
                bindOpt (gen_ideal_eval_sized P next_c st ast true size) (fun '(ds, st', ast', b', os) =>
                returnGen (Some (DForce::ds, st', ast', b', (OBranch condition)::os))
                )
            | _ => returnGen None
            end
        | <{ while be do c end }> =>
            gen_ideal_eval_sized P <{ if be then c; while be do c end else skip end }> st ast b size
        | _ => returnGen None
        end
    end
  end.

(* HIDE: Moving syntactic constraints about ds and os out of the conclusions of
   rules and into equality premises could make this proof script less
   verbose. Maybe just define "smart constructors" for that? *)

QuickChick (forAll gen_pub_vars (fun P =>
    forAll arbitrary (fun c =>

    forAll gen_state (fun st =>
    forAll gen_astate (fun ast =>

    forAll arbitrary (fun b =>

    forAllMaybe (gen_ideal_eval_sized P c st ast b 100) (fun '(ds, st', ast', b', os) =>
      let hardened := sel_slh P c in
      printTestCase ((show hardened) ++ nl) (

      let input_state_with_b := "b" !-> (if b then 1 else 0); st in
      let output_state_with_b := "b" !-> (if b' then 1 else 0); st' in

      match spec_eval_engine hardened input_state_with_b ast b ds with
      | Some (st'', ast'', b'', os') =>
          printTestCase ((show st'') ++ nl) (
          printTestCase ((show ast'') ++ nl) (

          (state_eqb st'' output_state_with_b) && (astate_eqb ast' ast'') &&
          (Bool.eqb b' b'') && (obs_eqb os os')
          ))
      | None => checker tt (* If the second execution crashes, this isn't a counterexample *)
      end
    )))))))).

