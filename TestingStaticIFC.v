(** * StaticIFC: Information Flow Control Type Systems *)

(* TERSE: HIDEFROMHTML *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SECF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From SECF Require Export Imp.
From Coq Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Export MonadNotation. Open Scope monad_scope.
From Coq Require Import String. (* Local Open Scope string. *)
(* TERSE: /HIDEFROMHTML *)

(* String variables not so easy for testing as plain numbers, but
   let's try simply "Xn" that's skewed towards low numbers n. *)

#[export] Instance genId : Gen string :=
  {arbitrary := (n <- freq [(10, ret 0);
                             (9, ret 1);
                             (8, ret 2);
                             (4, ret 3);
                             (2, ret 4);
                             (1, ret 5)];;
                 ret ("X" ++ show n)%string) }.

#[export] Instance shrinkId : Shrink string :=
  {shrink :=
    (fun s => match get 1 s with
              | Some a => match (nat_of_ascii a - nat_of_ascii "0") with
                          | S n => ["X" ++ show (S n / 2); "X" ++ show (S n - 1)]
                          | 0 => []
                          end
              | None => nil
              end)%string }.

Eval compute in (shrink "X5")%string.
Eval compute in (shrink "X0")%string.

(* Deriving generators and shrinkers for aexp, bexp, and com *)

Derive (Arbitrary, Shrink) for aexp.
Derive (Arbitrary, Shrink) for bexp.
Derive (Arbitrary, Shrink) for com.

(* Print (arbitrary : G com). LATER: Why does this fail? *)

(* QuickChick could also generate show instances for these, just that
   the manual ones below better match our existing Coq notations
   (still not perfect in terms of parentheses) *)

(* Derive Show for aexp. *)
(* Derive Show for bexp. *)
(* Derive Show for com. *)

#[export] Instance showAexp : Show aexp :=
  {show :=
      (let fix showAexpRec (a:aexp) : string :=
         match a with
         | AId i => String DoubleQuote (i ++ String DoubleQuote "")
         | ANum n => show n
         | <{x + y}> => "(" ++ showAexpRec x ++ " + " ++ showAexpRec y ++ ")"
         | <{x - y}> => "(" ++ showAexpRec x ++ " - " ++ showAexpRec y ++ ")"
         | <{x * y}> => "(" ++ showAexpRec x ++ " * " ++ showAexpRec y ++ ")"
         end
       in showAexpRec)%string
   }.

#[export] Instance showBexp : Show bexp :=
  {show :=
      (let fix showBexpRec (a:bexp) : string :=
         match a with
         | <{true}> => "true"%string
         | <{false}> => "false"%string
         | <{x <= y}> => "(" ++ show x ++ " <= " ++ show y ++ ")"
         | <{x > y}> => "(" ++ show x ++ " > " ++ show y ++ ")"
         | <{x = y}> => "(" ++ show x ++ " = " ++ show y ++ ")"
         | <{x <> y}> => "(" ++ show x ++ " <> " ++ show y ++ ")"
         | <{~x}> => "(~ " ++ showBexpRec x ++ ")"
         | <{x && y}> => "(" ++ showBexpRec x ++ " && " ++ showBexpRec y ++ ")"
         end
       in showBexpRec)%string
  }.

#[export] Instance showCom : Show com :=
  {show :=
      (let fix showComRec (a:com) : string :=
         match a with
         | <{skip}> => "skip"%string
         | <{x := y}> => "(" ++ show x ++ ":= " ++ show y ++ ")"
         | <{x ; y}> => "(" ++ showComRec x ++ " ; " ++ showComRec y ++ ")"
         | <{if x then y else z end}> => "(if " ++ show x ++
                                        " then " ++ showComRec y ++
                                        " else " ++ showComRec z ++ " end)"
         | <{while x do y end}> => "(while " ++ show x ++ " do "
                                            ++ showComRec y ++ " end)"
         end
       in showComRec)%string
  }.

(* For sizes larger than 1-2 these objects seem larger than what we need.
   SOONER: May want to reduce sizes below?
   Or just listen to John Hughes and implement a good shrinker? *)
Sample (arbitrarySized 2 : G aexp).
Sample (arbitrarySized 1 : G bexp). (* TODO: these get too big *)
Sample (arbitrarySized 1 : G com).

(* HIDE: This one no longer works, but was still in some old QC examples:
Derive Sized for aexp. *)

Fixpoint size_aexp (a:aexp) : nat :=
  match a with
  | ANum _ | AId _ => 1
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => 1 + size_aexp a1 + size_aexp a2
  end.

QuickChick (forAll arbitrary (fun (a:aexp) =>
            collect (size_aexp a) true)).

(* Time Elapsed: 0.533273s *)
(* QuickChick (forAll arbitrary (fun (a:aexp) => *)
(*             true)). *)

(* Time Elapsed: 37.837302s -- with discards *)
(* QuickChick (forAll arbitrary (fun (a:aexp) => *)
(*             (implication false false))). *)

Fixpoint size_bexp (a:bexp) : nat :=
  match a with
  | <{ true }> | <{ false }> => 1
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => 1 + size_aexp a1 + size_aexp a2
  | <{ ~b }> => 1 + size_bexp b
  | <{ b1 && b2 }> => 1 + size_bexp b1 + size_bexp b2
  end.

QuickChick (forAll arbitrary (fun (b:bexp) =>
            collect (size_bexp b) true)).

Fixpoint size_com (c:com) : nat :=
  match c with
  | <{ skip }> => 1
  | <{ X := a }> => 1 + size_aexp a
  | <{ c1 ; c2 }> => 1 + size_com c1 + size_com c2
  | <{ if b then c1 else c2 end }> =>
      1 + size_bexp b + size_com c1 + size_com c2
  | <{ while b do c1 end }> =>
      1 + size_bexp b + size_com c1
  end.

QuickChick (forAll arbitrary (fun (c:com) =>
            collect (size_com c) true)).

(* Time Elapsed: 2.964364s *)
(* QuickChick (forAll arbitrary (fun (c:com) => *)
(*             true)). *)

(* Time Elapsed: 229.742461s -- with discards *)
(* QuickChick (forAll arbitrary (fun (c:com) => *)
(*             (implication false false))). *)

(* SOONER: I sometimes have troubles with the printing just stopping;
   not sure if it has to do with the instances below, or it's just a
   QuickChick / Coq / Emacs / Proof General / ... bug. For instance,
   the `G bexp` printer above printed this cropped output for me:
[(((4 + "X2") * "X1") = (("X0" + "X2") - (6 - "X0"))); ((((9 - (("X1"
- (2 - ("X5" - ("X2" + "X5")))) * 1)) + ((((("X5" + (7 - (("X2" * 9) -
9))) - (((9 * (0 * 0)) - (1 + (6 + "X1"))) + ((0 - 1) + "X2"))) +
"X2") - (2 * ("X2" * (5 + (((0 + "X2") * "X1") - 9))))) * ((("X1" -
"X0") * "X2") - (("X1" - ("X0" + ((("X2" * "X4") + 4) * 8))) * "X0")))
*)

(* SOONER: I'm generally not longer sure how sized generators
   work. Should relearn more about them and try to prevent that we
   have arbitrary magic numbers everywhere.

   Now I'm even more worried with not having any numbers though, since
   QC could generate huge expressions for instance, which is not needed.

   Should gather statistics about the terms we generate and
   whether their sizes are good for testing. For instance, we may be
   generating too large expressions, but too small commands,
   especially in the number of assignments? Worth investigating. *)

(* SOONER: One forcing function for this would be to start introducing
   mutants. Should start trying that soon anyway! *)

Eval compute in shrink
       <{while ("X1" = (((6 * (4 - 0)) + (("X4" + "X0") - (3 * (("X1" + 3) * 3)))) + "X1"))
           do ("X0":= "X0") end}>%string.

(* For testing, we can't use functions to implement total_map, so we
   need something more computational for states and variable assignments.
   We build on top of the list-based maps from TImp.v (volume 4). *)

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

Eval compute in (union ["1";"2";"3"] ["2";"3";"4"])%string.

(* QuickChick already knows how to sample such maps. We will define a
   specialized generator below that e.g. doesn't repeat keys, but
   first let's use the automatically-derived generator for maps to
   make sure our maps work well even in those cases. *)

Sample (arbitrary : G (Map nat)).

(* As opposed to TImp.v, here we try hard to keep the total_map
   interface by pairing a default value with a list-based map.
   This payed off, we could keep most of this file unchanged when
   switching to the new representation. *)

Definition total_map (X:Type) : Type := X * Map X.

Sample (arbitrary : G (total_map nat)).

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

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(* We can no longer just use function application for map lookups,
   instead we define a combinator for this: *)
Definition apply {A:Type} (m : total_map A) (x:string) : A := 
  match m with
  | (d, lm) => match map_get lm x with
               | Some v => v
               | None => d
               end
  end.

Example update_example1 : apply examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : apply examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : apply examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : apply examplemap' "bar" = true.
Proof. reflexivity. Qed.

(* We do our testing using the new version of state: *)
Definition state := total_map nat.

Check t_apply_empty.
QuickChick (forAll arbitrary (fun (x:string) =>
            forAll arbitrary (fun (v:nat) =>
            apply (_ !-> v) x = v ?))).

Check t_update_eq.
QuickChick (forAll arbitrary (fun (x:string) =>
            forAll arbitrary (fun (v:nat) =>
            forAll arbitrary (fun (m:state) =>
            apply (x !-> v ; m) x = v ?)))).

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  apply (x !-> v ; m) x = v.
Admitted.
(* LATER: This is well tested, so not a problem to admit for now ;)
   We do this for the two total_map lemmas used in the proofs below.
   They are not that relevant for our testing. *)

Check t_update_neq.
QuickChick (forAll arbitrary (fun (x1:string) =>
            forAll arbitrary (fun (x2:string) =>
            implication (x1 <> x2 ?)
            (forAll arbitrary (fun (v:nat) =>
             forAll arbitrary (fun (m:state) =>
              (apply (x1 !-> v ; m) x2 = apply m x2 ?))))))).
(* SOONER: figure out why `===>` notation doesn't work for implication *)
(* LATER: could also easily get rid of the discards here; but choosing
   this order is anyway quite fine *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  apply (x1 !-> v ; m) x2 = apply m x2.
Admitted. 

(* Extensional equality for total_map (this differs from Coq [=] on
   this type, since our maps don't have a canonical representation): *)

Definition total_map_beq (a:Type) (a_beq:a->a->bool) (m1 m2 : total_map a) :=
  match m1, m2 with
  | (d1,lm1), (d2,lm2) => a_beq d1 d2 &&
      forallb (fun x => a_beq (apply m1 x) (apply m2 x))
              (union (map_dom lm1) (map_dom lm2))
  end.

Definition state_beq := total_map_beq nat Nat.eqb.

Check t_update_shadow.
QuickChick (forAll arbitrary (fun (x:string) =>
            forAll arbitrary (fun (v1:nat) =>
            forAll arbitrary (fun (v2:nat) =>
            forAll arbitrary (fun (m:state) =>
            state_beq (x !-> v2 ; x !-> v1 ; m)
                      (x !-> v2 ; m)))))).

Check t_update_same.
QuickChick (forAll arbitrary (fun (x:string) =>
            forAll arbitrary (fun (v:nat) =>
            forAll arbitrary (fun (m:state) =>
            state_beq (x !-> apply m x ; m) m)))).

Check t_update_permute.
QuickChick (forAll arbitrary (fun (x1:string) =>
            forAll arbitrary (fun (x2:string) =>
            implication (x2 <> x1 ?)
            (forAll arbitrary (fun (v1:nat) =>
             forAll arbitrary (fun (v2:nat) =>
             forAll arbitrary (fun (m:state) =>
             (state_beq (x1 !-> v1 ; x2 !-> v2 ; m)
                        (x2 !-> v2 ; x1 !-> v1 ; m))))))))).
(* LATER: could also easily get rid of the discards here *)

(* Here is a specialized version of `Gen (total_map a)` that doesn't
   repeat keys, binds all vars, and that puts them in order. *)

#[export] Instance genTotalMap (A:Type) `{Gen A} : Gen (total_map A) :=
  {arbitrary := (d <- arbitrary;;
                 v0 <- arbitrary;;
                 v1 <- arbitrary;;
                 v2 <- arbitrary;;
                 v3 <- arbitrary;;
                 v4 <- arbitrary;;
                 v5 <- arbitrary;;
                 ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
                         ("X3",v3); ("X4",v4); ("X5",v5)])%string)}.

Sample (arbitrary : G state).

(* Just duplicating the following definitions so that they use the
   testable total_maps: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => apply st x (* <--- NEW: apply is now needed here *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
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

(* HIDEFROMHTML *)
Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).
(* /HIDEFROMHTML *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** * Noninterference *)

(** As explained in \CHAP{Noninterference} and \CHAP{RelHoare}, data
    confidentiality is most often expressed formally as a property
    called _noninterference_.

    To formalize this for Imp programs, we divide the variables as
    either public or secret by assuming a total map [P : pub_vars]
    between variables and Boolean labels: *)

Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := total_map label.

Sample (arbitrary : G pub_vars).

(** TERSE: ** Publicly equivalent states *)

(** A noninterference attacker can only observe the values of public
    variables, not of secret ones. We formalize this as a notion of
    _publicly equivalent_ states that agree on the values of all
    public variables, which are thus indistinguishable to an attacker: *)

Definition pub_equiv (P : pub_vars) {X:Type} (s1 s2 : total_map X) : Prop :=
  forall x:string, apply P x = true -> apply s1 x = apply s2 x.

Definition pub_equivb (P : pub_vars) (s1 s2 : state) : bool :=
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

(* LATER: could also define decidability type class; but it requires proving pub_equivb correct *)
(* #[export] Instance decPubEquiv P (s1 s2 : state) : Dec (pub_equiv P s1 s2). *)
(* Proof. dec_eq. Defined. *)

(** For some total map [P] from variables to Boolean labels,
    [pub_equiv P] is an equivalence relation on states, so reflexive,
    symmetric, and transitive. *)

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s : state) =>
            pub_equivb P s s))).

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s1 s2 : state) =>
            implication (pub_equivb P s1 s2) (pub_equivb P s2 s1)))).

Definition gen_pub_equiv (P : pub_vars) (s:state) : G state :=
  match s with
  | (d,m) => v0 <- (if apply P "X0" then ret (apply s "X0") else arbitrary)%string;;
             v1 <- (if apply P "X1" then ret (apply s "X1") else arbitrary)%string;;
             v2 <- (if apply P "X2" then ret (apply s "X2") else arbitrary)%string;;
             v3 <- (if apply P "X3" then ret (apply s "X3") else arbitrary)%string;;
             v4 <- (if apply P "X4" then ret (apply s "X4") else arbitrary)%string;;
             v5 <- (if apply P "X5" then ret (apply s "X5") else arbitrary)%string;;
             ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
                     ("X3",v3); ("X4",v4); ("X5",v5)])%string
  end.

(* With this smart generator we can test the equivalence properties much better: *)

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s1 : state) =>
            forAll (gen_pub_equiv P s1) (fun (s2 : state) =>
            pub_equivb P s1 s2)))).

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s1 : state) =>
            forAll (gen_pub_equiv P s1) (fun (s2 : state) =>
            pub_equivb P s2 s1)))).

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s2 : state) =>
            forAll (gen_pub_equiv P s2) (fun (s1 : state) =>
            forAll (gen_pub_equiv P s2) (fun (s3 : state) =>
            pub_equivb P s1 s3))))).

(* TERSE: HIDEFROMHTML *)
Lemma pub_equiv_refl : forall {X:Type} (P : pub_vars) (s : total_map X),
  pub_equiv P s s.
Proof. intros X P s x Hx. reflexivity. Qed.

Lemma pub_equiv_sym : forall {X:Type} (P : pub_vars) (s1 s2 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s1.
Proof. unfold pub_equiv. intros X P s1 s2 H x Px. rewrite H; auto. Qed.

Lemma pub_equiv_trans : forall {X:Type} (P : pub_vars) (s1 s2 s3 : total_map X),
  pub_equiv P s1 s2 ->
  pub_equiv P s2 s3 ->
  pub_equiv P s1 s3.
Proof. unfold pub_equiv. intros X P s1 s2 s3 H12 H23 x Px.
       rewrite H12; try rewrite H23; auto. Qed.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: ** Noninterference *)

(** Program [c] is _noninterferent_ if whenever it has two terminating
    runs from two publicly equivalent initial states [s1] and [s2],
    the obtained final states [s1'] and [s2'] are also publicly equivalent. *)

Definition noninterferent P c := forall s1 s2 s1' s2',
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv P s1' s2'.

(** Intuitively, [c] is noninterferent when the value of the public
    variables in the final state can only depend on the value of
    public variables in the initial state, and do not depend on the
    initial value of secret variables. *)

(* Trying to test this quickly, using the interpreter that skips while
   loops for now. Again, we need to repeat this definition so that it
   uses the new representation of maps (SF is not that modular): *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st  (* bogus *)
  end.

(* LATER: For while loops try out fueled interpreter too. Not as simple though. *)

(* This should fail, since not all programs are noninterferent *)

Definition shrink_pub_equiv (P:pub_vars) (s:state) : list state :=
  let '(d,m) := s in
  (if fst P then []
   else d' <- shrink d;; ret (d',m))
    ++ 
  (m' <- (let fix aux (l:Map nat) : list (Map nat) :=
              match l with
              | (x,v) :: l' => 
                  (if (v =? d) || negb (apply P x) then [l'] else []) ++
                    map (cons (x,v)) (aux l') ++
                    if apply P x then []
                    else map (fun v' => (x,v')::l') (shrink v)
              | [] => []
              end
            in aux m);;
     ret (d, m')).

Sample (gen_pub_equiv (public, [("X0",public); ("X1",false); ("X2",false)])
                      (70, [("X0",42); ("X1",100); ("X2",3)]) )%string.

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll arbitrary (fun (s1 : state) =>
            forAll (elems_ s1 (shrink_pub_equiv P s1)) (fun (s2' : state) =>
              pub_equivb P s1 s2')))).

(* Eval compute in (shrink_pub_equiv *)
(*                    (true, [("X0", false); ("X1", false); ("X2", false); ("X3", false); ("X4", true); ("X5", true)]) *)
(*                    (0, [("X0", 0); ("X1", 0); ("X2", 0); ("X3", 0); ("X4", 0); ("X5", 0)]) *)
(*                    (0, [("X0", 0); ("X1", 0); ("X2", 0); ("X3", 0); ("X4", 0); ("X5", 0)]))%string. *)

QuickChick (forAllShrink arbitrary shrink (fun (P : pub_vars) =>
            forAllShrink arbitrary shrink (fun (c : com) =>
            forAllShrink arbitrary shrink (fun (s1 : state) =>
            forAllShrink (gen_pub_equiv P s1) (shrink_pub_equiv P)
            (fun (s2 : state) =>
              (pub_equivb P (ceval_fun_no_while s1 c)
                            (ceval_fun_no_while s2 c))))))).

(* Indeed it does fail. QuickChick finds an explicit flow most of the
   time!  A bit later below we will show that with a bit more work we
   can also find implicit flows (i.e. by only generating commands
   without explicit flows).*)

(* SOONER: Looking at the counterexamples above it seems that P is not
           shrunk, but in my attempts shrink seems to work fine for pub_vars?
           Could it be that the shrinking for P should be done after
           the shrinking for s1 and s2?
           Or maybe the 3 of them should be shrunk together? *)
(* SOONER: I anyway don't understand how nested forAllShrinks work.
           Worth investigating, at least to double check that what we
           do above for shrinking is sound without extra premises. *)

(** TERSE: ** *)

(** TERSE: A first noninterferent program *)

(** For instance, consider the following command
    (taken from \CHAP{Noninterference}): *)

Definition secure_com : com := <{ X := X+1; Y := X+Y*2 }>.

(** If we assume that variable [X] is public and variable [Y] is
    secret, we can state noninterference for [secure_com] as follows: *)

Definition xpub : pub_vars := (X !-> public; _ !-> secret).

Definition noninterferent_secure_com :=
  noninterferent xpub secure_com.

(** We have already proved that [secure_com] is indeed noninterferent
    both directly using the semantics (in \CHAP{Noninterference}) and using
    RHL (in \CHAP{RelHoare}). Both these proofs were manual though,
    while in this chapter we will show how this proof can be done more
    syntactically using several _information flow control_ (IFC) type
    systems that enforce noninterference for all well-typed programs. *)

(** TERSE: ** Explicit flows *)

(** Not all programs are noninterferent though. For instance, a
    program that reads the contents of a secret variable and uses that
    to change the value of a public variable is unlikely to be
    noninterferent. We call this an _explicit flow_ and all our type
    systems will prevent _all_ explicit flows.

    Here is a program that has an explicit flow, which breaks
    noninterference, as we already proved in \CHAP{Noninterference}. *)

Definition insecure_com1 : com :=
  <{ X := Y+1; (* <- bad explicit flow! *)
     Y := X+Y*2 }>.

Definition interferent_insecure_com1 :=
  ~noninterferent xpub insecure_com1.

(** TERSE: ** Not all explicit flows are harmful *)

(** Not all explicit flows break noninterference though. For instance,
    the following variant of [insecure_com1] is noninterferent even if
    it has an explicit flow. The reason for this is that the variable
    [X] is overwritten with public information in a subsequent assignment. *)

Definition secure_com1' : com :=
  <{ X := Y+1; (* <- harmless explicit flow (dead store) *)
     X := 42; (* <- X is overwritten afterwards *)
     Y := X+Y*2 }>.

(** Since our IFC type systems will prevent all explicit flows, they
    will also reject [secure_com1'], even if it is secure with respect
    to our attacker model for noninterference, in which the attacker
    only observes the final values of public variables.

    As usual, our type systems will only provide sound syntactic
    overapproximations of the semantic property of noninterference. *)

(* LATER: Can we also find the [secure_com1'] above by testing? *)

(** TERSE: ** Implicit flows *)

(** Explicit flows are not the only way to leak secrets: one can also
    leak secrets using the control flow of the program, by branching
    on secrets and then assigning to public variables. We call these
    leaks _implicit flows_. *)

Definition insecure_com2 : com :=
  <{ if Y = 0
     then Y := 42
     else X := X+1 (* <- bad implicit flow! *)
     end }>.

(** Here the expression [X+1] we are assigning to [X] is public
    information, but we are doing this assignment after we branched on
    a secret condition [Y = 0], so we are indirectly leaking
    information about the value of [Y]. In this case we can infer that
    if [X] gets incremented the value of [Y] is not [0]. We have
    proved in \CHAP{Noninterference} that this program is insecure, so it
    will be rejected by our type systems, which enforce noninterference
    by preventing _all_ implicit flows. *)

(** TERSE: ** Not all implicit flows are harmful *)

(** Not all implicit flows break noninterference though. For instance,
    in \CHAP{RelHoare} we saw a program that we proved to be
    noninterferent, even though it contains both an explicit and an
    implicit flow: *)

Definition secure_p2 :=
  <{ if Y = 0
     then X := Y (* <- harmless explicit flow *)
     else X := 0 (* <- harmless implicit flow *)
     end }>.

(** Intuitively, even if this program branches on the secret [Y], it
    always assigns the value [0] to [X], so no secret is
    leaked. Still, our type systems will reject programs containing
    any explicit or implicit flows, this one included. C'est la vie! *)

(* LATER: Can we also find the [secure_p2] above by testing? *)

(** * Type system for noninterference of expressions *)

(* HIDE: CH: The big duplication in expressions is awkward.  Is the
   typed version of Imp that got hidden in Types.v better? Maybe a
   little bit, but not for the good reasons: currently they drop some
   stuff there, instead of factoring things better. *)

(* HIDE: CH: Conceptually, would a typed version of Imp be a better base
   for this chapter? I was indeed hoping that Types.v would introduce
   a standard type system for Imp; otherwise it seems a bit funny to show
   them security typing for Imp without showing them standard typing
   for Imp. Whether the two are put together is bit orthogonal though.
   They may be connected if we add arrays for crypto constant-time?
   Managed to avoid it there too, for now, at the expense of
   duplicating the state in Imp with arrays. *)


(* INSTRUCTORS: Showed them a diagram a few times to keep them oriented
   about the different type systems and semantic properties:
   https://photos.app.goo.gl/yhKFTdear2KYdzEH8 *)

(* SOONER: Try to include this diagram in ASCII art *)

(** We will build a type system that prevents all explicit and
    implicit flows.

    But first, let's start with something simpler, a type system for
    arithmetic expressions: our typing judgement [P |-a- a \IN l]
    specifies the label [l] of an arithmetic expression [a] in terms
    of the labels of the variables read it reads.

    In particular, [P |-a- a \IN public] says that expression [a]
    only reads public variables, so it computes a public value.
    [P |-a- a \IN secret] says that expression [a] reads some secret
    variable, so it computes a value that may depend on secrets.

    Here are some examples:
    - For a variable [X] we just look up its label in P, so
      [P |-a- X \IN P X].
    - For a constant [n] the label is [public], so
      [P |-a n \IN public].
    - Given variable [X1] with label [l1] and variable [X2] with
      label [l2], what should be the label of [X1 + X2] though? *)

(* LATER: Seems that \in collides to something in QC, so switched to \IN *)

(** ** Combining labels *)

(** We need a way to combine the labels of two sub-expressions, which
    we call the _join_ (or least upper bound) of the two labels: *)

Definition join (l1 l2 : label) : label := l1 && l2.

(* This one is too simple to test, but still here it goes: *)
QuickCheck (forAll arbitrary (fun (l1:label) =>
            forAll arbitrary (fun (l2:label) =>
              join l1 l2 = join l2 l1 ?))).

(* TERSE: HIDEFROMHTML *)
Lemma join_commutative : forall {l1 l2},
  join l1 l2 = join l2 l1.
Proof. intros l1 l2. destruct l1; destruct l2; reflexivity. Qed.

Lemma join_public : forall {l1 l2},
  join l1 l2 = public -> l1 = public /\ l2 = public.
Proof. apply andb_prop. Qed.
(* TERSE: /HIDEFROMHTML *)

Lemma join_public_l : forall {l},
  join public l = l.
Proof. reflexivity. Qed.

(* TERSE: HIDEFROMHTML *)
Lemma join_public_r : forall {l},
  join l public = l.
Proof. intros l. rewrite join_commutative. reflexivity. Qed.
(* TERSE: /HIDEFROMHTML *)

Lemma join_secret_l : forall {l},
  join secret l = secret.
Proof. reflexivity. Qed.

(** TERSE: ** Typing of arithmetic expressions *)

(** [[[
                          -------------------                  (T_Num)
                          P |-a- n \IN public

                           -----------------                    (T_Id)
                           P |-a- X \IN P X

                  P |-a- a1 \IN l1    P |-a- a2 \IN l2
                  ------------------------------------        (T_Plus)
                      P |-a- a1+a2 \IN join l1 l2

                  P |-a- a1 \IN l1    P |-a- a2 \IN l2
                  ------------------------------------       (T_Minus)
                      P |-a- a1-a2 \IN join l1 l2

                  P |-a- a1 \IN l1    P |-a- a2 \IN l2
                  ------------------------------------        (T_Mult)
                      P |-a- a1*a2 \IN join l1 l2
]]]
*)

(** TERSE: ** *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P '|-a-' a \IN l" (at level 40).
(* TERSE: /HIDEFROMHTML *)

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

where "P '|-a-' a '\IN' l" := (aexp_has_label P a l).

(* Derive ArbitrarySizedSuchThat for (fun a => aexp_has_label P a l). *)
(* Derive DecOpt for (aexp_has_label P a l). *)
(* Error: Anomaly "Uncaught exception Failure("Internal QuickChick Error : Matching result type error")." *)
(* LATER: Unclear if this could be made to work; try to figure this out eventually.
   My initial experiments showed that the deriving mechanism is extremely flaky;
   basically it's hugely unlikely that one would naturally satisfy all the constraints,
   which are not documented anywhere (just terrible error messages). *)

Fixpoint label_of_aexp (P:pub_vars) (a:aexp) : label :=
  match a with
  | ANum n => public
  | AId X => apply P X
  | <{ a1 + a2 }>
  | <{ a1 - a2 }>
  | <{ a1 * a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  end.

Lemma label_of_aexp_sound : forall P a,
  P |-a- a \IN label_of_aexp P a.
Proof. intros P a. induction a; constructor; eauto. Qed.

Lemma label_of_aexp_unique : forall P a l,
  P |-a- a \IN l ->
  l = label_of_aexp P a.
Proof.
  intros P a l H. induction H; simpl in *;
  (repeat match goal with
    | [Heql : _ = _ |- _] => rewrite Heql in *
   end); eauto.
Qed.

(* The ;; notation didn't work with oneOf, probably related to monadic
   bind also using ;;. So I redefined the notation using ;;;. *)
Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Definition gen_pub_aexp_leaf (P : pub_vars) : G aexp :=
  oneOf (liftM ANum arbitrary ;;;
         (let pubs := filter (apply P) (map_dom (snd P)) in
         if seq.nilp pubs then []
         else [liftM AId (elems_ "X0"%string pubs)] ) ).

(* LATER: Really no way to check for list nilness in Coq standard
   library?  Searched quite a bit and it seems that no. Super strange.
   Above using a mathcomp function, [seq.nilp]. *)
(* Search (forall _, list _ -> bool). *)

Fixpoint gen_pub_aexp (sz:nat) (P:pub_vars) : G aexp :=
  match sz with
  | O => gen_pub_aexp_leaf P
  | S sz' =>
      freq [ (3, gen_pub_aexp_leaf P);
             (sz, liftM2 APlus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (sz, liftM2 AMinus (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (sz, liftM2 AMult (gen_pub_aexp sz' P) (gen_pub_aexp sz' P))]
  end.

Sample (P <- arbitrary;;
        a <- gen_pub_aexp 2 P;;
        ret (P, a)).

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
            forAll (gen_pub_aexp 2 P) (fun (a:aexp) =>
            label_of_aexp P a = public ?))).

(** TERSE: ** Noninterference by typing for arithmetic expressions *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
            forAll (gen_pub_aexp 2 P) (fun (a:aexp) =>
            forAll arbitrary (fun (s1:state) =>
            forAll (gen_pub_equiv P s1) (fun (s2:state) =>
            aeval s1 a = aeval s2 a ?))))).

(* SOONER: It would be great to also check that inserting a bug
   somewhere is found using mutants. *)

(* For now, checking that the previous two assertions don't hold for
   arbitrary aexps. *)

QuickChick (forAllShrink arbitrary shrink (fun (P:pub_vars) =>
            forAllShrink arbitrary shrink (fun (a:aexp) =>
            label_of_aexp P a = public ?))).

QuickChick (forAllShrink arbitrary shrink (fun (P:pub_vars) =>
            forAllShrink arbitrary shrink (fun (a:aexp) =>
            forAllShrink arbitrary shrink (fun (s1:state) =>
            forAllShrink (gen_pub_equiv P s1) (shrink_pub_equiv P) (fun (s2:state) =>
            aeval s1 a = aeval s2 a ?))))).

Theorem noninterferent_aexp : forall {P s1 s2 a},
  pub_equiv P s1 s2 ->
  P |-a- a \IN public ->
  aeval s1 a = aeval s2 a.
(* FOLD *)
Proof.
  intros P s1 s2 a Heq Ht. remember public as l.
  induction Ht; simpl.
  - reflexivity.
  - apply Heq. apply Heql.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
  - destruct (join_public Heql) as [H1 H2].
    rewrite (IHHt1 H1). rewrite (IHHt2 H2). reflexivity.
Qed.
(* /FOLD *)

(* HIDE *)
(* CH: Because of the lack of subtyping, not every expression is
       secret (top label), which seems a bit odd. Is it a problem?
       Since if it was we could fix it by changing T_Num.
       It's just a problem in reading the [\IN secret] judgement?
       It computes a secret value? *)
Lemma not_everything_secret :
  ~xpub |-a- ANum 42 \IN secret.
Proof. intro Hc. inversion Hc. Qed.

(* CH: Even in our simple setting we do need the [\IN secret] for
       assignments, so can't trivially simplify to [P |-pa- a], so a
       judgement that checks whether an expression is public?  *)
(* /HIDE *)

(** TERSE: ** Typing of Boolean expressions *)

(** [[[
                         ----------------------               (T_True)
                         P |-b- true \IN public

                         -----------------------             (T_False)
                         P |-b- false \IN public

                  P |-a- a1 \IN l1    P |-a- a2 \IN l2
                  ------------------------------------          (T_Eq)
                      P |-b- a1=a2 \IN join l1 l2

...

                             P |-b- b \IN l
                            ---------------                    (T_Not)
                            P |-b- ~b \IN l

                  P |-b- b1 \IN l1    P |-b- b2 \IN l2
                  ------------------------------------         (T_And)
                      P |-b- b1&&b2 \IN join l1 l2
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P '|-b-' b \IN l" (at level 40).

Inductive bexp_has_label (P:pub_vars) : bexp -> label -> Prop :=
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
(* TERSE: /HIDEFROMHTML *)

Fixpoint label_of_bexp (P:pub_vars) (a:bexp) : label :=
  match a with
  | <{ true }> | <{ false }> => public
  | <{ a1 = a2 }>
  | <{ a1 <> a2 }>
  | <{ a1 <= a2 }>
  | <{ a1 > a2 }> => join (label_of_aexp P a1) (label_of_aexp P a2)
  | <{ ~b }> => label_of_bexp P b
  | <{ b1 && b2 }> => join (label_of_bexp P b1) (label_of_bexp P b2)
  end.

Lemma label_of_bexp_sound : forall P b,
    P |-b- b \IN label_of_bexp P b.
Proof.
  intros P b. induction b; constructor;
    eauto using label_of_aexp_sound. Qed.

Lemma label_of_bexp_unique : forall P b l,
  P |-b- b \IN l ->
  l = label_of_bexp P b.
Proof.
  intros P a l H. induction H; simpl in *;
  (repeat match goal with
    | [H : _ |-a- _ \IN _ |- _] =>
        apply label_of_aexp_unique in H
    | [Heql : _ = _ |- _] => rewrite Heql in *
   end); eauto.
Qed.

Fixpoint gen_pub_bexp (sz:nat) (P:pub_vars) : G bexp :=
  match sz with
  | O => elems [BTrue; BFalse]
  | S sz' =>
      freq [ (1, ret BTrue);
             (1, ret BFalse);
             (1, liftM2 BEq (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (1, liftM2 BNeq (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (1, liftM2 BLe (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (1, liftM2 BGt (gen_pub_aexp sz' P) (gen_pub_aexp sz' P));
             (sz, liftM BNot (gen_pub_bexp sz' P));
             (sz, liftM2 BAnd (gen_pub_bexp sz' P) (gen_pub_bexp sz' P))]
  end.

Sample (P <- arbitrary;;
        b <- gen_pub_bexp 2 P;;
        ret (P, b)).

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
            forAll (gen_pub_bexp 2 P) (fun (b:bexp) =>
            label_of_bexp P b = public ?))).

(** TERSE: ** Noninterference by typing for Boolean expressions *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
            forAll (gen_pub_bexp 2 P) (fun (b:bexp) =>
            forAll arbitrary (fun (s1:state) =>
            forAll (gen_pub_equiv P s1) (fun (s2:state) =>
            beval s1 b = beval s2 b ?))))).

(* SOONER: It would be great to also check that inserting a bug
   somewhere is found using mutants. *)

(* For now, checking that the previous two assertions don't hold for
   arbitrary bexps. *)

QuickChick (forAllShrink arbitrary shrink (fun (P:pub_vars) =>
            forAllShrink arbitrary shrink (fun (b:bexp) =>
            label_of_bexp P b = public ?))).

QuickChick (forAllShrink arbitrary shrink (fun (P:pub_vars) =>
            forAllShrink arbitrary shrink (fun (b:bexp) =>
            forAllShrink arbitrary shrink (fun (s1:state) =>
            forAllShrink (gen_pub_equiv P s1) (shrink_pub_equiv P) (fun (s2:state) =>
            beval s1 b = beval s2 b ?))))).

Theorem noninterferent_bexp : forall {P s1 s2 b},
  pub_equiv P s1 s2 ->
  P |-b- b \IN public ->
  beval s1 b = beval s2 b.
(* FOLD *)
Proof.
  intros P s1 s2 b Heq Ht. remember public as l.
  induction Ht; simpl; try reflexivity;
    try (destruct (join_public Heql) as [H1 H2];
         rewrite H1 in *; rewrite H2 in *).
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (noninterferent_aexp Heq H).
    rewrite (noninterferent_aexp Heq H0).
    reflexivity.
  - rewrite (IHHt Heql). reflexivity.
  - rewrite (IHHt1 Logic.eq_refl).
    rewrite (IHHt2 Logic.eq_refl). reflexivity.
Qed.
(* /FOLD *)

(* For producing implicit flows as counterexamples; let's start by
   generating assignments that are never explicit flows: *)

Definition gen_secure_asgn (P:pub_vars) : G com :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  a <- (if apply P x then gen_pub_aexp 1 P else arbitrary);;
  ret <{ x := a }>.

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll (gen_secure_asgn P) (fun (c : com) =>
            forAll arbitrary (fun (s1 : state) =>
            forAll (gen_pub_equiv P s1) (fun (s2 : state) =>
            pub_equivb P (ceval_fun_no_while s1 c)
                         (ceval_fun_no_while s2 c)))))).

(* We write our command generator more generally than what's needed
   here, so that we can also reuse below: *)

Fixpoint gen_com (gen_asgn : pub_vars -> G com)
                 (gen_bexp : pub_vars -> G bexp)
                 (sz:nat) (P:pub_vars) : G com :=
  match sz with
  | O => oneOf [ret CSkip; gen_asgn P]
  | S sz' =>
      freq [ (1, ret CSkip);
             (sz, gen_asgn P);
             (sz, liftM2 CSeq (gen_com gen_asgn gen_bexp sz' P)
                              (gen_com gen_asgn gen_bexp sz' P));
             (sz, liftM3 CIf (gen_bexp P) (gen_com gen_asgn gen_bexp sz' P)
                                          (gen_com gen_asgn gen_bexp sz' P));
             (sz, liftM2 CWhile (gen_bexp P) (gen_com gen_asgn gen_bexp sz' P))]
  end.

Definition gen_no_explicit_flows := gen_com gen_secure_asgn (fun _ => arbitrary).

(* This produces implicit flows as counterexamples: *)
QuickChick (forAllShrink arbitrary shrink (fun (P : pub_vars) =>
            forAllShrink (gen_no_explicit_flows 2 P) shrink (fun (c : com) =>
            forAllShrink arbitrary shrink (fun (s1 : state) =>
            forAllShrink (gen_pub_equiv P s1) (shrink_pub_equiv P) (fun (s2 : state) =>
            pub_equivb P (ceval_fun_no_while s1 c)
                         (ceval_fun_no_while s2 c)))))).

(** * Restrictive type system prohibiting branching on secrets *)

(** For commands, we start with a simple type system that doesn't
    allow any branching on secrets, which prevents all implicit flows. *)

(** For preventing explicit flows when typing assignments, we need to
    define when it is okay for information to flow from an expression
    with label [l1] to a variable with label [l1]. *)

Definition can_flow (l1 l2 : label) : bool := l1 || negb l2.

(** In particular, we disallow the value of secret expressions to be
    assigned to public variables. *)

Lemma cannot_flow_secret_public : can_flow secret public = false.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(** We allow public information to flow everywhere, and secret
    information to flow to secret variables: *)

Lemma can_flow_public : forall l, can_flow public l = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)
Lemma can_flow_secret : can_flow secret secret = true.
(* FOLD *)
Proof. reflexivity. Qed.
(* /FOLD *)

(* TERSE: HIDEFROMHTML *)
Lemma can_flow_refl : forall l,
  can_flow l l = true.
Proof. intros [|]; reflexivity. Qed.

Lemma can_flow_trans : forall l1 l2 l3,
  can_flow l1 l2 = true ->
  can_flow l2 l3 = true ->
  can_flow l1 l3 = true.
Proof. intros l1 l2 l3 H12 H23.
  destruct l1; destruct l2; simpl in *; auto. Qed.

Lemma can_flow_join_1 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l1 l = true.
Proof. intros l1 l2 l. destruct l1; [reflexivity | auto ]. Qed.

Lemma can_flow_join_2 : forall l1 l2 l,
  can_flow (join l1 l2) l = true ->
  can_flow l2 l = true.
Proof. intros l1 l2 l. destruct l1; auto. destruct l2; auto. Qed.

Lemma can_flow_join_l : forall l1 l2 l,
  can_flow l1 l = true ->
  can_flow l2 l = true ->
  can_flow (join l1 l2) l = true.
Proof. intros l1 l2 l H1 H2. destruct l1; simpl in *; auto. Qed.

Lemma can_flow_join_r1 : forall l l1 l2,
  can_flow l l1 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto. Qed.

Lemma can_flow_join_r2 : forall l l1 l2,
  can_flow l l2 = true ->
  can_flow l (join l1 l2) = true.
Proof. intros l l1 l2 H. destruct l; destruct l1; simpl in *; auto. Qed.
(* TERSE: /HIDEFROMHTML *)

(** TERSE: ** IFC typing of commands ([pc_well_typed] relation) *)

(** [[[
                            ------------                    (PCWT_Skip)
                            P |-pc- skip

             P |-a- a \IN l    can_flow l (P X) = true
             -----------------------------------------      (PCWT_Asgn)
                           P |-pc- X := a

                      P |-pc- c1    P |-pc- c2
                      ------------------------               (PCWT_Seq)
                            P |-pc- c1;c2

           P |-b- b \IN public    P |-pc- c1    P |-pc- c2
           -----------------------------------------------    (PCWT_If)
                      P |-pc- if b then c1 else c2

                  P |-b- b \IN public    P |-pc- c
                  --------------------------------         (PCWT_While)
                    P |-pc- while b then c end
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P '|-pc-' c" (at level 40).

Inductive pc_well_typed (P:pub_vars) : com -> Prop :=
  | PCWT_Com :
      P |-pc- <{ skip }>
  | PCWT_Asgn : forall X a l,
      P |-a- a \IN l ->
      can_flow l (apply P X) = true ->
      P |-pc- <{ X := a }>
  | PCWT_Seq : forall c1 c2,
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ c1 ; c2 }>
  | PCWT_If : forall b c1 c2,
      P |-b- b \IN public ->
      P |-pc- c1 ->
      P |-pc- c2 ->
      P |-pc- <{ if b then c1 else c2 end }>
  | PCWT_While : forall b c1,
      P |-b- b \IN public ->
      P |-pc- c1 ->
      P |-pc- <{ while b do c1 end }>

where "P '|-pc-' c" := (pc_well_typed P c).
(* TERSE: /HIDEFROMHTML *)

Fixpoint pc_typechecker (P:pub_vars) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (label_of_aexp P a) (apply P X)
  | <{ c1 ; c2 }> => pc_typechecker P c1 && pc_typechecker P c2
  | <{ if b then c1 else c2 end }> =>
      Bool.eqb (label_of_bexp P b) public &&
      pc_typechecker P c1 && pc_typechecker P c2
  | <{ while b do c1 end }> =>
      Bool.eqb (label_of_bexp P b) public && pc_typechecker P c1
  end.

Lemma pc_typechecker_sound : forall P c,
  pc_typechecker P c = true ->
  P |-pc- c.
(* FOLD *)
Proof.
  intros P c. induction c; simpl in *; econstructor; 
    try rewrite andb_true_iff in *; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound. 
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; try tauto.
    destruct H1 as [H11 H12]. apply Bool.eqb_prop in H11.
    rewrite <- H11. apply label_of_bexp_sound.
  - destruct H as [H1 H2]. rewrite andb_true_iff in H1; tauto.
  - destruct H as [H1 H2]. apply Bool.eqb_prop in H1.
    rewrite <- H1. apply label_of_bexp_sound.
Qed.
(* /FOLD *)

Lemma pc_typechecker_complete : forall P c,
  pc_typechecker P c = false ->
  ~P |-pc- c.
(* FOLD *)
Proof.
  intros P c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *;
    try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; eauto. rewrite andb_false_iff in H.
    destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
  - destruct H; eauto. rewrite eqb_false_iff in H.
    apply label_of_bexp_unique in H0. congruence.
Qed.
(* /FOLD *)

(** ** Secure program that is [pc_well_typed]: *)

Example swt_secure_com :
  xpub |-pc- <{ X := X+1;  (* check: can_flow public public (OK!)  *)
               Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
             }>.
Proof. apply pc_typechecker_sound. reflexivity. Qed.

(** ** Explicit flow prevented by [pc_well_typed]: *)

Example not_swt_insecure_com1 :
  ~ xpub |-pc- <{ X := Y+1;  (* check: can_flow secret public (FAILS!) *)
                 Y := X+Y*2 (* check: can_flow secret secret (OK!)  *)
               }>.
Proof. apply pc_typechecker_complete. reflexivity. Qed.

(** ** Implicit flow prevented by [pc_well_typed]: *)

Example not_swt_insecure_com2 :
  ~ xpub |-pc- <{ if Y=0  (* check: P |-b- Y=0 \IN public (FAILS!) *)
                 then Y := 42
                 else X := X+1 (* <- bad implicit flow! *)
                 end }>.
Proof. apply pc_typechecker_complete. reflexivity. Qed.

(** SOONER: Add an example of a non-interferent program that is rejected? *)

(** TERSE: ** *)

(** We show that [pc_well_typed] commands are [noninterferent]. *)

Definition gen_pc_well_typed := gen_com gen_secure_asgn (gen_pub_bexp 2).

(* We first validate that our generator produces well-typed terms *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_pc_well_typed 1 P) (fun (c:com) =>
             pc_typechecker P c)))).

(* Then we use this generator to test that well-typed terms are indeed
   noninterferent: *)

QuickChick (forAll arbitrary (fun (P : pub_vars) =>
            forAll (gen_pc_well_typed 1 P) (fun (c : com) =>
            forAll arbitrary (fun (s1 : state) =>
            forAll (gen_pub_equiv P s1) (fun (s2 : state) =>
            pub_equivb P (ceval_fun_no_while s1 c)
                         (ceval_fun_no_while s2 c)))))).

Theorem pc_well_typed_noninterferent : forall P c,
  P |-pc- c ->
  noninterferent P c.
(* FOLD *)
Proof.
  intros P c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  induction Heval1; intros s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - assumption.
  - intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      unfold can_flow in H8. apply orb_prop in H8. destruct H8 as [Hl | Hx].
      * rewrite Hl in *. apply (noninterferent_aexp Heq H7).
      * subst. rewrite Hy in Hx. discriminate Hx.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
  - eapply IHHeval1; eassumption.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - rewrite (noninterferent_bexp Heq H10) in H.
    rewrite H in H5. discriminate H5.
  - eapply IHHeval1; eassumption.
  - assumption.
  - rewrite (noninterferent_bexp Heq H9) in H.
    rewrite H in H2. discriminate H2.
  - rewrite (noninterferent_bexp Heq H7) in H.
    rewrite H in H4. discriminate H4.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
Qed.
(* /FOLD *)

(** Remember the definition of [noninterferent] is as follows:
<<
forall s1 s2 s1' s2',
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1' ->
  s2 =[ c ]=> s2' ->
  pub_equiv P s1' s2'.
>>

   The main intuition is that the two executions will proceed "in
   lockstep", because all the branch conditions are enforced to be
   public, so they will execute to the same Boolean in both executions. *)

(** FULL: The proof is by induction on [s1 =[ c ]=> s1'] and inversion
    on [s2 =[ c ]=> s2'] and [P |-pc- c]. Here is a sketch of the two
    most interesting cases:

    - In the conditional case we have that [c] is [if b then c1 else c2],
      [P |-pc- c1], [P |-pc- c2], and [P |-b- b \IN public]. Given this
      last fact we can apply noninterference of boolean expressions to
      show that [beval st1 b = beval st2 b]. If they are both [true],
      we use the induction hypothesis for [c1], and if they are both
      false we use the induction hypothesis for [c2] to conclude.

    - In the assignment case we have that [c] is [X := a],
      [P |-a- a \IN l], and [can_flow l (P X) = true], which expands out
      to [l == public \/ P X == secret].

      If [l == public] then by noninterference of arithmetic
      expressions then [aeval st1 a = aeval s2 a], so we are
      assigning the same value to X, which leads to public equivalent
      final states (since the initial states were public equivalent).

      If [P X == secret] then the value of [X] doesn't matter
      for determining whether the final states are [pub_equiv]. *)

(** ** [pc_well_typed] too strong for noninterference *)

(** While we have just proved that [pc_well_typed] implies
    noninterference, this is too strong a restriction for just
    noninterference. For instance, the following program contains no
    explicit flows and no implicit flows, so it is intuitively
    noninterferent, yet it is still rejected by the type system just
    because it branches on a secret: *)

Example not_typechecks_noninterferent_com :
  pc_typechecker xpub <{ if Y=0 then Z := 0 else skip end }> = false.
Proof. reflexivity. Qed.

Example not_swt_noninterferent_com :
  ~ xpub |-pc- <{ if Y=0 (* check: P |-b- Y=0 \IN public (fails!) *)
                 then Z := 0
                 else skip
                 end }>.
(* FOLD *)
Proof.
  intros contra.
  inversion contra; subst; clear contra.
  inversion H2; subst; clear H2.
  destruct l1, l2; simpl in H1; try discriminate.
  inversion H5.
Qed.
(* /FOLD *)

Example not_swt_noninterferent_com_is_noninterferent:
  noninterferent xpub <{ if Y=0
                         then Z := 0
                         else skip
                         end }>.
(* FOLD *)
Proof.
  unfold noninterferent.
  intros s1 s2 s1' s2' H red1 red2.
  inversion red1; inversion red2; subst; clear red1 red2.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px.
    destruct (String.eqb_spec x Z); subst.
    + discriminate.
    + rewrite !t_update_neq; auto.
  - inversion H6; subst; clear H6.
    inversion H13; subst; clear H13.
    intros x Px. eapply H; eauto.
Qed.
(* /FOLD *)

(** SOONER: The proof the command is noninterferent is a bit repetitive! *)

(** We will later show that [pc_well_typed] enforces a security
    notion called program counter security, which prevents some
    side-channel attacks and which also serves as the base for
    cryptographic constant-time. *)

(** * IFC type system allowing branching on secrets *)

(** We now instead extend this to a more permissive type system for
    noninterference in which we do allow branching on secrets.

    Now to prevent implicit flows we need to track whether we have
    branched on secrets. We do this with a _program counter_ ([pc])
    label, which records the labels of the branches we have taken at
    the current point in the execution (joined together). *)

(** [[[
                      ----------------                      (WT_Skip)
                      P ,, pc |-- skip

       P |-a- a \IN l   can_flow (join pc l) (P X) = true
       --------------------------------------------------   (WT_Asgn)
                     P ,, pc |-- X := a

                P ,, pc |-- c1    P ,, pc |-- c2
                --------------------------------             (WT_Seq)
                      P ,, pc |-- c1;c2

           P |-b- b \IN l    P ,, join pc l |-- c1
                             P ,, join pc l |-- c2
           ---------------------------------------            (WT_If)
                P ,, pc |-- if b then c1 else c2

              P |-b- b \IN l    P ,, join pc l |-- c
              --------------------------------------       (WT_While)
                P ,, pc |-- while b then c end
]]]
*)
(* SOONER: center these *)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P ',,' pc '|--' c" (at level 40).

Inductive well_typed (P:pub_vars) : label -> com -> Prop :=
  | WT_Com : forall pc,
      P ,, pc |-- <{ skip }>
  | WT_Asgn : forall pc X a l,
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P X) = true ->
      P ,, pc |-- <{ X := a }>
  | WT_Seq : forall pc c1 c2,
      P ,, pc |-- c1 ->
      P ,, pc |-- c2 ->
      P ,, pc |-- <{ c1 ; c2 }>
  | WT_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P ,, (join pc l) |-- c1 ->
      P ,, (join pc l) |-- c2 ->
      P ,, pc |-- <{ if b then c1 else c2 end }>
  | WT_While : forall pc b l c1,
      P |-b- b \IN l ->
      P ,, (join pc l) |-- c1 ->
      P ,, pc |-- <{ while b do c1 end }>

where "P ',,' pc '|--' c" := (well_typed P pc c).
(* TERSE: /HIDEFROMHTML *)

(* LATER: Seems that ;; was colliding with bind notation,
   so changed to ,, for now. *)

Fixpoint wt_typechecker (P:pub_vars) (pc:label) (c:com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ X := a }> => can_flow (join pc (label_of_aexp P a)) (apply P X)
  | <{ c1 ; c2 }> => wt_typechecker P pc c1 && wt_typechecker P pc c2
  | <{ if b then c1 else c2 end }> =>
      wt_typechecker P (join pc (label_of_bexp P b)) c1 &&
      wt_typechecker P (join pc (label_of_bexp P b)) c2
  | <{ while b do c1 end }> =>
      wt_typechecker P (join pc (label_of_bexp P b)) c1
  end.

Lemma wt_typechecker_sound : forall P pc c,
  wt_typechecker P pc c = true ->
  P ,, pc |-- c.
(* FOLD *)
Proof.
  intros P pc c. generalize dependent pc.
  induction c; intros pc H; simpl in *; econstructor; 
    try rewrite andb_true_iff in *;
    try destruct H as [H1 H2]; try tauto;
    eauto using label_of_aexp_sound, label_of_bexp_sound.
Qed.
(* /FOLD *)

Lemma wt_typechecker_complete : forall P pc c,
  wt_typechecker P pc c = false ->
  ~ P ,, pc |-- c.
(* FOLD *)
Proof.
  intros P pc c H Hc. induction Hc; simpl in *;
    try rewrite andb_false_iff in *; try tauto; try congruence.
  - apply label_of_aexp_unique in H0.
    rewrite H0 in *. congruence.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
  - destruct H; apply label_of_bexp_unique in H0; subst; eauto.
Qed.
(* /FOLD *)

(** TERSE: ** *)

(** With this more permissive type system we can accept more
    noninterferent programs that were rejected by [pc_well_typed]. *)

Example wt_noninterferent_com :
  xpub ,, public |--
    <{ if Y=0 (* raises pc label from public to secret *)
       then Z := 0 (* check: [can_flow secret secret] (OK!) *)
       else skip
       end }>.
Proof. apply wt_typechecker_sound. reflexivity. Qed.

(** And we still prevent implicit flows: *)

Example not_wt_insecure_com2 :
  ~ xpub ,, public |--
    <{ if Y=0  (* raises pc label from public to secret *)
       then Y := 42
       else X := X+1 (* check: [can_flow secret public] (FAILS!)  *)
       end }>.
Proof. apply wt_typechecker_complete. reflexivity. Qed.


Definition gen_asgn_in_ctx (gen_asgn : pub_vars -> G com)
    (pc:label) (P:pub_vars) : G com :=
  if pc then gen_asgn P
  else
    let privs := filter (fun x => negb (apply P x))
                        (map_dom (snd P)) in
    match privs with
    | x0 :: _ =>
      x <- elems_ x0 privs;;
      a <- arbitrary;;
      ret <{ x := a }>
    | [] => ret <{ skip }>
      (* generates skip if there no secure assignements possible *)
    end.

Fixpoint gen_com_rec (gen_asgn : pub_vars -> G com)
                     (sz:nat) (P:pub_vars) : G com :=
  match sz with
  | O => oneOf [ret CSkip ; gen_asgn P ]
  | S sz' =>
      freq [ (1, ret CSkip);
             (sz, gen_asgn P);
             (sz, liftM2 CSeq (gen_com_rec gen_asgn sz' P)
                              (gen_com_rec gen_asgn sz' P));
             (sz, b <- arbitrary;;
                  liftM3 CIf (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b)) sz' P)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b)) sz' P));
             (sz, b <- arbitrary;;
                  liftM2 CWhile (ret b)
                    (gen_com_rec (gen_asgn_in_ctx gen_asgn (label_of_bexp P b)) sz' P))]
  end.

Definition gen_wt_com := gen_com_rec gen_secure_asgn.

(* We first validate that our generator produces well-typed terms *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com 1 P) (fun (c:com) =>
             wt_typechecker P public c)))).

(* TERSE: HIDEFROMHTML *)

(* For the next lemmas we also need to generate commands that are
   well-typed with pc=secret: *)

Definition gen_wt_com_pc_secret :=
  gen_com_rec (gen_asgn_in_ctx gen_secure_asgn secret).

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com_pc_secret 1 P) (fun (c:com) =>
             wt_typechecker P secret c)))).

(* With this we can test the weaken_pc lemma below *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com_pc_secret 1 P) (fun (c:com) =>
             wt_typechecker P public c)))).

Lemma weaken_pc : forall {P pc1 pc2 c},
  P,, pc1 |-- c ->
  can_flow pc2 pc1 = true->
  P,, pc2 |-- c.
Proof.
  intros P pc1 pc2 c H. generalize dependent pc2.
  induction H; subst; intros pc2 Hcan_flow.
  - constructor.
  - econstructor; try eassumption. apply can_flow_join_l.
    + apply can_flow_join_1 in H0. eapply can_flow_trans; eassumption.
    + apply can_flow_join_2 in H0. assumption.
  - constructor; auto.
  - econstructor; try eassumption.
    + apply IHwell_typed1. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
    + apply IHwell_typed2. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
  - econstructor; try eassumption. apply IHwell_typed. apply can_flow_join_l.
      * apply can_flow_join_r1. assumption.
      * apply can_flow_join_r2. apply can_flow_refl.
Qed.
(* TERSE: /HIDEFROMHTML *)

(** ** Dealing with unsynchronized executions running different code *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com_pc_secret 1 P) (fun (c:com) =>
           (forAll arbitrary (fun (s:state) =>
             pub_equivb P s (ceval_fun_no_while s c))))))).

Lemma secret_run : forall {P c s s'},
  P,, secret |-- c ->
  s =[ c ]=> s' ->
  pub_equiv P s s'.
(* FOLD *)
Proof.
  intros P c s s' Hwt Heval. induction Heval; inversion Hwt; subst.
  - apply pub_equiv_refl.
  - intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + subst. rewrite join_secret_l in H4. rewrite Hy in H4. discriminate H4.
    + rewrite t_update_neq; auto.
  - eapply pub_equiv_trans; eauto.
  - eauto.
  - eauto.
  - apply pub_equiv_refl.
  - eapply pub_equiv_trans; eauto.
Qed.
(* /FOLD *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com_pc_secret 1 P) (fun (c1:com) =>
           (forAll (gen_wt_com_pc_secret 1 P) (fun (c2:com) =>
           (forAll arbitrary (fun (s1:state) =>
           (forAll (gen_pub_equiv P s1) (fun (s2:state) =>
             pub_equivb P (ceval_fun_no_while s1 c1)
                          (ceval_fun_no_while s2 c2))))))))))).

Corollary different_code : forall P c1 c2 s1 s2 s1' s2',
  P,, secret |-- c1 ->
  P,, secret |-- c2 ->
  pub_equiv P s1 s2 ->
  s1 =[ c1 ]=> s1' ->
  s2 =[ c2 ]=> s2' ->
  pub_equiv P s1' s2'.
(* FOLD *)
Proof.
  intros P c1 c2 s1 s2 s1' s2' Hwt1 Hwt2 Hequiv Heval1 Heval2.
  eapply secret_run in Hwt1; [| eassumption].
  eapply secret_run in Hwt2; [| eassumption].
  apply pub_equiv_sym in Hwt1.
  eapply pub_equiv_trans; try eassumption.
  eapply pub_equiv_trans; eassumption.
Qed.
(* /FOLD *)

(** ** We show that [well_typed] commands are [noninterferent]. *)

QuickChick (forAll arbitrary (fun (P:pub_vars) =>
           (forAll (gen_wt_com 1 P) (fun (c:com) =>
           (forAll arbitrary (fun (s1:state) =>
           (forAll (gen_pub_equiv P s1) (fun (s2:state) =>
             pub_equivb P (ceval_fun_no_while s1 c)
                          (ceval_fun_no_while s2 c))))))))).

Theorem well_typed_noninterferent : forall P c,
  P,, public |-- c ->
  noninterferent P c.
(* FOLD *)
Proof.
  intros P c Hwt s1 s2 s1' s2' Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  induction Heval1; intros s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - assumption.
  - intros y Hy. destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + rewrite Hxy. do 2 rewrite t_update_eq.
      unfold can_flow in H9. rewrite join_public_l in H9.
      apply orb_prop in H9. destruct H9 as [Hl | Hx].
      * rewrite Hl in *. apply (noninterferent_aexp Heq H8).
      * subst. rewrite Hy in Hx. discriminate Hx.
    + do 2 rewrite (t_update_neq _ _ _ _ _ Hxy).
      apply Heq. apply Hy.
  - eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; eassumption.
  - (* if true-true *) rewrite join_public_l in *.
    eapply IHHeval1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
  - (* if true-false *) rewrite join_public_l in *. destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + eapply different_code with (c1:=c1) (c2:=c2); eassumption.
  - (* if false-true *) rewrite join_public_l in *. destruct l.
    + rewrite (noninterferent_bexp Heq H11) in H.
      rewrite H in H5. discriminate H5.
    + eapply different_code with (c1:=c2) (c2:=c1); eassumption.
  - (* if false-false *) rewrite join_public_l in *.
    eapply IHHeval1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
  - (* while false-false *) assumption.
  - (* while false-true *) rewrite join_public_l in *. destruct l.
    + rewrite (noninterferent_bexp Heq H10) in H.
      rewrite H in H2. discriminate H2.
    + eapply different_code with (c1:=<{skip}>) (c2:=<{c;while b do c end}>);
        repeat (try eassumption; try econstructor).
  - (* while true-false *) rewrite join_public_l in *. destruct l.
    + rewrite (noninterferent_bexp Heq H8) in H.
      rewrite H in H4. discriminate H4.
    + eapply different_code with (c1:=<{c;while b do c end}>) (c2:=<{skip}>);
        repeat (try eassumption; try econstructor).
  - (* while true-true *) rewrite join_public_l in *.
    eapply IHHeval1_2; try eassumption. eapply IHHeval1_1; try eassumption.
    eapply weaken_pc; try eassumption. apply can_flow_public.
Qed.
(* /FOLD *)

(** The noninterference proof is still relatively simple, since the
    cases in which we take different branches based on secret
    information are all handled by the [different_code] lemma.

    Another key ingredient for having a simple noninterference proof
    is working with a big-step semantics. *)

(** * Type system for termination-sensitive noninterference *)

(** The noninterference notion we used above was "termination
    insensitive". If we prevent loop conditions depending on secrets
    we can actually enforce termination-sensitive noninterference
    (TSNI), which we defined in \CHAP{Noninterference} as follows: *)

Definition tsni P c :=
  forall s1 s2 s1',
  s1 =[ c ]=> s1' ->
  pub_equiv P s1 s2 ->
  (exists s2', s2 =[ c ]=> s2' /\ pub_equiv P s1' s2').

(** We could prove that [pc_well_typed] enforces TSNI, but that
    typing relation is too restrictive, since for TSNI we can allow
    if-then-else conditions to depend on secrets. So we define a new
    type system that only prevents _loop_ conditions to depend on secrets. *)

(** ** We just need to update the while rule of [well_typed]: *)

(** Old rule for noninterference:
[[[
              P |-b- b \IN l    P ,, join pc l |-- c
              --------------------------------------       (WT_While)
                P ,, pc |-- while b then c end
]]]

    New rule for termination-sensitive noninterference:
[[[
          P |-b- b \IN public    P ,, public |-ts- c
          ------------------------------------------       (TS_While)
             P ,, public |-ts- while b then c end
]]]

   Beyond requiring the label of [b] to be [public], we also require
   that once one branches on secrets with if-then-else
   (i.e. pc=secret) no while loops are allowed.
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation "P ',,' pc '|-ts-' c" (at level 40).

Inductive ts_well_typed (P:pub_vars) : label -> com -> Prop :=
  | TS_Com : forall pc,
      P,, pc |-ts- <{ skip }>
  | TS_Asgn : forall pc X a l,
      P |-a- a \IN l ->
      can_flow (join pc l) (apply P X) = true ->
      P,, pc |-ts- <{ X := a }>
  | TS_Seq : forall pc c1 c2,
      P,, pc |-ts- c1 ->
      P,, pc |-ts- c2 ->
      P,, pc |-ts- <{ c1 ; c2 }>
  | TS_If : forall pc b l c1 c2,
      P |-b- b \IN l ->
      P,, (join pc l) |-ts- c1 ->
      P,, (join pc l) |-ts- c2 ->
      P,, pc |-ts- <{ if b then c1 else c2 end }>
  | TS_While : forall b c1,
      P |-b- b \IN public -> (* <-- NEW *)
      P,, public |-ts- c1 -> (* <-- ONLY pc=public *)
      P,, public |-ts- <{ while b do c1 end }>

where "P ',,' pc '|-ts-' c" := (ts_well_typed P pc c).
(* TERSE: /HIDEFROMHTML *)

(** ** We prove that [ts_well_typed] enforces TSNI. *)

(** For this we show that [ts_well_typed] implies [well_typed], so
    by our previous theorem also [noninterference].

    Then we show that [P,, secret |-ts- c] implies termination.
    
    Then we show that [ts_well_typed] implies equitermination, which
    together with noninterference implies termination-sensitive noninterference.
 *)

(* SOONER: CH: Maybe worth making the TSNI = NI + equitermination
   split more formal. It may help for keeping equitermination around
   also for [pc_well_typed] and [ct_well_typed]. In fact, could also
   update the diagram to separate semantic security about states (NI)
   from semantic security about termination (equitermination). *)

(* TERSE: HIDEFROMHTML *)
Theorem ts_well_typed_well_typed : forall P c pc,
  P,, pc |-ts- c ->
  P,, pc |-- c.
Proof.
  intros P c pc H. induction H; econstructor; eassumption.
Qed.

Theorem ts_well_typed_noninterferent : forall P c,
  P,, public |-ts- c ->
  noninterferent P c.
Proof.
  intros P c H. apply well_typed_noninterferent.
  apply ts_well_typed_well_typed. apply H.
Qed.

Lemma ts_secret_run_terminating : forall {P c s},
  P,, secret |-ts- c ->
  exists s', s =[ c ]=> s'.
Proof.
  intros P c s Hwt. remember secret as l.
  generalize dependent s. induction Hwt; intro s.
  - eexists. econstructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHwt1 Heql s) as  [s' IH1].
    destruct (IHHwt2 Heql s') as [s''IH2]. eexists. econstructor; eassumption.
  - rewrite Heql in *. rewrite join_secret_l in *.
    destruct (IHHwt1 Logic.eq_refl s) as [s1 IH1].
    destruct (IHHwt2 Logic.eq_refl s) as [s2 IH2].
    destruct (beval s b) eqn:Heq; eexists; econstructor; eassumption.
  - discriminate Heql.
Qed.

Theorem ts_well_typed_equitermination : forall {P c s1 s2 s1'},
  P,, public |-ts- c ->
  s1 =[ c ]=> s1' ->
  pub_equiv P s1 s2 ->
  exists s2', s2 =[ c ]=> s2'.
Proof.
  intros P C s1 s2 s1' Hwt Heval. generalize dependent s2.
  induction Heval; intros s2 Heq; inversion Hwt; subst.
  - eexists. constructor.
  - eexists. econstructor. reflexivity.
  - destruct (IHHeval1 H2 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv P st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 H3 _ Heq') as [s2'' IH2].
    eexists. econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H5 _ Heq) as [s2' IH1].
      eexists. apply E_IfTrue; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - rewrite join_public_l in *. destruct l.
    + destruct (IHHeval H6 _ Heq) as [s2' IH1].
      eexists. apply E_IfFalse; [ | eassumption ].
      * eapply noninterferent_bexp in Heq; [ | eassumption ]. congruence.
    + eapply ts_secret_run_terminating in H5. destruct H5 as [s1' H5].
      eapply ts_secret_run_terminating in H6. destruct H6 as [s2' H6].
      destruct (beval s2 b) eqn:Heq2; eexists; econstructor; eassumption.
  - eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. apply E_WhileFalse. congruence.
  - destruct (IHHeval1 H3 _ Heq) as [s2' IH1].
    assert (Heq' : pub_equiv P st' s2').
    { eapply ts_well_typed_noninterferent;
        [ | eassumption | eassumption | eassumption]. assumption. }
    destruct (IHHeval2 Hwt _ Heq') as [s2'' IH2].
    eapply noninterferent_bexp in Heq; [ | eassumption ].
    eexists. eapply E_WhileTrue; try congruence; eassumption.
Qed.
(* TERSE: /HIDEFROMHTML *)

Corollary ts_well_typed_tsni : forall P c,
  P,, public |-ts- c ->
  tsni P c.
(* FOLD *)
Proof.
  intros P c Hwt s1 s2 s1' Heval1 Heq.
  destruct (ts_well_typed_equitermination Hwt Heval1 Heq) as [s2' Heval2].
  exists s2'. split; [assumption| ].
  eapply ts_well_typed_noninterferent; eassumption.
Qed.
(* /FOLD *)

(** * Program counter security *)

(** Especially for cryptographic code one is also worried about
    side-channel attacks, in which secrets are for instance leaked via
    the execution time of the program. For instance, most processors
    have instruction caches, which make executing cached instructions
    faster than non-cached ones.

    To prevent such attacks, cryptographic code is normally written
    without branching on any secrets. To formalize this we introduce a
    new security notion called _program counter security_, which
    considers the program's branching visible to the attacker. More
    precisely, we instrument the operational semantics of [Imp] to
    also record the control-flow decisions of the program. *)

Definition branches := list bool.

(** ** Instrumented semantics with branches *)
(**
[[[
                     ---------------------                         (E_Skip)
                     st =[ skip ]=> st, []

                       aeval st a = n
               -----------------------------------                 (E_Asgn)
               st =[ x := a ]=> (x !-> n ; st), []

      st  =[ c1 ]=> st', bs1   st' =[ c2 ]=> st'', bs2
      ------------------------------------------------              (E_Seq)
               st =[ c1;c2 ]=> st'', (bs1++bs2)

            beval st b = true     st =[ c1 ]=> st', bs1
        -------------------------------------------------        (E_IfTrue)
        st =[ if b then c1 else c2 end ]=> st', true::bs1

            beval st b = false    st =[ c2 ]=> st', bs2
       --------------------------------------------------       (E_IfFalse)
       st =[ if b then c1 else c2 end ]=> st', false::bs2

  st =[ if b then c; while b do c end else skip end ]=> st, os
  ------------------------------------------------------------    (E_While)
            st =[ while b do c end ]=> st, os
]]]
*)

(* TERSE: HIDEFROMHTML *)
Reserved Notation
         "st '=[' c ']=>' st' , bs"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive pceval : com -> state -> state -> branches -> Prop :=
  | PC_Skip : forall st,
      st =[ skip ]=> st, []
  | PC_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st), []
  | PC_Seq : forall c1 c2 st st' st'' bs1 bs2,
      st  =[ c1 ]=> st', bs1  ->
      st' =[ c2 ]=> st'', bs2 ->
      st  =[ c1 ; c2 ]=> st'', (bs1++bs2)
  | PC_IfTrue : forall st st' b c1 c2 bs1,
      beval st b = true ->
      st =[ c1 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (true::bs1)
  | PC_IfFalse : forall st st' b c1 c2 bs1,
      beval st b = false ->
      st =[ c2 ]=> st', bs1 ->
      st =[ if b then c1 else c2 end]=> st', (false::bs1)
  | PC_While : forall b st os c, (* <- Nice trick; from small-step semantics *)
      st =[ if b then c; while b do c end else skip end ]=> st, os ->
      st =[ while b do c end ]=> st, os

  where "st =[ c ]=> st' , bs" := (pceval c st st' bs).

Lemma pceval_ceval : forall c st st' bs,
  st =[ c ]=> st', bs ->
  st =[ c ]=> st'.
Proof.
  intros c st st' bs H. induction H; try (econstructor; eassumption).
  - (* need to justify the while trick *)
    inversion IHpceval.
    + inversion H6. subst. eapply E_WhileTrue; eauto.
    + eapply E_WhileFalse; eauto.
Qed.
(* TERSE: /HIDEFROMHTML *)

(** ** Program counter security definition *)

(** Using the instrumented semantics we define program counter security: *)

Definition pc_secure P c := forall s1 s2 s1' s2' bs1 bs2,
  pub_equiv P s1 s2 ->
  s1 =[ c ]=> s1', bs1 ->
  s2 =[ c ]=> s2', bs2 ->
  bs1 = bs2.

(** Program counter security is mostly orthogonal to noninterference and
    instead of relating the final states it requires the branches of
    the program to be independent of secrets.

    Our restrictive [pc_well_typed] relation enforces both
    noninterference (as we already proved above) and program counter security: *)

Theorem pc_well_typed_pc_secure : forall P c,
  P |-pc- c ->
  pc_secure P c.
(* FOLD *)
Proof.
  intros P c Hwt s1 s2 s1' s2' bs1 bs2 Heq Heval1 Heval2.
  generalize dependent s2'. generalize dependent s2.
  generalize dependent bs2.
  induction Heval1; intros bs2' s2 Heq s2' Heval2;
    inversion Heval2; inversion Hwt; subst.
  - reflexivity.
  - reflexivity.
  - erewrite IHHeval1_2; [erewrite IHHeval1_1 | | |];
      try reflexivity; try eassumption.
    (* the proof does rely on noninterference for the sequencing case *)
    eapply pc_well_typed_noninterferent;
      [ | eassumption | eapply pceval_ceval; eassumption
                      | eapply pceval_ceval; eassumption ]; eassumption.
  - f_equal. eapply IHHeval1; try eassumption.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - rewrite (noninterferent_bexp Heq H11) in H.
    rewrite H in H6. discriminate H6.
  - f_equal. eapply IHHeval1; eassumption.
  - eapply IHHeval1; try eassumption. repeat constructor; eassumption.
Qed.
(* /FOLD *)

(** The proof does rely on [pc_well_typed] implying
    noninterference for the sequencing and loop cases. *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+\\|(\\* EX[1-5]..." *)
(* End: *)
(* mode: outline-minor *)
(* outline-heading-end-regexp: "\n" *)
(* /HIDE *)
