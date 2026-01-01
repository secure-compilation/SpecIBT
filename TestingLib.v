Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.
From Stdlib Require Import String.
From SECF Require Import ListMaps MapsFunctor MiniCET Utils TaintTracking.
Require Import Stdlib.Classes.EquivDec.

(** ** Type system for cryptographic constant-time programming *)

(* Imported straight from TestingStateIFC.v, so don't bother testing them. *)

(* TERSE: HIDEFROMHTML *)
Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := ListTotalMap.t label.
Definition pub_arrs := ListTotalMap.t label.

Notation t_apply := ListTotalMap.t_apply.

Definition fold_extra {A : Type} {B : Type} (f : A -> list B -> B -> list B -> A) (l : list B) (v : A) : A :=
  let fix aux (processed : list B) (incoming : list B) (acc : A) :=
    match incoming with
    | [] => acc
    | h::t =>
        let new_acc := f acc processed h t in
        aux (processed ++ [h]) t new_acc
    end
  in aux [] l v.

#[export] Instance shrinkTotalMap {X : Type} `{Shrink X}: Shrink (ListTotalMap.t X) :=
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

Definition pub_equiv (P : ListTotalMap.t label) {X:Type} (s1 s2 : ListTotalMap.t X) :=
  forall x:string, t_apply P x = true -> t_apply s1 x = t_apply s2 x.

Definition pub_equivb (P : ListTotalMap.t label) {X:Type} `{EqDec X} (s1 s2 : ListTotalMap.t X) : bool :=
  match P, s1, s2 with
  | (dP,mP), (d1,m1), (d2,m2) =>
      if dP
      then forallb (fun x => if t_apply P x
                             then (t_apply s1 x) ==b (t_apply s2 x) else true)
                   (union (map_dom mP) (union (map_dom m1) (map_dom m2)))
           && (d1 ==b d2)
      else forallb (fun x => if t_apply P x
                             then (t_apply s1 x) ==b (t_apply s2 x) else true)
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

Definition gen_pub_equiv (P : ListTotalMap.t label) {X: Type} `{Gen X} (s: ListTotalMap.t X) : G (ListTotalMap.t X) :=
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map X)) (c : string * X) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if t_apply P k then ret v else arbitrary);;
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

#[export] Instance genVal : Gen val :=
  {arbitrary := freq [(2, n <- arbitrary;; ret (N n));
                      (1, l <- arbitrary;; ret (FP l))] }.

#[export] Instance showVal : Show val :=
  {show :=fun v => 
      match v with
      | N n => show n
      | FP l => ("&" ++ show l)%string
      | UV => "UV"%string
      end
  }.

Definition val_eqb (v1 v2: val) : bool :=
  match v1, v2 with
  | N n1, N n2 => Nat.eqb n1 n2
  | FP l1, FP l2 => Nat.eqb l1 l2
  | UV, UV => true (* don't use this in the semantics *)
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
    + reflexivity.
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
    + contradiction.
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

Definition gen_state : G (ListTotalMap.t val) :=
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

(* Definition shrink_pub_equiv_reg (P : ListTotalMap.t label) (s : ListTotalMap.t val) : ListTotalMap.t val -> list (ListTotalMap.t val) := *)
(*   fun '(d, m) => *)
(*     (* We can only shrink the default value iif nothing secret uses it. *)
(*        If the default for P is "secret", then we can always find a variable not in m that is secret. *)
(*        Otherwise, we can shrink if all public values in P are explicit in s *) *)
(*     let can_shrink_default := ( *)
(*       let '(default_visiblity, visiblities) := P in *)

(*       if default_visiblity *)
(*       then false *)
(*       else *)
(*         let public_variables := List.filter (fun x => *)
(*           apply P x *)
(*         ) (map_dom visiblities) in *)

(*         forallb (fun v => List.existsb (fun '(v', _) => String.eqb v v') m) public_variables *)
(*     ) in *)

(*     let secret_entries_shrunk := (List.map *)
(*          (fun m' => (d, m')) *)
(*          (fold_extra (fun acc before '(k, v) after => *)
(*             let modified_entry := if apply P k *)
(*               then [] *)
(*               else List.map (fun v' => *)
(*                   before ++ [(k, v')] ++ after *)
(*                 ) (shrink v) in *)

(*             modified_entry ++ acc *)
(*          ) m []) *)
(*       ) in *)

(*     (* We can only remove secret entries or public entries that have *)
(*        the same value as the default value *) *)
(*     let entries_removed := List.map *)
(*         (fun m' => (d, m')) *)
(*         (fold_extra (fun acc before '(k, v) after => *)
(*            let replacement := *)
(*              if negb (apply P k) || (v =v d) *)
(*              then before ++ after (* secret or same value as default *) *)
(*              else before ++ (k, v) :: after in *)

(*            replacement :: acc *)
(*         ) m []) in *)

(*     if can_shrink_default *)
(*     then (List.map (fun d' => (d', m)) (shrink d)) ++ (secret_entries_shrunk ++ entries_removed) *)
(*     else secret_entries_shrunk ++ entries_removed. *)

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

(* Definition shrink_pub_equiv_mem (P: list label) (s: list val) *)
(*   : list val -> list (list val) := *)
(*   fun s' => *)
(*     if negb (Datatypes.length P =? Datatypes.length s')%nat then [] *)
(*     else *)
(*       ( *)
(*         let secret_values_shrunk := *)
(*           (fix secret_values_shrunk_aux (P: list label) (rs: list val) := *)
(*              match P, rs with *)
(*              | [], [] => [] *)
(*              | hp::tp, hr::tr => *)
(*                  if hp *)
(*                  then (let shrunk_tl := secret_values_shrunk_aux tp tr in *)
(*                        List.map (fun tl => hr :: tl) shrunk_tl) *)
(*                  else (let shrunk_hd := shrink hr in *)
(*                        List.map (fun hd => hd :: tr) shrunk_hd) *)
(*              | _, _ => [] (* unreachable *) *)
(*              end) P s' in *)
(*         let secret_items_shrunk := *)
(*           remove_one_secret P s' in *)
(*         secret_values_shrunk ++ secret_items_shrunk *)

(*       ). *)

Definition list_minus {X : Type} `{EqDec X} (l1 l2 : list X) : list X :=
  filter (fun x => negb (existsb (fun y => x ==b y) l2)) l1.

#[export] Instance EqDec_nat : EqDec nat eq.
Proof.
  red. intros.
  destruct (Nat.eqb x y) eqn:Heb.
  - rewrite Nat.eqb_eq in Heb. left. subst. reflexivity.
  - rewrite Nat.eqb_neq in Heb. right. red. intros. apply Heb.
    apply H.
Qed.

Definition eitherOf {A} (a : G A) (b : G A) : G A := freq [(1, a); (1, b)].

(* [TestingStaticIFC.v]: The ;; notation didn't work with oneOf, probably related to monadic
   bind also using ;;. So I redefined the notation using ;;;. *)
Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.


(** TestingMiniCET-related Gen and Show instances *)

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
    (fun s => match String.get 1 s with
           | Some a => match (nat_of_ascii a - nat_of_ascii "0") with
                      | S n => ["X" ++ show (S n / 2); "X" ++ show (S n - 1)]
                      | 0 => []
                      end
           | None => nil
           end)%string }.

Eval compute in (shrink "X5")%string.
Eval compute in (shrink "X0")%string.

#[export] Instance showBinop : Show binop :=
  {show :=fun op => 
      match op with
      | BinPlus => "+"%string
      | BinMinus => "-"%string  
      | BinMult => "*"%string
      | BinEq => "="%string
      | BinLe => "<="%string
      | BinAnd => "&&"%string
      | BinImpl => "->"%string
      end
  }.

#[export] Instance showExp : Show exp :=
  {show := 
    (let fix showExpRec (e : exp) : string :=
       match e with
       | ANum n => show n
       | AId x => x
       | ABin o e1 e2 => 
           "(" ++ showExpRec e1 ++ " " ++ show o ++ " " ++ showExpRec e2 ++ ")"
       | ACTIf b e1 e2 =>
           "(" ++ showExpRec b ++ " ? " ++ showExpRec e1 ++ " : " ++ showExpRec e2 ++ ")"
       | FPtr l => "&" ++ show l
       end
     in showExpRec)%string
  }.

#[export] Instance showInst : Show inst :=
  {show := 
      (fun i =>
         match i with
         | ISkip => "skip"
         | IAsgn x e => x ++ " := " ++ show e
         | IBranch e l => "branch " ++ show e ++ " to " ++ show l
         | IJump l => "jump " ++ show l
         | ILoad x a => x ++ " <- load[" ++ show a ++ "]"
         | IStore a e => "store[" ++ show a ++ "] <- " ++ show e
         | ICall fp => "call " ++ show fp
         | ICTarget => "ctarget"
         | IRet => "ret"
         end)%string
  }.

(* As in [TestingStaticIFC.v], we generate a finite total map which we use as state. *)
#[export] Instance genTotalMap (A:Type) `{Gen A} : Gen (ListTotalMap.t A) :=
  {arbitrary := (d <- arbitrary;;
                 v0 <- arbitrary;;
                 v1 <- arbitrary;;
                 v2 <- arbitrary;;
                 v3 <- arbitrary;;
                 v4 <- arbitrary;;
                 v5 <- arbitrary;;
                 ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
                         ("X3",v3); ("X4",v4); ("X5",v5)])%string)}.

(* [TestingStaticIFC.v]: The ;; notation didn't work with oneOf, probably related to monadic
   bind also using ;;. So I redefined the notation using ;;;. *)
Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.

Derive (Arbitrary, Shrink) for binop.
Derive (Arbitrary, Shrink) for exp.
Derive (Arbitrary, Shrink) for inst.

Definition is_defined (v:val) : bool :=
  match v with
  | UV => false
  | _ => true
  end.

Fixpoint max n m := match n, m with 
                   | 0, _ => m
                   | _, 0 => n
                   | S n', S m' => S (max n' m')
                   end.


Module MCC := MiniCETCommon(ListTotalMap).
Import MCC.

(*! Section testing_ETE *)

(** Type system for soundenss *)

Inductive ty : Type := | TNum | TPtr.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum | TPtr, TPtr => true
                               | _, _ => false
                               end.

Definition rctx := ListTotalMap.t ty.
Definition tmem := list ty.

Fixpoint ty_of_exp (c : rctx) (e : exp) : ty :=
  match e with
  | ANum _ => TNum
  | AId x => c ! x
  | ABin _ _ _ => TNum
  (* Here we assume that "e" is well-typed and infer the type by the second branch of "ACTIf"  *)
  | ACTIf _ _ x => ty_of_exp c x
  | FPtr _ => TPtr
end.

Definition filter_vars_by_ty (t: ty) (c: rctx) : list string :=
  filter (fun x => ty_eqb (c ! x) t) (map_dom (snd c)).

Definition is_ptr (c : rctx) (var : string) :=
  match c ! var with
  | TPtr => true
  | _ => false
  end.

(* predicate for fold *)
Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.

(** Well-formed Program Generator *)

(* This auxiliary function, given a program length, generates the length of procedures in this program, counted in blocks.
   It therefore partitions the program in procedures. *)
Fixpoint _gen_partition (fuel program_length: nat) : G (list nat) :=
  match fuel with
  | 0 => ret [program_length]
  | S fuel' =>
      match program_length with
      | O => ret []
      | S O => ret [1]
      | S (S program_length') => (k <- choose(1, program_length - 1);;
                     rest <- _gen_partition fuel' (program_length - k);;
                     ret (k :: rest))
      end
  end.

Definition gen_partition (pl: nat): G (list nat) := _gen_partition pl pl.

Fixpoint proc_hd (pst: list nat) : list nat :=
  match pst with
  | [] => []
  | hd :: tl => 0 :: map (fun x => x + hd) (proc_hd tl)
  end.

Compute (proc_hd [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Definition gen_callable (pl : nat) : G (list nat) :=
  pst <- gen_partition pl ;; ret (proc_hd pst).

Definition gen_vars (len: nat) : G (list string) :=
  vectorOf len arbitrary.

Sample (gen_vars 5).

Definition ex_vars : list string :=
  ["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string].

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

#[export] Instance genTMem `{Gen ty} : Gen tmem :=
  {arbitrary := t <- arbitrary;;
                tm <- arbitrary;;
                ret (t :: tm) }.

(* Similar to the previous expressions generators, we now generate the well-typed leaves, which
  differentiate between different types of values in the program. *)
Definition gen_exp_leaf_wt (t: ty) (c: rctx) (pst: list nat) : G exp :=
  match t with
  | TNum =>
      oneOf (liftM ANum arbitrary ;;;
               (let not_ptrs := filter (fun x => negb (is_ptr c x)) (map_dom (snd c)) in
                if seq.nilp not_ptrs then [] else
                  [liftM AId (elems_ "X0"%string not_ptrs)] ) )
  | _ =>
      oneOf (liftM FPtr (elems_ 0 (proc_hd pst));;;
               (let ptrs := filter (fun x => (is_ptr c x)) (map_dom (snd c)) in
                if seq.nilp ptrs then [] else
                  [liftM AId (elems_ "X0"%string ptrs)] ) )
  end.

Fixpoint gen_exp_no_ptr_wt (sz : nat) (c : rctx) (pst: list nat) : G exp :=
  match sz with
  | O => gen_exp_leaf_wt TNum c []
  | S sz' =>
      freq [ (2, gen_exp_leaf_wt TNum c []);
             (sz, eitherOf
                    (liftM3 ABin arbitrary (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
                    (liftM2 (ABin BinEq) (gen_exp_leaf_wt TPtr c pst)  (gen_exp_leaf_wt TPtr c pst)));
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
          ]
  end
with gen_exp_ptr_wt (sz : nat) (c : rctx) (pst: list nat) : G exp :=
  match sz with
  | O => gen_exp_leaf_wt TPtr c pst
  | S sz' => 
      freq [ (2, gen_exp_leaf_wt TPtr c pst);
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_ptr_wt sz' c pst) (gen_exp_ptr_wt sz' c pst))
          ]
  end.

Fixpoint gen_exp_wt (sz: nat) (c: rctx) (pst: list nat) : G exp :=
  match sz with 
  | O =>
      t <- arbitrary;;
      gen_exp_leaf_wt t c pst
  | S sz' => 
      freq [
          (2, t <- arbitrary;; gen_exp_leaf_wt t c pst);
          (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
                    (liftM2 (ABin BinEq) (gen_exp_leaf_wt TPtr c pst) (gen_exp_leaf_wt TPtr c pst))
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_wt sz' c pst) (gen_exp_wt sz' c pst))
          ]
  end.

Fixpoint gen_exp_ty_wt (t: ty) (sz: nat) (c: rctx) (pst: list nat) : G exp :=
  match t with
  | TNum => gen_exp_no_ptr_wt sz c pst
  | TPtr => gen_exp_ptr_wt sz c pst
  end.

Definition gen_val_wt (t: ty) (pst: list nat) : G val :=
  match t with
  | TNum => liftM N arbitrary
  | TPtr => match (proc_hd pst) with
           | [] => ret (FP 0)
           | p::pst' => liftM FP (elems_ p (p::pst'))
           end
  end.

Definition gen_reg_wt (c: rctx) (pst: list nat) : G reg :=
  let wt_vars := snd c in
  let gen_binds := mapGen (fun '(name, t) =>  (v <- gen_val_wt t pst;; ret (name, v))) wt_vars in
  default_val <- gen_val_wt (fst c) pst;;
  b <- gen_binds;;
  ret (default_val, b).

Definition wt_exp_is_defined := (forAll arbitrary (fun (c : rctx) =>
            forAll (gen_reg_wt c [3; 3; 1; 1]) (fun (state: reg) =>
            forAll (gen_exp_wt 4 c [3; 3; 1; 1]) (fun (exp : exp) =>
            implication (is_defined (eval state exp)) true)))).
(*! QuickChick wt_exp_is_defined. *)

Definition gen_asgn_wt (t: ty) (c: rctx) (pst: list nat) : G inst :=
  let tlst := filter (fun '(_, t') => ty_eqb t t') (snd c) in
  let vars := map_dom tlst in
  if seq.nilp vars
  then ret <{ skip }>
  else
    x <- elems_ "X0"%string vars;;
    a <- gen_exp_ty_wt t 1 c pst;;
    ret <{ x := a }>.

Definition gen_branch_wt (c: rctx) (pl: nat) (pst: list nat) (default : nat) : G inst :=
  let vars := (map_dom (snd c)) in
  let jlst := (list_minus (seq 0 pl) (proc_hd pst)) in
  e <- gen_exp_ty_wt TNum 1 c pst;;
  l <- elems_ default jlst;; (* 0 is unreachable *)
  ret <{ branch e to l }>.

Definition gen_jump_wt (pl: nat) (pst: list nat) (default : nat) : G inst :=
  l <- elems_ default (list_minus (seq 0 pl) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ jump l }>.

Definition filter_typed {A : Type} (t : ty) (l : list (A * ty)): list A := 
  map fst (filter (fun '(_, t') => ty_eqb t t') l).

Notation " 'elems' ( h ;;; tl )" := (elems_ h (cons h tl)) 
  (at level 1, no associativity) : qc_scope.

Definition gen_load_wt (t: ty) (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  let vars := filter_typed t (snd c) in
  sz <- choose(1, 3);;
  exp <- gen_exp_ty_wt TNum sz c pst;;
  match vars with
  | h :: tl =>
    x <- elems ( h ;;; tl);;
    ret <{ x <- load[exp] }>
  | _ => ret <{ skip }>
  end.

Definition gen_store_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  match tm with
  | h :: tl =>
    t <- elems (h ;;; tl);;
    e1 <- gen_exp_ty_wt TNum 1 c pst;;
    e2 <- gen_exp_ty_wt t 1 c pst;;
    ret <{ store[e1] <- e2 }>
  | _ => ret <{ skip }>
  end.

Definition compose_load_store_guard (t : ty) (id_exp : exp) (mem : tmem) : exp :=
  let indices := seq 0 (Datatypes.length mem) in
  let idx := filter_typed t (combine indices mem) in
  let tc := fold_left 
            (fun acc x => BOr x acc)
            (map (fun id => <{{ id_exp = ANum id }}>) idx)
            <{{ false }}> in
  let mem_sz := ANum (Datatypes.length mem) in
  let guardc := BLt id_exp mem_sz in
  BAnd tc guardc. 
Eval compute in (compose_load_store_guard TNum <{ AId "X0"%string }> [TNum ; TPtr; TNum ]).

Definition transform_load_store_inst (c : rctx) (mem : tmem) (acc : list inst) (i : inst) : M (bool * list inst) :=
  match i with
  | <{{ x <- load[e] }}> =>
      let t := t_apply c x in
      merge <- add_block_M acc;;
      new <- add_block_M <{{ i[ x <- load[e]; jump merge] }}>;;
      ret (true, <{{ i[branch (compose_load_store_guard t e mem) to new; jump merge] }}>)
  | <{{ store[e] <- e1 }}> =>
      merge <- add_block_M acc;;
      new <- add_block_M <{{ i[store[e] <- e1; jump merge] }}>;;
      ret (true, <{{ i[branch (compose_load_store_guard (ty_of_exp c e1) e mem) to new; jump merge] }}>)
  | _ => ret (false, [i])
  end.

Definition split_and_merge (c : rctx) (mem : tmem) (i : inst) (acc : list inst) : M (list inst) :=
  tr <- transform_load_store_inst c mem acc i;;
  let '(is_split, new_insts) := tr in
  (* If we split the block in two because of "load"/"store", then all previous instructions *)
  (* get saved in the new block. New ones stay, and the "merge" lnk gets updated. *)
  if is_split then
    ret new_insts
  (* If we don't split, than we concat new instructions to previous instructions and last "merge" link stays the same *)
  else
  (* NOTE: We are folding from the right, so new instructions are appended to the beginning of current block *)
    ret (new_insts ++ acc).

Definition transform_load_store_blk (c : rctx) (mem : tmem) (nblk : list inst * bool): M (list inst * bool) :=
  let (bl, is_proc) := nblk in
  folded <- fold_rightM (split_and_merge c mem) bl <{{ i[ ret ] }}>;;
  ret (folded, is_proc).

Definition transform_load_store_prog (c : rctx) (mem : tmem) (p : prog) :=
  let '(p', newp) := mapM (transform_load_store_blk c mem) p (Datatypes.length p) in
  (p' ++ newp).

(* Example transform := transform_load_store_prog [TPtr; TNum; TPtr]%list [(<{{ i[ ctarget; X := 0; Y <- load[X]; store[Y] <- X] }}>, true)]. 
Eval compute in transform.
Eval compute in (Datatypes.length transform).
Eval compute in (nth_error transform 3). *)

Definition gen_call_wt (c: rctx) (pst: list nat) : G inst :=
  e <- gen_exp_ptr_wt 1 c pst;;
  ret <{ call e }>.

Definition _gen_inst_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                        (gen_branch : rctx -> nat -> list nat -> nat -> G inst)
                        (gen_jump : nat -> list nat -> nat -> G inst)
                        (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_call : rctx -> list nat -> G inst)
                        (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  let insts := 
     [ (1, ret ISkip);
       (1, ret IRet);
       (sz, t <- arbitrary;; gen_asgn t c pst);
       (sz, t <- arbitrary;; gen_load t c tm pl pst);
       (sz, gen_store c tm pl pst);
       (sz, gen_call c pst) ] in
  let non_proc_labels := list_minus (seq 0 pl) (proc_hd pst) in
  match non_proc_labels with
  | nil => freq_ (ret ISkip) insts
  | hd :: _ => freq_ (ret ISkip) (insts ++ [ (2, gen_branch c pl pst hd)(* ; (sz, gen_jump pl pst hd) *)])
  end.

(* redundant functions *)
Definition gen_nonterm_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                          (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                          (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                          (gen_call : rctx -> list nat -> G inst)
                          (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  freq [ (1, ret ISkip);
         (sz, t <- arbitrary;; gen_asgn t c pst);
         (sz, t <- arbitrary;; gen_load t c tm pl pst);
         (sz, gen_store c tm pl pst);
         (sz, gen_call c pst)].

Definition _gen_term_wt (gen_branch : rctx -> nat -> list nat -> nat -> G inst)
                      (gen_jump : nat -> list nat -> nat -> G inst)
                      (c: rctx) (tm: tmem) (* (sz:nat) *) (pl: nat) (pst: list nat) : G inst :=
  let non_proc_labels := list_minus (seq 0 pl) (proc_hd pst) in
  match non_proc_labels with
  | nil => ret IRet
  | hd :: _ => freq_ (ret IRet) ([(1, ret IRet) ; (2, gen_jump pl pst hd)])
  end.

Definition gen_term_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  _gen_term_wt gen_branch_wt gen_jump_wt c tm pl pst.

Definition gen_inst_wt (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  _gen_inst_wt gen_asgn_wt gen_branch_wt gen_jump_wt gen_load_wt gen_store_wt gen_call_wt
               c tm sz pl pst.

Definition gen_blk_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wt c tm bsz pl pst).

Definition _gen_blk_body_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf (bsz - 1) (gen_inst_wt c tm bsz pl pst).

Definition gen_blk_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  blk <- _gen_blk_body_wt c tm bsz pl pst;;
  term <- gen_term_wt c tm pl pst;;
  ret (blk ++ [term]).

Definition basic_block_checker (blk: list inst) : bool :=
  match blk with
  | [] => false
  | _ => match seq.last ISkip blk with
        | IRet | IJump _ => true
        | _ => false
        end
  end.

Definition basic_block_gen_example : G (list inst) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  gen_blk_with_term_wt c tm 8 8 [3; 3; 1; 1].

Definition basic_block_test := (forAll (basic_block_gen_example) (fun (blk: list inst) => (basic_block_checker blk))).
(*! QuickChick basic_block_test. *)

Fixpoint _gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Definition gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_with_term_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_with_term_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Definition gen_prog_with_term_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_with_term_wt c tm bsz pl pst pst.

Definition prog_basic_block_checker (p: prog) : bool :=
  forallb (fun bp => (basic_block_checker (fst bp))) p.

Definition basic_block_wt_test := (forAll (gen_prog_with_term_wt_example 8) (fun (p: prog) => (prog_basic_block_checker p))).
(*! QuickChick basic_block_wt_test. *)

(* Similarly to "_gen_proc_wf", we generate a procedure with all expressions well-typed (with respect to
  statuc register context "c : rctx"). Here, "fsz" is the number of blocks in procedure, "bsz" is the
  number of instructions in the block, and "pl" is the program length. *)
Fixpoint _gen_proc_wt (c: rctx) (tm: tmem) (psz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match psz with
  | O => ret []
  | S psz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm psz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Definition gen_proc_wt (c: rctx) (tm: tmem) (psz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match psz with
  | O => ret [] (* unreachable *)
  | S psz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm psz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Definition gen_prog_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_wt c tm bsz pl pst pst.

Definition test_wt_example : G bool :=
  prog <- gen_prog_wt_example 8;;
  ret (wf prog).

Definition gen_prog_wt (bsz pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  _gen_prog_wt c tm bsz pl pst pst.

Definition gen_prog_wt' (c : rctx) (pst : list nat) (bsz pl : nat) :=
  tm <- arbitrary;;
  _gen_prog_wt c tm bsz pl pst pst.

Definition wt_wf := (forAll (gen_prog_wt 3 8) (fun (p : prog) => (wf p))).
(*! QuickChick wt_wf. *)
Definition wt_uslh_wf := (forAll (gen_prog_wt 3 8) (fun (p : prog) => (wf (uslh_prog p)))).
(*! QuickChick wt_uslh_wf. *)

(* The well-typed expression "always evaluates" in the register set produces by "gen_reg_wt " *)
Definition wt_expr_is_defined := (
    forAll arbitrary (fun (c : rctx) =>
    forAll arbitrary (fun (pl : nat) =>
    forAll (choose (2, 5)) (fun (exp_sz : nat) => 
    pst <- gen_partition pl;;
    forAll (gen_reg_wt c pst) (fun (r : reg) =>
    forAll (gen_exp_wt exp_sz c pst) (fun (e : exp) =>
    is_defined (eval r e)
  )))))).
(*! QuickChick wt_expr_is_defined. *)

(* "+++ Passed 10000 tests (0 discards)" *)

(* To evaluate our generator, we proceed by creating a predicate, which checks kind of type checks the
  program. *)

Fixpoint ty_exp (c: rctx) (e: exp) : option ty :=
  match e with
  | ANum _ => Some TNum
  | FPtr _ => Some TPtr
  | AId x => Some (t_apply c x)
  | ACTIf e1 e2 e3 => match ty_exp c e1 with
                     | Some TNum => match ty_exp c e2, ty_exp c e3 with
                                   | Some TNum, Some TNum => Some TNum
                                   | Some TPtr, Some TPtr => Some TPtr
                                   | _, _ => None
                                   end
                     | _ => None
                     end
  | ABin bop e1 e2 => match bop with
                     | BinEq =>  match ty_exp c e1, ty_exp c e2 with
                                | Some t1, Some t2 => if (ty_eqb t1 t2) then Some TNum else None
                                | _, _ => None
                                end
                     | _ => match ty_exp c e1, ty_exp c e2 with
                           | Some TNum, Some TNum => Some TNum
                           | _, _ => None
                           end
                     end
  end.

(* The "ty_inst" predicate checks if the instruction "i" in the program "p" is well-typed with respect to
  register context "c" and a typed memory "tm". *)
Fixpoint ty_inst (c: rctx) (tm: tmem) (p: prog) (i: inst) : bool :=
  match i with
  | ISkip | ICTarget | IRet => true
  | IAsgn x e => match ty_exp c e with
                | Some t => ty_eqb (t_apply c x) t
                | _ => false
                end
  | IBranch e l => match ty_exp c e with
                  | Some TNum => wf_label p false l
                  | _ => false
                  end
  | IJump l => wf_label p false l
  (* let's trust generator. *)
  | ILoad x e => match e with
                | ANum n =>
                    match nth_error tm n with
                    | Some t => ty_eqb (t_apply c x) t
                    | _ => false
                    end
                | _ => match ty_exp c e with
                      | Some TNum => true
                      | _ => false
                      end
                end
  | IStore a e => match a with
                 | ANum n =>
                     match nth_error tm n, ty_exp c e with
                     | Some t1, Some t2 => ty_eqb t1 t2
                     | _, _ => false
                     end
                 | _ => match ty_exp c a, ty_exp c e with
                       | Some TNum, Some _ => true
                       | _, _ => false
                       end
                 end
  | ICall e => match e with
              | FPtr l => wf_label p true l
              | _ => match ty_exp c e with
                    | Some TPtr => true
                    | _ => false
                    end
              end
  end.

Definition ty_blk (c: rctx) (tm: tmem) (p: prog) (blk: list inst * bool) : bool :=
  forallb (ty_inst c tm p) (fst blk).

Definition ty_prog (c: rctx) (tm: tmem) (p: prog) : bool :=
  forallb (ty_blk c tm p) p.

Definition gen_prog_ty_ctx_wt (bsz pl: nat) : G (rctx * tmem * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_wt c tm bsz pl pst pst;;
  ret (c, tm, p).

Definition ty_prog_wf := (forAll (gen_prog_ty_ctx_wt 3 8) (fun '(c, tm, p) => ((ty_prog c tm p) && (wf p)))).

(** Relative Security *)

(* Taint Tracker for input pairs *)

Definition join (l1 l2 : label) : label := l1 && l2.

Fixpoint vars_exp (e:exp) : list string :=
  match e with
  | ANum n => []
  | AId i => [i]
  | ABin op e1 e2 => vars_exp e1 ++ vars_exp e2
  | ACTIf e1 e2 e3 => vars_exp e1 ++ vars_exp e2 ++ vars_exp e3
  | FPtr n => []
  end.

Definition vars_inst (i: inst) : list string :=
  match i with
  | ISkip | IRet | ICTarget | IJump _ => []
  | IAsgn x e => x :: vars_exp e
  | IBranch e l => vars_exp e
  | ILoad x e => x :: vars_exp e
  | IStore e1 e2 => vars_exp e1 ++ vars_exp e2
  | ICall e => vars_exp e
  end.

Fixpoint vars_blk (blk: list inst) : list string :=
  List.concat (map vars_inst blk).

Fixpoint _vars_prog (p: prog) : list string :=
  match p with
  | [] => []
  | (blk, _) :: tl => vars_blk blk ++ _vars_prog tl
  end.

Definition vars_prog (p: prog) : list string :=
  remove_dupes String.eqb (_vars_prog p).

Definition label_of_exp (P:pub_vars) (e:exp) : label :=
  List.fold_left (fun l a => join l (P ! a)) (vars_exp e) public.

(* Copied from TestingFlexSLH.v *)

(** Some generators *)

Definition gen_prog_ty_ctx_wt' (bsz pl: nat) : G (rctx * tmem * list nat * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_wt c tm bsz pl pst pst;;
  ret (c, tm, pst, p).

Definition gen_prog_wt_with_basic_blk (bsz pl: nat) : G (rctx * tmem * list nat * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_with_term_wt c tm bsz pl pst pst;;
  ret (c, tm, pst, p).

Definition gen_wt_mem (tm: tmem) (pst: list nat) : G mem :=
  let indices := seq 0 (Datatypes.length tm) in
  let idx_tm := combine indices tm in
  let gen_binds := mapGen (fun '(idx, t) => (v <- gen_val_wt t pst;; ret (idx, v))) idx_tm in
  r <- gen_binds;;
  ret (snd (split r)).

(** Some common definitions *)

Definition all_possible_vars : list string := (["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string; "X5"%string]).

Fixpoint member (n: nat) (l: list nat) : bool :=
  match l with
  | [] => false
  | hd::tl => if (hd =? n) then true else member n tl
  end.

Fixpoint _tms_to_pm (tms: list nat) (len: nat) (cur: nat) : list label :=
  match len with
  | 0 => []
  | S len' => member cur tms :: _tms_to_pm tms len' (S cur)
  end.

(* Calculate public memory from taint memory *)
Definition tms_to_pm (len: nat) (tms: list nat) : list label :=
  _tms_to_pm tms len 0.

Compute (tms_to_pm 8 [3; 4; 5]).

(* well-type checkers *)
Definition wt_valb (v: val) (t: ty) : bool :=
  match v, t with
  | N _, TNum | FP _, TPtr => true
  | _, _ => false
  end.

Definition rs_wtb (rs : total_map val) (c : rctx) : bool :=
  let '(dv, m) := rs in
  let '(dt, tm) := c in
  wt_valb dv dt && forallb (fun '(x, t) => wt_valb (t_apply rs x) t) tm.

Fixpoint _gen_pub_mem_equiv_same_ty (P : list label) (m: list val) : G (list val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 | UV => ret UV (* shouldn't happen *)
                 end in
  match P, m with
  | [], [] => ret []
  | hdp::tlp, hdm::tlm =>
      hd <- (if hdp then ret hdm else f hdm);;
      tl <-_gen_pub_mem_equiv_same_ty tlp tlm;;
      ret (hd::tl)
  | _, _ => ret [] (* unreachable *)
  end.

Fixpoint gen_pub_mem_equiv_same_ty (P : list label) (m: list val) : G (list val) :=
  if (Datatypes.length P =? Datatypes.length m)
  then _gen_pub_mem_equiv_same_ty P m
  else ret [].

Definition m_wtb (m: mem) (tm: tmem) : bool :=
  let mtm := combine m tm in
  forallb (fun '(v, t) => wt_valb v t) mtm.

(* check 2: no observation -> no leaked *)

Definition gen_inst_no_obs (pl: nat) (pst: list nat) : G inst :=
  let jlb := (list_minus (seq 0 (pl - 1)) (proc_hd pst)) in
  if seq.nilp jlb
  then ret <{ skip }>
  else freq [
           (1, ret ISkip);
           (1, ret IRet);
           (1, l <- elems_ 0 jlb;; ret (IJump l))
         ].

Definition gen_blk_no_obs (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_no_obs pl pst).

Fixpoint _gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, max 1 bsz);;
      blk <- gen_blk_no_obs n pl pst;;
      rest <- _gen_proc_no_obs fsz' bsz pl pst;;
      ret ((blk, false) :: rest)
  end.

Definition gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, max 1 bsz);;
      blk <- gen_blk_no_obs n pl pst;;
      rest <- _gen_proc_no_obs fsz' bsz pl pst;;
      ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_no_obs (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl =>
      hd_proc <- gen_proc_no_obs hd bsz pl pst;;
      tl_proc <- _gen_prog_no_obs bsz pl pst tl;;
      ret (hd_proc ++ tl_proc)
  end.

Definition gen_no_obs_prog : G prog :=
  pl <- choose(2, 6);; (* Generate small but non-trivial programs *)
  pst <- gen_partition pl;;
  let bsz := 3 in (* Max instructions per block *)
  _gen_prog_no_obs bsz pl pst pst.

Definition empty_mem : mem := [].

Definition empty_rs : reg := t_empty (FP 0).

(** Tests for Speculative Execution *)

Derive Show for observation.

Definition spec_rs (rs: reg) := (callee !-> (FP 0); (msf !-> (N 0); rs)).

(** * Reusable testing strategies, which are based on generators from this library.  *)

Module TestingStrategies(Import ST : Semantics ListTotalMap).
(* Extract Constant defNumTests => "1000000". *)

Module Import MTT := TaintTracking(ST).

(* ** Direction generators *)
(* 
Definition gen_dbr : G direction :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G direction :=
  l <- (elems_ 0 (proc_hd pst));; ret (DCall (l, 0)). *)

Variant sc_output_st : Type :=
  | SRStep : obs -> dirs -> spec_cfg -> sc_output_st
  | SRError : obs -> dirs -> spec_cfg -> sc_output_st
  | SRTerm : obs -> dirs -> spec_cfg -> sc_output_st.

Definition gen_step_direction (i: inst) (c: cfg) (pst: list nat)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G dirs :=
  let '(pc, rs, m, s) := c in
  match i with
  | <{ branch e to l }> => db <- gen_dbr;; ret [db]
  | <{ call e }> =>  dc <- gen_dcall pst;; ret [dc]
  | _ => ret []
  end.

Definition gen_spec_step (p:prog) (sc:spec_cfg) (pst: list nat) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir): G sc_output_st :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  match fetch p pc with
  | Some i =>
      match i with
      | <{{branch e to l}}> =>
          d <- gen_dbr;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | <{{call e}}> =>
          d <- gen_dcall pst;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | IRet | ICTarget =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [ ] sc'
               | (S_Term, _, _) => SRTerm [] [] sc
               | _ => SRError [] [] sc
               end)
      | _ =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [ ] sc'
               | _ => SRError [] [] sc
               end)
      end
  | None => ret (SRError [] [] sc)
  end.

Variant spec_exec_result : Type :=
  | SETerm (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEError (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEOutOfFuel (sc: spec_cfg) (os: obs) (ds: dirs).

#[export] Instance showSER `{Show dir} : Show spec_exec_result :=
  {show :=fun ser => 
      match ser with
      | SETerm sc os ds => show ds
      | SEError _ _ ds => ("error!!"%string ++ show ds)%string
      | SEOutOfFuel _ _ ds => ("oof!!"%string ++ show ds)%string
      end
  }.

Fixpoint _gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc: spec_cfg) (os: obs) (ds: dirs) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G (spec_exec_result) :=
  match f with
  | 0 => ret (SEOutOfFuel sc os ds)
  | S f' =>
      sr <- gen_spec_step p sc pst gen_dbr gen_dcall;;
      match sr with
      | SRStep os1 ds1 sc1 =>
          _gen_spec_steps_sized f' p pst sc1 (os ++ os1) (ds ++ ds1) gen_dbr gen_dcall
      | SRError os1 ds1 sc1 =>
          (* trace ("ERROR STATE: " ++ show sc1)%string *)
          (ret (SEError sc1 (os ++ os1) (ds ++ ds1)))
      | SRTerm  os1 ds1 sc1 =>
          ret (SETerm sc1 (os ++ os1) (ds ++ ds1))
      end
  end.

Definition gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc:spec_cfg) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G (spec_exec_result) :=
  _gen_spec_steps_sized f p pst sc [] [] gen_dbr gen_dcall.

(* Speculative Step functions *)
Definition spec_step_acc (p:prog) (sc:spec_cfg) (ds: dirs) : sc_output_st :=
  match spec_step p (S_Running sc) ds with
  | (S_Running sc', ds', os) => SRStep os ds' sc' (* sc': current spec_cfg, os: observations, ds': remaining dirs *)
  | (S_Term, _, _) => SRTerm [] [] sc
  | _ => SRError [] [] sc
  end.

Fixpoint _spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (os: obs) (ds: dirs) : spec_exec_result :=
  match f with
  | 0 => SEOutOfFuel sc os ds (* sc: current spec_cfg, os: observations, ds: remaining dirs *)
  | S f' =>
      match spec_step_acc p sc ds with
      | SRStep os1 ds1 sc1 =>
          _spec_steps_acc f' p sc1 (os ++ os1) ds1
      | SRError os1 ds1 sc1 =>
          (SEError sc1 (os ++ os1) ds1)
      | SRTerm os1 ds1 sc1 =>
          (SETerm sc1 (os ++ os1) ds1)
      end
  end.

Definition spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (ds: dirs) : spec_exec_result :=
  _spec_steps_acc f p sc [] ds.

Definition load_store_trans_basic_blk := (
    forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
      List.forallb basic_block_checker (map fst (transform_load_store_prog c tm p)))
).

Definition stuck_free (f : nat) (p : prog) (c: cfg) : exec_result :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  steps_taint_track f p ist [].

Definition load_store_trans_stuck_free := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let p' := transform_load_store_prog c tm p in
  let icfg := (ipc, rs, m, istk) in
  let r1 := stuck_free 1000 p' icfg in
  match r1 with
  | ETerm st os => checker true
  | EOutOfFuel st os => checker tt
  | EError st os => printTestCase (show p' ++ nl) (checker false)
  end)))).

Definition no_obs_prog_no_obs := (
  forAll gen_no_obs_prog (fun p =>
  let icfg := (ipc, empty_rs, empty_mem, istk) in
    match taint_tracking 10 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker tt
    end
  )).

Definition gen_prog_and_unused_var : G (rctx * tmem * list nat * prog * string) :=
  '(c, tm, pst, p) <- (gen_prog_wt_with_basic_blk 3 5);;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (c, tm, pst, p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (c, tm, pst, p, x).

Definition unused_var_no_leak (transform : rctx -> tmem -> prog -> prog) := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform c tm p in
  match stuck_free 100 p' icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      checker (negb (existsb (String.eqb unused_var) leaked_vars))
  | EOutOfFuel st os => checker tt
  | EError st os => checker false
  end)))).

Definition gen_pub_equiv_same_ty (P : total_map label) (s: total_map val) : G (total_map val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 | UV => ret UV (* shouldn't happen *)
                 end in
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map val)) (c : string * val) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if t_apply P k then ret v else f v);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

Definition gen_pub_equiv_is_pub_equiv := (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv_same_ty P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

Definition gen_reg_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs => rs_wtb rs c))).

Definition gen_pub_mem_equiv_is_pub_equiv := (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

Definition gen_mem_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst) (fun m => m_wtb m tm))).

Definition test_ni (transform : rctx -> tmem -> prog -> prog) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform c tm p in
  let r1 := taint_tracking 100 p' icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let icfg' := (ipc, rs', m', istk) in
      let r2 := taint_tracking 100 p' icfg' in
      match r2 with
      | Some (os2', _, _) => checker (obs_eqb os1' os2')
      | None => checker false (* fail *)
      end))
   | None => checker tt (* discard *)
  end)))).

Definition test_safety_preservation `{Show dir} 
  (harden : prog -> prog) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let p' := transform_load_store_prog c tm p in
  let harden := harden p' in
  let rs' := spec_rs rs in
  let icfg' := (ipc, rs', m, istk) in
  let iscfg := (icfg', true, false) in
  let h_pst := pst_calc harden in
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg gen_dbr gen_dcall) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError (c', _, _) _ ds => checker false
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

Definition test_relative_security `{Show dir} 
  (harden : prog -> prog) 
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) := (
  (* TODO: should make sure shrink indeed satisfies invariants of generator;
           or define a better shrinker *)
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst) (fun m1 =>
  let icfg1 := (ipc, rs1, m1, istk) in
  let p' := transform_load_store_prog c tm p in
  let r1 := taint_tracking 1000 p' icfg1 in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m1) tms in
      forAll (gen_pub_equiv_same_ty P rs1) (fun rs2 =>
      forAll (gen_pub_mem_equiv_same_ty PM m1) (fun m2 =>
      let icfg2 := (ipc, rs2, m2, istk) in
      let r2 := taint_tracking 1000 p' icfg2 in
      match r2 with
      | Some (os2', _, _) =>
          if (obs_eqb os1' os2') (* The source program produces the same leakage for a pair of inputs. *)
          then (let harden := harden p' in
                let rs1' := spec_rs rs1 in
                let icfg1' := (ipc, rs1', m1, istk) in
                let iscfg1' := (icfg1', true, false) in
                let h_pst := pst_calc harden in
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1' gen_dbr gen_dcall) (fun ods1 =>
                (match ods1 with
                 | SETerm _ os1 ds =>
                     (* checker true *)
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => checker (obs_eqb os1 os2)
                     | SEOutOfFuel _ _ _ => collect "se2 oof"%string (checker tt)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                     end
                 | SEOutOfFuel _ os1 ds => 
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => collect "se1 oof but se2 term"%string (checker tt) (* this would be very weird *)
                     | SEOutOfFuel _ os2 _ => checker (obs_eqb os1 os2) (* equality should hold because essentially lockstep *)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                     end
                 | _ =>  collect "1st speculative execution fails!"%string (checker tt) (* discard -- doesn't seem to happen *)
                 end))
               )
          else collect "seq obs differ"%string (checker tt) (* discard *)
      | None => collect "tt2 failed"%string (checker tt) (* discard *)
      end))
   | None => collect "tt1 failed"%string (checker tt) (* discard *)
  end)))).

End TestingStrategies.