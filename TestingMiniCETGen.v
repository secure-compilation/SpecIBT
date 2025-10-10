(* Utils for testing of "TestingMiniCET" *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From SECF Require Import ListMaps.
From SECF Require Import TestingMiniCET.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From Coq Require Import String.

(* The first property I test is the one proposed by Catalin, which shows how sane our
  generators are: *)
(* "forAll e st, is_some (eval st e) ==> True" *)

(* Tests with generators derived by QuickChick are almost fully discarded: *)
(* QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll arbitrary (fun (exp : exp) =>
            implication (is_some (eval state exp)) true))). *)
(* "*** Gave up! Passed only 4988 tests" *)

(* Above, we test if our evaluation succeeds, i.e. "eval" function returns "Some" value.
    From the definition of "eval", it fails in two cases: if the expression contains a binary expression 
    on a function pointer; or if the expression branches on a function pointer.
*)

(* Both branching and operating on function pointers may happen in two cases: when
    a function pointer is directly used, or an identifier which evaluates to a function pointer
    is used. *)

(* To generate expressions which successfully evaluate I restrict these two cases.
    Similar to [TestingStaticIFC], I first define generators for "leaves": expressions of size 0.
    In our case, there are two such generators: one that permits all expressions, and the other which
    only allows non-pointer expressions. *)

Definition is_not_ptr (state : reg) (var : string) :=
  match apply state var with
  | N _ => true
  | FP _ => false
  end.

(* This generator creates leaves as numbers and identifiers, which evaluate to numbers  *)
Definition gen_exp_leaf_no_ptr (state : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
        (let not_ptrs := filter (is_not_ptr state) (map_dom (snd state)) in
         if seq.nilp not_ptrs then [] else
         [liftM AId (elems_ "X0"%string not_ptrs)] ) ).

Sample (P <- arbitrary ;; 
       exp <- gen_exp_leaf_no_ptr P;; 
       ret (P, exp)).

(* This generator allows numbers, function pointers and all variables *)
Definition gen_exp_leaf (state : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;; 
         liftM FPtr arbitrary ;;; 
         (let vars := map_dom (snd state) in
          if seq.nilp vars then [] else
          [liftM AId (elems_ "X0"%string vars)] )).

(* I then define generators for expressions of a given size. Similarly,
    there are two generators: one that allows all expressions, and one which
    produces expressions without pointers. *)

Fixpoint gen_exp_no_ptr (sz : nat) (state : reg) : G exp :=
  match sz with
  | O => gen_exp_leaf_no_ptr state
  | S sz' => 
      freq [ (2, gen_exp_leaf_no_ptr state);
             (sz, liftM3 ABin arbitrary (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state));
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state))
          ]
  end.

Fixpoint gen_exp1 (sz : nat) (state : reg) : G exp :=
  match sz with 
  | O => gen_exp_leaf state
  | S sz' => 
          freq [ 
            (2, gen_exp_leaf state);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => liftM2 (ABin BinEq) (gen_exp1 sz' state) (gen_exp1 sz' state)
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp1 sz' state) (gen_exp1 sz' state))
          ]
  end.

(* Notice, that a "gen_exp" generator calls non-pointer "gen_exp_no_ptr" generator when branching and
  when performing a binary operation other than "BinEq" (equality is allowed on function pointers). *)

Sample (P <- arbitrary;;
        a <- gen_exp1 4 P;;
        ret (P, a)).

QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll (gen_exp1 4 state) (fun (exp : exp) =>
            implication (is_some (eval state exp)) true))).
(* "+++ Passed 10000 tests (382 discards)" *)

(* Better, but we still get discards. These cases are when the equality is generated between pointer
  and non-pointer. The following generator accounts for that: *)

Fixpoint gen_exp (sz : nat) (state : reg) : G exp :=
  match sz with 
  | O => gen_exp_leaf state
  | S sz' => 
          freq [ 
             (2, gen_exp_leaf state);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state))
                    (liftM2 (ABin BinEq) (liftM FPtr arbitrary) (liftM FPtr arbitrary))
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr sz' state) (gen_exp_no_ptr sz' state)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr sz' state) (gen_exp sz' state) (gen_exp sz' state))
          ]
  end.

(* QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll (gen_exp 4 state) (fun (exp : exp) => is_some (eval state exp)))). *)
(* "+++ Passed 10000 tests (0 discards)" *)

(* Now we generate expressions, where we only branch on numbers and identifiers evaluating to numbers,
  and a binary operation allowed for function pointers is only equality. *)

Compute (proc_hd [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Definition gen_exp_leaf_wf (vars: list string) (pst: list nat) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
         liftM FPtr (elems_ 0 (proc_hd pst)) ;;;
         if seq.nilp vars then [] else [liftM AId (elems_ "X0"%string vars)] ).

(* We then generate the actual expressions. *)
(* The restrictions on "well-formed" expressions are more relaxed then on those which actually evaluate. *)
(* For instance, "well-formedness" does not consider if we add a number or a function pointer. *)
Fixpoint gen_exp_wf (vars: list string) (sz : nat) (pst: list nat) : G exp :=
  match sz with 
  | O => gen_exp_leaf_wf vars pst
  | S sz' => 
          freq [
             (2, gen_exp_leaf_wf vars pst);
             (sz, liftM3 ABin arbitrary (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst));
             (sz, liftM3 ACTIf (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst))
          ]
  end.

(* We further generate each type of instructions. *)

Definition gen_asgn_wf (vars: list string) (pst: list nat) : G inst :=
  if seq.nilp vars
  then ret <{ skip }> 
  else
    x <- elems_ "X0"%string vars;;
    a <- gen_exp_wf vars 1 pst;;
    ret <{ x := a }>.

Definition gen_branch_wf (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  let non_proc_labels := list_minus (seq 0 (pl - 1)) (proc_hd pst) in
  match non_proc_labels with
  | nil => ret <{ skip }>
  | hd :: tl =>
    e <- gen_exp_wf vars 1 pst;;
    l <- elems_ hd non_proc_labels;; (* 0 is unreachable *)
    ret <{ branch e to l }>
  end.

Sample (gen_branch_wf ex_vars 8 [3; 3; 1; 1]).

Definition gen_jump_wf (pl: nat) (pst: list nat): G inst :=
  let non_proc_labels := list_minus (seq 0 (pl - 1)) (proc_hd pst) in
  match non_proc_labels with
  | nil => ret <{ skip }>
  | hd :: _ =>
    l <- elems_ hd non_proc_labels ;; (* 0 is unreachable *)
    ret <{ jump l }>
  end.

Sample (gen_jump_wf 8 [3; 3; 1; 1]).

Definition gen_load_wf (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  e <- gen_exp_wf vars 1 pst;;
  x <- elems_ "X0"%string vars;;
  ret <{ x <- load[e] }>.

Sample (gen_load_wf ex_vars 8 [3; 3; 1; 1]).

Definition gen_store_wf  (vars: list string) (pl: nat) (pst: list nat) : G inst :=
  e1 <- gen_exp_wf vars 1 pst;;
  e2 <- gen_exp_wf vars 1 pst;;
  ret <{ store[e1] <- e2 }>.

Sample (gen_store_wf ex_vars 8 [3; 3; 1; 1]).

(* SOONER: fix -> # of procedure is needed. *)
Definition gen_call_wf (pst: list nat) : G inst :=
  (* l <- gen_exp_wf vars pl pst;; *)
  l <- elems_ 0 (proc_hd pst);;
  ret <{ call (FPtr l) }>.

Sample (gen_call_wf [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Sample (vectorOf 1 (gen_call_wf [3; 3; 1; 1])).

Definition gen_inst (gen_asgn : list string -> list nat -> G inst)
                    (gen_branch : list string -> nat -> list nat -> G inst)
                    (gen_jump : nat -> list nat -> G inst)
                    (gen_load : list string -> nat -> list nat -> G inst)
                    (gen_store : list string -> nat -> list nat -> G inst)
                    (gen_call : list nat -> G inst)
                    (vars: list string) (sz:nat) (pl: nat) (c: list nat) : G inst :=
  freq
    [ (1, ret ISkip);
         (1, ret IRet);
         (sz, gen_asgn vars c);
         (sz, gen_branch vars pl c); 
         (sz, gen_jump pl c);
         (sz, gen_load vars pl c);
         (sz, gen_store vars pl c);
         (sz, gen_call c) ].

Definition gen_inst_wf (vars: list string) (sz pl: nat) (pst: list nat) : G inst :=
  gen_inst gen_asgn_wf gen_branch_wf gen_jump_wf
           gen_load_wf gen_store_wf gen_call_wf vars sz pl pst.

Sample (gen_inst_wf ex_vars 8 8 [3; 3; 1; 1]).

(* We further generate the blocks. Here, "bsz" is number of instructions per block, "pl" is program length and
  "pst" are the labels of procedure heads. *)
Definition gen_blk_wf (vars: list string) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wf vars bsz pl pst).

Sample (gen_blk_wf ex_vars 8 8 [3; 3; 1; 1]).

(* Similarly, we generate procedures. This Here, "psz" is the number of blocks in the program, and other
  paramaters are the same as for "_gen_blk_wf". *)
Fixpoint gen_proc_tail_wf (vars: list string) (psz bsz pl: nat) (pst: list nat) : G prog :=
  match psz with
  | O => ret []
  | S psz' => 
    blk <- gen_blk_wf vars bsz pl pst;;
    rest <- gen_proc_tail_wf vars psz' bsz pl pst;;
    (* Note: all blocks generated by this function are not head of procedures ("false" flag for blocks) *)
    ret ((blk, false) :: rest)
  end.

Sample (gen_proc_tail_wf ex_vars 3 3 8 [3; 3; 1; 1]).

Definition gen_proc_wf (vars: list string) (psz bsz pl: nat) (pst: list nat) : G prog :=
  match psz with
  | O => ret [] (* unreachable *)
  | S psz' => 
    blk <- gen_blk_wf vars bsz pl pst;;
    rest <- gen_proc_tail_wf vars psz' bsz pl pst;;
    ret ((blk, true) :: rest)
  end.

Sample (gen_proc_wf ex_vars 3 3 3 [3; 3; 1; 1]).

(* We further generate a program. A program in our setting has the same structure as the procedure, and is only
  separated in procedures by procedure heads. *)
Definition _gen_prog_wf (vars: list string) (pl bsz: nat) (pst : list nat) : G prog :=
  List.fold_left 
    (fun (a : G prog) proc_size => acc <- a;; proc <- gen_proc_wf vars proc_size bsz pl pst;; ret (acc ++ proc)) 
    pst (ret []).

Sample (_gen_prog_wf ex_vars 8 3 [3; 3; 1; 1]).

Definition gen_prog_wf_example :=
  let bsz := 3%nat in
  let pl := 8%nat in
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl bsz pst.

Sample (gen_prog_wf_example).

Definition gen_prog_wf_example' :=
  let pl := 8%nat in
  let bsz := 3%nat in
  let pst := [3;3;1;1] in
  _gen_prog_wf ex_vars pl bsz pst.

Definition test_wf_example' : G bool :=
  prog <- gen_prog_wf_example';;
  ret (wf prog).

Sample (vectorOf 1 test_wf_example').

Definition gen_prog_wf :=
  pl <- choose(1, 8);;
  bsz <- choose(3, 5);;
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl bsz pst.

QuickChick (forAll (gen_prog_wf) (fun (p : prog) => wf p)).

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

QuickChick (forAll (gen_prog_wf) (fun (p : prog) => wf (uslh_prog p))).
