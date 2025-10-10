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
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Export MonadNotation. Open Scope monad_scope.
From SECF Require Import PSlib.
From Coq Require Import String.

From SECF Require Import Utils.
From SECF Require Import ListMaps.
Require Import Coq.Classes.EquivDec.

(** The factoring of expressions is taken from the latest SpecCT chapter *)

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
  | BinEq => bool_to_nat (n1 =? n2)
  | BinLe => bool_to_nat (n1 <=? n2)
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp)
  | ACTIf (b : exp) (e1 e2 : exp)
  | FPtr (l : nat). (* <- NEW: function pointer to procedure at label [l] *)

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
    except the notation for [be?e1:e2] and [&l] which are new: *)
Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".
Definition msf : string := "msf".
Definition callee : string := "callee".

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

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2)
                 (in custom com at level 20, no associativity).

Notation "'&' l"   := (FPtr l)
                        (in custom com at level 75,
                          l constr at level 0, right associativity).

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.

(** Now to the first interesting part, values instead of just numbers: *)

(* Inductive val : Type := *)
(*   | N (n:nat) *)
(*   | FP (l:nat). (* <- NEW: function pointer to procedure at label [l] *) *)

(** Since type mismatches are now possible, evaluation of expressions can now
    fail, so the [eval] function is in the option monad. *)

Definition to_nat (v:val) : option nat :=
  match v with
  | N n => Some n
  | FP _ => None
  end.

Definition to_fp (v:val) : option nat :=
  match v with
  | FP l => Some l
  | N _ => None
  end.

Definition eval_binop (o:binop) (v1 v2 : val) : option val :=
  match v1, v2 with
  | N n1, N n2 => Some (N (eval_binop_nat o n1 n2))
  | FP l1, FP l2 =>
      match o with
      | BinEq => Some (N (bool_to_nat (l1 =? l2)))
      | _ => None (* Function pointers can only be tested for equality *)
      end
  | _, _ => None (* Type error *)
  end.

Definition reg := total_map val.

Fixpoint eval (st : reg) (e: exp) : option val :=
  match e with
  | ANum n => ret (N n)
  | AId x => ret (apply st x)
  | ABin b e1 e2 =>
      v1 <- eval st e1;;
      v2 <- eval st e2;;
      eval_binop b v1 v2
  | <{b ? e1 : e2}> =>
      v1 <- eval st b;;
      n1 <- to_nat v1;; (* Can't branch on function pointers *)
      if not_zero n1 then eval st e1 else eval st e2
  | <{&l}> => ret (FP l)
  end.

(* PROPERTY: forAll e st, is_some (eval st e) ==> True
   will show we need custom generators *)

Inductive inst : Type :=
  | ISkip
  | IAsgn (x : string) (e : exp)
  | IBranch (e : exp) (l : nat)
  | IJump (l : nat)
  | ILoad (x : string) (a : exp)
  | IStore (a : exp) (e : exp)
  | ICall (fp:exp)
  | ICTarget
  | IRet.

Notation "'skip'"  :=
  ISkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (IAsgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "'branch' e 'to' l"  := (* SOONER: get rid of the [to] *)
  (IBranch e l)
     (in custom com at level 0, e custom com at level 85,
      l constr at level 0, no associativity) : com_scope.
Notation "'jump' l"  :=
  (IJump l)
     (in custom com at level 0,
      l constr at level 0, no associativity) : com_scope.
Notation "x '<-' 'load[' a ']'"  :=
  (ILoad x a)
     (in custom com at level 0, x constr at level 0,
      a custom com at level 85, no associativity) : com_scope.
Notation "'store[' a ']'  '<-' e"  :=
  (IStore a e)
     (in custom com at level 0, a custom com at level 0,
      e custom com at level 85,
         no associativity) : com_scope.
Notation "'call' e" :=
  (ICall e)
    (in custom com at level 89, e custom com at level 99) : com_scope.
Notation "'ctarget'"  :=
  ICTarget (in custom com at level 0) : com_scope.
Notation "'ret'"  :=
  IRet (in custom com at level 0) : com_scope.

Definition prog := list (list inst * bool).

(** The inner [list inst] is a basic block, and the [bool] is telling us if the
    basic block is a procedure start. *)

Notation "'i[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (in custom com at level 89, x custom com at level 99,
      y custom com at level 99, no associativity) : com_scope.

Check <{{ skip }}>.
Check <{{ i[skip ; skip ; skip] }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Check <{ true && ~(false && true) }>.
(* SOONER: need tests for new notations *)
(* Check <{{ if true then skip else skip end }}>. *)
(* Check <{{ if true && true then skip; skip else skip; X:=X+1 end }}>. *)
(* Check <{{ while Z <> 0 do Y := Y * Z; Z := Z - 1 end }}>. *)
Check <{{ call 0 }}>.
Check <{{ ctarget }}>.
Check <{{ ret }}>.
Check <{{ branch 42 to 42 }}>.
Check <{{X<-load[8]}}>.
Check <{{store[X + Y]<- (Y + 42)}}>.

Definition cptr : Type := nat * nat. (* label(=(basic) block identifier) and offset *)

Definition mem := list val.

Definition cfg : Type := ((cptr*reg)*mem)*list cptr. (* (pc, register set, memory, stack frame) *)

Inductive observation : Type :=
  | OBranch (b:bool)
  | OLoad (n:nat)
  | OStore (n:nat)
  | OCall (v:val). (* we allow speculative calls to arbitrary values;
                      see Spectre 1.1 discussion in MiniCET.md *)

Definition obs := list observation.

Definition observation_eqb (os1 : observation) (os2 : observation) : bool :=
  match os1, os2 with
  | OBranch b, OBranch b' => Bool.eqb b b'
  | OLoad i, OLoad i' => (i =? i')
  | OStore i, OStore i' => (i =? i')
  | OCall v, OCall v' => match v, v' with
                        | N n, N n' => (n =? n')
                        | FP l, FP l' => (l =? l')
                        | _, _ => false
                        end
  | _, _ => false
  end.

Definition obs_eqb (o1 : obs) (o2 : obs) : bool :=
  forallb (fun '(os1, os2) => observation_eqb os1 os2) (List.combine o1 o2).

Definition fetch (p:prog) (pc:cptr) : option inst :=
  let '(l,o) := pc in
  r <- nth_error p l;;
  nth_error (fst r) o.

Notation "p '[[' pc ']]'" := (fetch p pc).

Definition inc (pc:cptr) : cptr :=
  let '(l,o) := pc in (l,o+1).

Notation "pc '+' '1'" := (inc pc).

Definition step (p:prog) (c:cfg) : option (cfg * obs) :=
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{skip}}> | <{{ctarget}}> =>
      ret ((pc+1, r, m, sk), [])
  | <{{x:=e}}> =>
      v <- eval r e;;
      ret ((pc+1, (x !-> v; r), m, sk), [])
  | <{{branch e to l}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      let b := not_zero n in
      ret ((if b then (l,0) else pc+1, r, m, sk), [OBranch b])
  | <{{jump l}}> =>
      ret (((l,0), r, m, sk), [])
  | <{{x<-load[e]}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      v' <- nth_error m n;;
      ret ((pc+1, (x !-> v'; r), m, sk), [OLoad n])      
  | <{{store[e]<-e'}}> =>
      v <- eval r e;;
      n <- to_nat v;;
      v' <- eval r e';;
      ret ((pc+1, r, upd n m v', sk), [OStore n])
  | <{{call e}}> =>
      v <- eval r e;;
      l <- to_fp v;;
      ret (((l,0), r, m, (pc+1)::sk), [OCall (FP l)])
  | <{{ret}}> =>
      pc' <- hd_error sk;;
      ret ((pc', r, m, tl sk), [])
  end.

(* Morally state+output monad hidden in here: step p >> steps f' p  *)
Fixpoint steps (f:nat) (p:prog) (c:cfg) : option (cfg * obs) :=
  match f with
  | S f' =>
      co1 <- step p c;;
      let '(c1,o1) := co1 in
      co2 <- steps f' p c1;;
      let '(c2,o2) := co2 in
      ret (c2, o1++o2)
  | 0 => ret (c,[])
  end.

(** Speculative semantics *)

Inductive direction : Type :=
  | DBranch (b':bool)
  | DCall (lo:cptr).

Definition dirs := list direction.

Definition spec_cfg : Type := ((cfg * bool) * bool).

Definition is_true (b:bool) : option unit :=
  if b then Some tt else None.

Definition is_false (b:bool) : option unit :=
  if b then None else Some tt.

Definition is_dbranch (d:direction) : option bool :=
  match d with
  | DBranch b => Some b
  | _ => None
  end.

Definition is_dcall (d:direction) : option cptr :=
  match d with
  | DCall pc => Some pc
  | _ => None
  end.

Definition if_some {a:Type} (o:option a) (f:a->bool) : bool :=
  match o with
  | Some x => f x
  | None => true
  end.

Definition spec_step (p:prog) (sc:spec_cfg) (ds:dirs) : option (spec_cfg * dirs * obs) :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  i <- p[[pc]];;
  match i with
  | <{{branch e to l}}> =>
      is_false ct;;
      d <- hd_error ds;;
      b' <- is_dbranch d;;
      v <- eval r e;;
      n <- to_nat v;;
      let b := not_zero n in
      let ms' := ms || negb (Bool.eqb b b') in 
      let pc' := if b' then (l, 0) else (pc+1) in
      ret ((((pc', r, m, sk), ct, ms'), tl ds), [OBranch b])
  | <{{call e}}> =>
      is_false ct;;
      d <- hd_error ds;;
      pc' <- is_dcall d;;
      v <- eval r e;;
      (* we allow speculative calls to arbitrary values;
         see Spectre 1.1 discussion in MiniCET.md *)
      is_true (if_some (to_nat v) (fun _ => ms));;
      let ms' := ms || (if_some (to_fp v)
                          (fun l => negb ((fst pc' =? l) && (snd pc' =? 0)))) in
      ret ((((pc', r, m, sk), true, ms'), tl ds), [OCall v])
  | <{{ctarget}}> =>
      is_true ct;; (* ctarget can only run after call? (CET) Maybe not? *)
      ret (((pc+1, r, m, sk), false, ms), ds, [])
  | _ =>
      is_false ct;;
      co <- step p c;;
      let '(c',o) := co in
      ret ((c',false,ms), ds, o)
  end.

Fixpoint spec_steps (f:nat) (p:prog) (c:spec_cfg) (ds:dirs)
  : option (spec_cfg * dirs * obs) :=
  match f with
  | S f' =>
      cdo1 <- spec_step p c ds;;
      let '(c1,ds1,o1) := cdo1 in
      cdo2 <- spec_steps f' p c1 ds1;;
      let '(c2,ds2,o2) := cdo2 in
      ret (c2,ds2,o1++o2)
  | 0 =>
      None (* Q: Do we need more precise out-of-fuel error here? *)
  end.

(* SOONER: define monad used by uslh *)

Definition M (A: Type) := nat -> A * prog.

Definition uslh_ret {A: Type} (x: A) : M A :=
  fun c => (x, []).

Definition uslh_bind {A B: Type} (m: M A) (f: A -> M B) : M B :=
  fun c =>
    let '(r, p) := m c in
    let '(r', p') := f r (c + Datatypes.length p) in
    (r', p ++ p').

#[export] Instance monadUSLH : Monad M :=
  { ret := @uslh_ret;
    bind := @uslh_bind
  }.

(* No mapM in ExtLib, seems it got removed: https://github.com/rocq-community/coq-ext-lib/commit/ef2e35f43b2d1db4cb64188e9521948fdd1e0527 *)
(* YH: We can use mapGen from QuickChick library instead.  *)
Definition mapM {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  sequence (List.map f l).

Definition concatM {A: Type} (m: M (list (list A))) : M (list A) :=
  xss <- m;; ret (List.concat xss).

Definition add_block (bl: list inst) (c: nat) := (c, [(bl, false)]).

Definition add_block_M (bl: list inst) : M nat :=
  fun c => add_block bl c.

(* SOONER: Try to use this to define our new uslh *)

Definition uslh_inst (i: inst) : M (list inst) :=
  match i with
  | <{{ctarget}}> => ret [<{{skip}}>]
  | <{{x<-load[e]}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{x<-load[e']}}>]
  | <{{store[e] <- e1}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{store[e'] <- e1}}>]
  | <{{branch e to l}}> =>
      let e' := <{ (msf=0) && e }> in (* if mispeculating always pc+1 *)
      l' <- add_block_M <{{ i[msf := ~e' ? 1 : msf; jump l] }}>;;
      ret <{{ i[branch e' to l'; msf := e' ? 1 : msf] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &0 : e }> in
      ret <{{ i[callee:=e'; call e'] }}>
  | _ => ret [i]
  end.

Definition uslh_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  bl' <- concatM (mapM uslh_inst bl);;
  if is_proc then
    ret (<{{ i[ctarget; msf := (callee = &l) ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition uslh_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM uslh_blk idx_p (Datatypes.length p) in
  (p' ++ newp).

Definition procedure : Type := list (list inst * bool).

Fixpoint group_by_proc_impl (p: prog) (current_proc_acc: procedure) : list procedure :=
  match p with
  | [] => match current_proc_acc with
         | [] => []
         | _ => [rev current_proc_acc]
         end
  | (blk, is_proc) :: tl =>
      if is_proc then
        match current_proc_acc with
        | [] => group_by_proc_impl tl [(blk, is_proc)]
        | _ => (rev current_proc_acc) :: group_by_proc_impl tl [(blk, is_proc)]
        end
      else group_by_proc_impl tl ((blk, is_proc) :: current_proc_acc)
  end.

Definition group_by_proc (p: prog) : list procedure :=
  group_by_proc_impl p [].

Definition sample_prog_for_grouping : prog := [
  (nil, true);  (* Proc 1, Blk 0 *)
  (nil, false); (* Proc 1, Blk 1 *)
  (nil, false); (* Proc 1, Blk 2 *)
  (nil, true);  (* Proc 2, Blk 3 *)
  (nil, false); (* Proc 2, Blk 4 *)
  (nil, true)   (* Proc 3, Blk 5 *)
].

Compute (group_by_proc sample_prog_for_grouping).

Compute (Datatypes.length (group_by_proc sample_prog_for_grouping)).

Definition proc_map := (fun (x: procedure) => Datatypes.length x).

(* pst: list of # of blocks in each procedure *)
Definition pst_calc (p: prog) : list nat := (map proc_map (group_by_proc p)).

Compute (pst_calc sample_prog_for_grouping).

(* SOONER: Run some unit tests *)

(* Static checks for both source and target programs *)

Definition wf_label (p:prog) (is_proc:bool) (l:nat) : bool :=
  match nth_error p l with
  | Some (_,b) => Bool.eqb is_proc b (* also know l <? List.length p *)
  | None => false
  end.

Fixpoint wf_exp (p:prog) (e : exp) : bool :=
  match e with
  | ANum _ | AId _ => true
  | ABin _ e1 e2  | <{_ ? e1 : e2}> => wf_exp p e1 && wf_exp p e2
  | <{&l}> => wf_label p true l
  end.

Definition wf_inst (p:prog) (i : inst) : bool :=
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> => true
  | <{{_:=e}}> | <{{_<-load[e]}}> | <{{call e}}> => wf_exp p e
  | <{{store[e]<-e'}}> => wf_exp p e && wf_exp p e'
  | <{{branch e to l}}> => wf_exp p e && wf_label p false l
  | <{{jump l}}> => wf_label p false l
  end.

Definition wf_blk (p:prog) (blb : list inst * bool) : bool :=
  forallb (wf_inst p) (fst blb).

Definition wf (p:prog) : bool :=
  forallb (wf_blk p) p.

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

(* May (not) need separate check for no ctarget, only for source *)

(* ** Property testing of MiniCET *)

(* Simple utility function to check if a value is Some.
  TODO: Check if there is an Stdlib or Extlib function with the same
  functionality. *)
Definition is_some {A} (v : option A) : bool := match v with
  | Some _ => true
  | None => false
  end.
  
(** custom tactics *)

Ltac inv H := inversion H; subst; clear H.

(** Generators and shows *)

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

Derive (Arbitrary, Shrink) for binop.
Derive (Arbitrary, Shrink) for exp.
Derive (Arbitrary, Shrink) for inst.

(* Derive Show for binop. *)
(* Derive Show for exp. *)
(* Derive Show for inst. *)

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


Sample (arbitrarySized 1 : G binop).
Sample (arbitrarySized 2 : G binop).
Sample (arbitrarySized 1 : G exp).
Sample (arbitrarySized 1 : G inst).

Derive Show for val.

(* #[export] Instance showExp : Show exp := *)
(*   {show := *)
(*       (let fix showExpRec (a:exp) : string := *)
(*          match a with *)
(*          | AId i => String DoubleQuote (i ++ String DoubleQuote "") *)
(*          | ANum n => show n *)
(*          | ABin bop e1 e2 => "(" ++ showExpRec e1 ++ " " ++ show bop ++ " " ++ showExpRec e2 ++ ")" *)
(*          | ACTIf b e1 e2 => showExpRec b ++ " ? " ++ showExpRec e1 ++ " : " ++ showExpRec e2 *)
(*          | FPtr fp => "&" ++ show fp *)
(*          end *)
(*        in showExpRec)%string *)
(*    }. *)

(* As in [TestingStaticIFC.v], we generate a finite total map which we use as state. *)
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

(* [TestingStaticIFC.v]: The ;; notation didn't work with oneOf, probably related to monadic
   bind also using ;;. So I redefined the notation using ;;;. *)
Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.

Derive (Arbitrary, Shrink) for val.
Derive (Arbitrary, Shrink) for binop.
Derive (Arbitrary, Shrink) for exp.

(** The first unit test *)

(* The first property I test is the one proposed by Catalin, which shows how sane our
  generators are: *)
(* "forAll e st, is_some (eval st e) ==> True" *)

(* Tests with generators derived by QuickChick are almost fully discarded: *)
QuickChick (forAll arbitrary (fun (state : reg) =>
            forAll arbitrary (fun (exp : exp) =>
            implication (is_some (eval state exp)) true))).
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

Print binop.

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

Definition eitherOf {A} (a : G A) (b : G A) : G A := freq [(1, a); (1, b)].

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

(* QuickChick (forAll arbitrary (fun (state : reg) => *)
(*             forAll (gen_exp 4 state) (fun (exp : exp) => *)
(*             implication (is_some (eval state exp)) true))). *)
(* "+++ Passed 10000 tests (0 discards)" *)

(* Now we generate expressions, where we only branch on numbers and identifiers evaluating to numbers,
  and a binary operation allowed for function pointers is only equality. *)

(** Wf Program Generator *)

Fixpoint _gen_partition (fuel n: nat) : G (list nat) :=
  match fuel with
  | 0 => ret [n]
  | S fuel' =>
      match n with
      | O => ret []
      | S O => ret [1]
      | S (S n') => (k <- choose(1, n - 1);;
                     rest <- _gen_partition fuel' (n - k);;
                     ret (k :: rest))
      end
  end.

Definition gen_partition (n: nat) := _gen_partition n n.

Sample (gen_partition 8).

Definition gen_vars (len: nat) : G (list string) :=
  vectorOf len arbitrary.

Sample (gen_vars 5).

Definition ex_vars : list string :=
  ["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string].

Fixpoint proc_hd (pst: list nat) : list nat :=
  match pst with
  | [] => []
  | hd :: tl => 0 :: map (fun x => x + hd) (proc_hd tl)
  end.

Compute (proc_hd [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Definition gen_exp_leaf_wf (vars: list string) (pst: list nat) : G exp :=
  oneOf [liftM ANum arbitrary ;
         liftM FPtr (elems_ 0 (proc_hd pst));
         liftM AId (elems_ "X0"%string vars)].

Fixpoint gen_exp_wf (vars: list string) (sz : nat) (pst: list nat) : G exp :=
  match sz with 
  | O => gen_exp_leaf_wf vars pst
  | S sz' => 
          freq [
             (2, gen_exp_leaf_wf vars pst);
             (sz, binop <- arbitrary;;
                  liftM2 (ABin binop) (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst));
             (sz, liftM3 ACTIf (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst) (gen_exp_wf vars sz' pst))
          ]
  end.

Definition gen_asgn_wf (vars: list string) (pst: list nat) : G inst :=
  x <- elems_ "X0"%string vars;;
  a <- gen_exp_wf vars 1 pst;;
  ret <{ x := a }>.

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

Definition gen_branch_wf (vars: list string) (pl: nat) (pst: list nat) (default: nat) : G inst :=
  e <- gen_exp_wf vars 1 pst;;
  l <- elems_ default (list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ branch e to l }>.

Sample (gen_branch_wf ex_vars 8 [3; 3; 1; 1] 2).

Definition gen_jump_wf (pl: nat) (pst: list nat) (default: nat): G inst :=
  l <- elems_ default (list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ jump l }>.

Sample (gen_jump_wf 8 [3; 3; 1; 1] 2).

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

(* Definition gen_exp_leaf_ptr (pl: nat) (rs : reg) : G exp := *)
(*   oneOf (liftM FPtr (choose (0, pl));;; *)
(*          (let ptrs := filter (fun s => negb (is_not_ptr rs s)) (map_dom (snd rs)) in *)
(*           if seq.nilp ptrs then [] else *)
(*           [liftM AId (elems_ "X0"%string ptrs)] )). *)

(* Fixpoint gen_exp_ptr (sz : nat) (pl: nat) (rs : reg) : G exp := *)
(*   match sz with *)
(*   | O => gen_exp_leaf_ptr pl rs *)
(*   | S sz' => *)
(*           freq [ *)
(*              (2, gen_exp_leaf_ptr pl rs); *)
(*              (sz, liftM3 ACTIf (gen_exp_no_ptr sz' rs) (gen_exp_ptr sz' pl rs) (gen_exp_ptr sz' pl rs)) *)
(*           ] *)
(*   end. *)

(* SOONER: fix -> # of procedure is needed. *)
Definition gen_call_wf (pst: list nat) : G inst :=
  (* l <- gen_exp_wf vars pl pst;; *)
  l <- elems_ 0 (proc_hd pst);;
  ret <{ call (FPtr l) }>.

Sample (gen_call_wf [3; 3; 1; 1]).
(* = <{{ i[ 0; 3; 6; 7] }}> *)

Sample (vectorOf 1 (gen_call_wf [3; 3; 1; 1])).

Definition gen_inst (gen_asgn : list string -> list nat -> G inst)
                    (gen_branch : list string -> nat -> list nat -> nat -> G inst)
                    (gen_jump : nat -> list nat -> nat -> G inst)
                    (gen_load : list string -> nat -> list nat -> G inst)
                    (gen_store : list string -> nat -> list nat -> G inst)
                    (gen_call : list nat -> G inst)
                    (vars: list string) (sz:nat) (pl: nat) (c: list nat) : G inst :=
  let insts := 
    [ (1, ret ISkip);
         (1, ret IRet);
         (sz, gen_asgn vars c);
         (sz, gen_load vars pl c);
         (sz, gen_store vars pl c);
         (sz, gen_call c) ] in
  let non_proc_labels := list_minus (seq 0 (pl - 1)) (proc_hd c) in
  match non_proc_labels with
    (* There are only procedure heads or the size of the program is 0 *)
    | nil => freq_ (ret ISkip) insts
    (* There is at least one non procedure label *)
    | hd :: _ => freq_ (ret ISkip) (insts ++ [ (sz, gen_branch vars pl c hd); (sz, gen_jump pl c hd) ])
  end.

Definition gen_inst_wf (vars: list string) (sz pl: nat) (pst: list nat) : G inst :=
  gen_inst gen_asgn_wf gen_branch_wf gen_jump_wf
           gen_load_wf gen_store_wf gen_call_wf vars sz pl pst.

Sample (gen_inst_wf ex_vars 8 8 [3; 3; 1; 1]).

(* bsz: # of instruction in blk *)
Definition gen_blk_wf (vars: list string) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wf vars bsz pl pst).

Sample (gen_blk_wf ex_vars 8 8 [3; 3; 1; 1]).

(* fsz: # of blocks in procedure *)
(* blk length = 8 *)
Fixpoint _gen_proc_wf (vars: list string) (fsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => blk <- gen_blk_wf vars 3 pl pst;;
             rest <- _gen_proc_wf vars fsz' pl pst;;
             ret ((blk, false) :: rest)
  end.

Sample (_gen_proc_wf ex_vars 3 8 [3; 3; 1; 1]).

(* blk length = 8 *)
Definition gen_proc_wf (vars: list string) (fsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => blk <- gen_blk_wf vars 3 pl pst;;
             rest <- _gen_proc_wf vars fsz' pl pst;;
             ret ((blk, true) :: rest)
  end.

Sample (gen_proc_wf ex_vars 3 3 [3; 3; 1; 1]).

Fixpoint _gen_prog_wf (vars: list string) (pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wf vars hd pl pst;;
              tl_proc <- _gen_prog_wf vars pl pst tl;;
              ret (hd_proc ++ tl_proc)
  end.

Sample (_gen_prog_wf ex_vars 8 [3; 3; 1; 1] [3; 3; 1; 1]).

Definition gen_prog_wf_example :=
  let pl := 8%nat in
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl pst pst.

Sample (gen_prog_wf_example).

Definition gen_prog_wf_example' :=
  let pl := 8%nat in
  let pst := [3;3;1;1] in
  _gen_prog_wf ex_vars pl pst pst.

Definition test_wf_example' : G bool :=
  prog <- gen_prog_wf_example';;
  ret (wf prog).

Sample (vectorOf 1 test_wf_example').

Definition gen_prog_wf :=
  pl <- choose(1, 8);;
  pst <- gen_partition pl;;
  _gen_prog_wf ex_vars pl pst pst.

QuickChick (forAll (gen_prog_wf) (fun (p : prog) => wf p)).

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

QuickChick (forAll (gen_prog_wf) (fun (p : prog) => wf (uslh_prog p))).


(* YH: The current expression generator depends on a specific register set.
   This structures can be problematic because registers changes during program execution.
   To define expressions that "always succeeds", it probably be better to make type system. *)

(* initial state X = 1, Y = 4
   code: X = FP 42
         Z = X + Y // error! *)

(** Type system for soundenss *)

Inductive ty : Type :=
| TNum | TPtr.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Definition rctx := total_map ty.
Definition tmem := list ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum | TPtr, TPtr => true
                               | _, _ => false
                               end.

Definition filter_vars_by_ty (t: ty) (c: rctx) : list string :=
  filter (fun x => ty_eqb (apply c x) t) (map_dom (snd c)).

Definition is_ptr (c : rctx) (var : string) :=
  match apply c var with
  | TPtr => true
  | _ => false
  end.

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

Fixpoint gen_exp_wt2 (t: ty) (sz: nat) (c: rctx) (pst: list nat) : G exp :=
  match t with
  | TNum => gen_exp_no_ptr_wt sz c pst
  | TPtr => gen_exp_ptr_wt sz c pst
  end.

Definition gen_val_wt (t: ty) (pst: list nat) : G val :=
  match t with
  | TNum => liftM N arbitrary
  | TPtr => match pst with
           | [] => ret (FP 0)
           | p::pst' => liftM FP (elems_ p (p::pst'))
           end
  end.

Definition gen_wt_reg (c: rctx) (pst: list nat) : G reg :=
  let wt_vars := snd c in
  let gen_binds := mapGen (fun '(s, t) =>  (v <- gen_val_wt t pst;; ret (s, v))) wt_vars in
  dv <- gen_val_wt (fst c) pst;;
  b <- gen_binds;;
  ret (dv, b).

QuickChick (forAll arbitrary (fun (c : rctx) =>
            forAll (gen_wt_reg c [3; 3; 1; 1]) (fun (state: reg) =>
            forAll (gen_exp_wt 4 c [3; 3; 1; 1]) (fun (exp : exp) =>
            implication (is_some (eval state exp)) true)))).

Definition gen_asgn_wt (t: ty) (c: rctx) (pst: list nat) : G inst :=
  let tlst := filter (fun '(_, t') => ty_eqb t t') (snd c) in
  let vars := map_dom tlst in
  if seq.nilp vars
  then ret <{ skip }>
  else
    x <- elems_ "X0"%string vars;;
    a <- gen_exp_wt2 t 1 c pst;;
    ret <{ x := a }>.

Sample (c <- arbitrary;; i <- gen_asgn_wt TPtr c [3; 3; 1; 1];; ret (c, i)).

Definition gen_branch_wt (c: rctx) (pl: nat) (pst: list nat) (default : nat) : G inst :=
  let vars := (map_dom (snd c)) in
  let jlst := (list_minus (seq 0 pl) (proc_hd pst)) in
  e <- gen_exp_wt2 TNum 1 c pst;;
  l <- elems_ default jlst;; (* 0 is unreachable *)
  ret <{ branch e to l }>.

Sample (c <- arbitrary;; i <- gen_branch_wt c 8 [3; 3; 1; 1] 2;; ret (c, i)).

(* SAME: gen_jump_wf *)
Definition gen_jump_wt (pl: nat) (pst: list nat) (default : nat) : G inst :=
  gen_jump_wf pl pst default.

Sample (gen_jump_wt 8 [3; 3; 1; 1] 2).

Definition gen_load_wt (t: ty) (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  let tlst := filter (fun '(_, t') => ty_eqb t t') (snd c) in
  let vars := map_dom tlst in
  (* SOONER: YH: now it just supports numbers. extend this later. *)
  let indices := seq 0 (Datatypes.length tm) in
  let idx_tm := combine indices tm in
  let idxt := fst (split (filter (fun '(_, t') => ty_eqb t t') idx_tm)) in
  if (seq.nilp vars) || (seq.nilp idxt)
  then ret <{ skip }>
  else
    n <- elems_ 0 idxt;;
    x <- elems_ "X0"%string vars;;
    ret <{ x <- load[ANum n] }>.

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_load_wt TPtr c tm 8 [3; 3; 1; 1];; ret (c, tm, i)).

Definition gen_store_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  let indices := seq 0 (Datatypes.length tm) in
  let idx_tm := combine indices tm in
  if seq.nilp idx_tm
  then ret <{ skip }>
  else
    '(n, t) <- elems_ (0, TNum) idx_tm;;
    e2 <- gen_exp_wt2 t 1 c pst;;
    ret <{ store[ANum n] <- e2 }>.

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_store_wt c tm 8 [3; 3; 1; 1];; ret (c, tm, i)).

Definition gen_call_wt (pst: list nat) : G inst :=
  gen_call_wf pst.

Sample (gen_call_wt [3; 3; 1; 1]).

Definition _gen_inst_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                        (gen_branch : rctx -> nat -> list nat -> nat -> G inst)
                        (gen_jump : nat -> list nat -> nat -> G inst)
                        (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_call : list nat -> G inst)
                        (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  let insts := 
     [ (1, ret ISkip);
         (1, ret IRet);
         (sz, t <- arbitrary;; gen_asgn t c pst);
         (sz, t <- arbitrary;; gen_load t c tm pl pst);
         (sz, gen_store c tm pl pst);
         (sz, gen_call pst) ] in
  let non_proc_labels := list_minus (seq 0 pl) (proc_hd pst) in
  match non_proc_labels with
  | nil => freq_ (ret ISkip) insts
  | hd :: _ => freq_ (ret ISkip) (insts ++ [ (2, gen_branch c pl pst hd)(* ; (sz, gen_jump pl pst hd) *)])
  end.

(* redundant functions *)
Fixpoint gen_nonterm_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                        (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_call : list nat -> G inst)
                        (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  freq [ (1, ret ISkip);
         (sz, t <- arbitrary;; gen_asgn t c pst);
         (sz, t <- arbitrary;; gen_load t c tm pl pst);
         (sz, gen_store c tm pl pst);
         (sz, gen_call pst)].

Fixpoint _gen_term_wt (gen_branch : rctx -> nat -> list nat -> nat -> G inst)
                      (gen_jump : nat -> list nat -> nat -> G inst)
                      (c: rctx) (tm: tmem) (* (sz:nat) *) (pl: nat) (pst: list nat) : G inst :=
  let non_proc_labels := list_minus (seq 0 pl) (proc_hd pst) in
  match non_proc_labels with
  | nil => ret IRet
  | hd :: _ => freq_ (ret IRet) ([(1, ret IRet) (* (sz, gen_branch c pl pst hd);  *) ; (2, gen_jump pl pst hd)])
  end.

Definition gen_term_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  _gen_term_wt gen_branch_wt gen_jump_wt c tm pl pst.

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_term_wt c tm 8 [3; 3; 1; 1];; ret (i)).

Definition gen_inst_wt (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  _gen_inst_wt gen_asgn_wt gen_branch_wt gen_jump_wt gen_load_wt gen_store_wt gen_call_wt
               c tm sz pl pst.

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_inst_wt c tm 3 8 [3; 3; 1; 1];; ret (c, tm, i)).

Definition gen_blk_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wt c tm bsz pl pst).

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_blk_wt c tm 5 8 [3; 3; 1; 1];; ret (c, tm, i)).

Definition _gen_blk_body_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf (bsz - 1) (gen_inst_wt c tm bsz pl pst).

Definition gen_blk_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  blk <- _gen_blk_body_wt c tm bsz pl pst;;
  term <- gen_term_wt c tm pl pst;;
  ret (blk ++ [term]).

Sample (tm <- arbitrary;; c <- arbitrary;; i <- gen_blk_with_term_wt c tm 5 8 [3; 3; 1; 1];; ret i).

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

QuickChick (forAll (basic_block_gen_example) (fun (blk: list inst) => (basic_block_checker blk))).

Fixpoint _gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => n <- choose (1, bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; proc <- _gen_proc_with_term_wt c tm 3 3 8 [3; 3; 1; 1];; ret proc).

Definition gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => n <- choose (1, bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; proc <- gen_proc_with_term_wt c tm 3 3 8 [3; 3; 1; 1];; ret proc).

Fixpoint _gen_prog_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_with_term_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_with_term_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; p <- _gen_prog_with_term_wt c tm 3 8 [3; 3; 1; 1] [3; 3; 1; 1];; ret  p).

Definition gen_prog_with_term_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_with_term_wt c tm bsz pl pst pst.

Definition prog_basic_block_checker (p: prog) : bool :=
  forallb (fun bp => (basic_block_checker (fst bp))) p.

QuickChick (forAll (gen_prog_with_term_wt_example 8) (fun (p: prog) => (prog_basic_block_checker p))).

(* fsz: # of blocks in procedure *)
(* blk: max # of instructions in blk *)
Fixpoint _gen_proc_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => n <- choose (1, bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm fsz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; proc <- _gen_proc_wt c tm 3 3 8 [3; 3; 1; 1];; ret (c, tm, proc)).

(* fsz: # of blocks in procedure *)
(* blk: max # of instructions in blk *)
Definition gen_proc_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret [] (* unreachable *)
  | S fsz' => n <- choose (1, bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm fsz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; proc <- gen_proc_wt c tm 3 3 8 [3; 3; 1; 1];; ret (c, tm, proc)).

Fixpoint _gen_prog_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Sample (tm <- arbitrary;; c <- arbitrary;; p <- _gen_prog_wt c tm 3 8 [3; 3; 1; 1] [3; 3; 1; 1];; ret  p).

Definition gen_prog_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_wt c tm bsz pl pst pst.

Sample (gen_prog_wt_example 5).

Definition test_wt_example : G bool :=
  prog <- gen_prog_wt_example 8;;
  ret (wf prog).

Sample (vectorOf 1 test_wt_example).

Definition gen_prog_wt (bsz pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  _gen_prog_wt c tm bsz pl pst pst.

QuickChick (forAll (gen_prog_wt 3 8) (fun (p : prog) => (wf p))).

QuickChick (forAll (gen_prog_wt 3 8) (fun (p : prog) => (wf p))).

(* PROPERTY: uslh produces well-formed programs from well-formed programs
   probably need generator for well-formed programs *)

QuickChick (forAll (gen_prog_wt 3 8) (fun (p : prog) => (wf (uslh_prog p)))).

(* "+++ Passed 10000 tests (0 discards)" *)

Fixpoint ty_exp (c: rctx) (e: exp) : option ty :=
  match e with
  | ANum _ => Some TNum
  | FPtr _ => Some TPtr
  | AId x => Some (apply c x)
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

Fixpoint ty_inst (c: rctx) (tm: tmem) (p: prog) (i: inst) : bool :=
  match i with
  | ISkip | ICTarget | IRet => true
  | IAsgn x e => match ty_exp c e with
                | Some t => ty_eqb (apply c x) t
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
                    | Some t => ty_eqb (apply c x) t
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

Definition gen_prog_wt2 (bsz pl: nat) : G (rctx * tmem * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_wt c tm bsz pl pst pst;;
  ret (c, tm, p).

QuickChick (forAll (gen_prog_wt2 3 8) (fun '(c, tm, p) => ((ty_prog c tm p) && (wf p)))).

(** Relative Security *)

(* Taint Tracker for input pairs *)

Notation label := PSlib.label.
Notation apply := ListMaps.apply.
Definition join (l1 l2 : label) : label := l1 && l2.

Definition pub_vars := total_map label.
Definition pub_arrs := list label. (* true: public, false: secret *)

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
  List.fold_left (fun l a => join l (apply P a)) (vars_exp e) public.

(* Copied from TestingFlexSLH.v *)

(* For testing relative security we do taint tracking of sequential executions
   (as a variant of Lucie's interpreter). We use this to track which initial
   values of variables and arrays affect CT observations. *)

Definition reg_id := string.
Definition mem_addr := nat.

Definition taint : Type := list (reg_id + mem_addr).

#[export] Instance showTaint : Show (reg_id + mem_addr) :=
  {show := fun x =>
     match x with
     | inl x => show x
     | inr a => show a
     end}.

Definition sum_eqb (s1 s2 : (reg_id + mem_addr)) : bool :=
  match s1, s2 with
  | inl x1, inl x2 => String.eqb x1 x2
  | inr x1, inr x2 => Nat.eqb x1 x2
  | _, _ => false
  end.

Definition join_taints t1 t2 := remove_dupes sum_eqb (t1 ++ t2).

Module TaintTracking.

Definition tcptr := taint.
Definition treg := total_map taint.
Definition tamem := list taint.
Definition tstk := list tcptr.

Definition tcfg := (tcptr * treg * tamem * tstk)%type.
Definition input_st : Type := cfg * tcfg * taint.

(* Currently, we generate UB-free programs based on abstract states.
   Going forward, we'll transition to execution-based program
   generation, which also produces UB-free programs. Therefore,
   we don't need to worry about UB in either case. *)

Variant output_st (A : Type) : Type :=
  | RStep : A -> obs -> input_st -> output_st A
  | RError : obs -> input_st -> output_st A
  | RTerm : obs -> input_st -> output_st A.

Record evaluator (A : Type) : Type := mkEvaluator
  { evaluate : input_st -> output_st A }.

(* An 'evaluator A'. This is the monad.
   It transforms an input state into an output state, returning an A. *)
(* An interpreter is a special kind of evaluator *)
Definition interpreter: Type := evaluator unit.

(* Generic monad operators *)
#[export] Instance monadEvaluator: Monad evaluator :=
  { ret := fun A value => mkEvaluator A (fun (ist : input_st) => RStep A value [] ist);
    bind := fun A B e f =>
      mkEvaluator B (fun (ist : input_st) =>
        match evaluate A e ist with
        | RStep _ value os1 ist'  =>
            match evaluate B (f value) ist' with
            | RStep _ value os2 ist'' => RStep B value (os1 ++ os2) ist''
            | RError _ os2 ist'' => RError B (os1 ++ os2) ist''
            | RTerm _ os2 ist'' => RTerm B (os1 ++ os2) ist''
            end
        | RError _ os ist' => RError B os ist'
        | RTerm _ os ist' => RTerm B os ist'
        end
      )
  }.

Fixpoint _calc_taint_exp (e: exp) (treg: total_map taint) : taint :=
  match e with
  | ANum _ | FPtr _ => []
  | AId x => apply treg x
  | ABin _ e1 e2 => join_taints (_calc_taint_exp e1 treg) (_calc_taint_exp e2 treg)
  | ACTIf e1 e2 e3 => join_taints (_calc_taint_exp e1 treg)
                                 (join_taints (_calc_taint_exp e2 treg) (_calc_taint_exp e3 treg))
  end.

Variant taint_ctx :=
  | CMem (n: nat)
  | CDefault.

(* None cases are unreachable. *)
Definition taint_step (i: inst) (c: cfg) (tc: tcfg) (tobs: taint) (tctx: taint_ctx) : option (tcfg * taint) :=
  let '(pc, rs, m, s) := c in
  let '(tpc, trs, tm, ts) := tc in
  match i with
  | <{ skip }> | <{ ctarget }> | <{ jump _ }> =>
      match tctx with
      | CDefault => Some (tc, tobs)
      | _ => None
      end
  | <{ x := e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tx := join_taints te tpc in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          Some (tc', tobs)
      | _ => None
      end
  | <{ branch e to l }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts) in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end
  | <{ x <- load[e] }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let tv := nth n tm [] in (* default case is unreachable: step already checked. *)
          let tx := (join_taints (join_taints te tv) tpc) in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          let tobs' := (join_taints (join_taints te tpc) tobs) in
          Some (tc', tobs')
      | _ => None
      end
  | <{ store[e] <- e' }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let te' := (_calc_taint_exp e' trs) in
          let tm_val := join_taints (join_taints te te') tpc in
          let tc' := (tpc, trs, upd n tm tm_val, ts) in
          let tobs' := join_taints (join_taints te tpc) tobs in
          Some (tc', tobs')
      | _ => None
      end
  | <{ call e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let ts' := tpc :: ts in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts') in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end
  | <{ ret }> =>
      match tctx with
      | CDefault =>
          let tpc' := hd [] ts in (* default case is unreachable: step already checked. *)
          let ts' := tl ts in
          let tc' := (tpc', trs, tm, ts') in
          Some (tc', tobs)
      | _ => None
      end
  end.

Definition get_ctx (rs: reg) (i: inst) : option taint_ctx  :=
  match i with
  | <{ x <- load[e] }> =>  v <- eval rs e;;
                         n <- to_nat v;;
                         Some (CMem n)
  | <{ store[e] <- e' }> => v <- (eval rs e);;
                          n <- to_nat v;;
                          Some (CMem n)
  | _ => Some CDefault
  end.

(* ret with empty stackframe *)
Definition final_cfg (p: prog) (c: cfg) : bool :=
  let '(pc, rs, m, stk) := c in
  match fetch p pc with
  | Some i => match i with
             | IRet => if seq.nilp stk then true else false
             | _ => false
             end
  | None => false
  end.

Definition step_taint_track (p: prog) : evaluator unit :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(c, tc, tobs) := ist in
    let '(pc, rs, m, s) := c in
    let '(tpc, trs, tm, ts) := tc in
    match step p c with
    | Some (c', os) =>
        match (fetch p pc) with
        | Some i => match get_ctx rs i with
                   | Some tctx => match taint_step i c tc tobs tctx with
                                 | Some (tc', tobs') => RStep _ tt os (c', tc', tobs')
                                 | _ => RError _ [] ist (* context is inconsistent. *)
                                 end
                   | _ => RError _ [] ist (* For now, unreachable *)
                   end
        | _ => RError _ [] ist
        end
    | None => if final_cfg p c
             then RTerm _ [] ist
             else RError _ [] ist
    end
    ).

Variant exec_result : Type :=
  | ETerm (st: input_st) (os: obs)
  | EError (st: input_st) (os: obs)
  | EOutOfFuel (st: input_st) (os: obs).

Fixpoint steps_taint_track (f: nat) (p: prog) (ist: input_st) (os: obs) : exec_result :=
  match f with
  | O => EOutOfFuel ist os
  | S f' =>
      match evaluate unit (step_taint_track p) ist with
      | RTerm _ os' ist' => ETerm ist' (os ++ os')
      | RError _ os' ist' => EError ist' (os ++ os')
      | RStep _ _ os' ist' => steps_taint_track f' p ist' (os ++ os')
      end
  end.

Fixpoint _init_taint_mem (m: mem) (n: nat) : tamem :=
  match m with
  | [] => []
  | h :: m' => ([inr n]) :: _init_taint_mem m' (S n)
  end.

Definition init_taint_mem (m: mem) : tamem :=
  _init_taint_mem m 0.

End TaintTracking.

Fixpoint split_sum_list {A B : Type} (l : list (A + B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | inl a :: xs => let (la, lb) := split_sum_list xs in (a :: la, lb)
  | inr b :: xs => let (la, lb) := split_sum_list xs in (la, b :: lb)
  end.

Definition taint_tracking (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := TaintTracking.init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (TaintTracking.steps_taint_track f p ist []) with
  | TaintTracking.ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.

Definition taint_tracking_detailed (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := TaintTracking.init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (TaintTracking.steps_taint_track f p ist []) with
  | TaintTracking.ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.

(** Some generators *)

Definition gen_prog_wt3 (bsz pl: nat) : G (rctx * tmem * list nat * prog) :=
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

Definition ipc : cptr := (0 , 0).
Definition istk : list cptr := [].
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
  wt_valb dv dt && forallb (fun '(x, t) => wt_valb (apply rs x) t) tm.

Fixpoint _gen_pub_mem_equiv_same_ty (P : list label) (m: list val) : G (list val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
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

(*! Section Sanity-Check *)

(* check 1: generated program is ub-free. *)

Definition ub_free (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := TaintTracking.init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (TaintTracking.steps_taint_track f p ist []) with
  | TaintTracking.ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | TaintTracking.EOutOfFuel (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.

(* check 2: no observation -> no leaked *)

Definition gen_inst_no_obs (pl: nat) (pst: list nat) : G inst :=
  let jlb := (list_minus (seq 0 (pl - 1)) (proc_hd pst)) in
  if seq.nilp jlb
  then ret <{ skip }>
  else freq [
           (1, ret ISkip);
           (1, l <- elems_ 0 jlb;; ret (IJump l))
         ].

Sample (gen_inst_no_obs 8 [3;3;1;1]).

Definition gen_blk_no_obs (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_no_obs pl pst).

Fixpoint _gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, bsz);;
      blk <- gen_blk_no_obs n pl pst;;
      rest <- _gen_proc_no_obs fsz' bsz pl pst;;
      ret ((blk, false) :: rest)
  end.

Definition gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, bsz);;
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

Sample gen_no_obs_prog.

QuickChick (
  forAll gen_no_obs_prog (fun p =>
  forAll arbitrary (fun rs =>
  forAll arbitrary (fun m =>
    let icfg := (ipc, rs, m, istk) in
    match taint_tracking 100 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker true
    end
  )))).

(* check 3: implicit flow *)

Example implicit_flow_test p rs icfg
  (P: p = [([ IBranch (AId "x") 1; IJump 1 ], true); ([ IAsgn "y"%string (ANum 1); IRet], false)])
  (RS: rs = (N 0, [("x"%string, N 10); ("y"%string, N 0)]))
  (ICFG: icfg = (ipc, rs, [], [])):
  match taint_tracking 10 p icfg with
  | Some (obs, leaked_vars, _) =>
      existsb (String.eqb "x") leaked_vars
  | None => false
  end = true.
Proof.
  remember (taint_tracking 10 p icfg).
  subst p rs icfg. simpl in Heqo.
  subst. simpl. reflexivity.
Qed.

(* check 4: unused variables never leaked *)

Definition gen_prog_and_unused_var : G (prog * string) :=
  '(c, tm, pst, p) <- gen_prog_wt3 3 5;;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (p, x).

QuickChick (
  forAll gen_prog_and_unused_var (fun '(p, unused_var) =>
  forAll arbitrary (fun rs =>
  forAll arbitrary (fun m =>
    let icfg := (ipc, rs, m, istk) in
    match taint_tracking 100 p icfg with
    | Some (_, leaked_vars, _) =>
        checker (negb (existsb (String.eqb unused_var) leaked_vars))
    | None =>
        checker true
    end
  )))).

(* check 5: gen_pub_equiv_same_ty works *)

Definition gen_pub_equiv_same_ty (P : total_map label) (s: total_map val) : G (total_map val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 end in
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map val)) (c : string * val) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if apply P k then ret v else f v);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv_same_ty P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

(* check 6: generated register set is well-typed. *)

QuickChick (
  forAll (gen_prog_wt3 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_reg c pst) (fun rs => rs_wtb rs c))).

(* check 5: gen_pub_mem_equiv_same_ty works *)

QuickChick (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

(* check 7: generated memory is well-typed. *)

QuickChick (
  forAll (gen_prog_wt3 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst) (fun m => m_wtb m tm))).

(* check 8: non-interference *)

(* QuickChick ( *)
(*   forAll (gen_prog_wt3 3 8) (fun '(c, tm, pst, p) => *)
(*   forAll (gen_wt_reg c pst) (fun rs => *)
(*   forAll (gen_wt_mem tm pst) (fun m => *)
(*   let icfg := (ipc, rs, m, istk) in *)
(*   let r1 := taint_tracking 100 p icfg in *)
(*   match r1 with *)
(*   | Some (os1', tvars, tms) => *)
(*       let P := (false, map (fun x => (x,true)) tvars) in *)
(*       let PM := tms_to_pm (Datatypes.length m) tms in *)
(*       forAll (gen_pub_equiv_same_ty P rs) (fun rs' => *)
(*       forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' => *)
(*       let icfg' := (ipc, rs', m', istk) in *)
(*       let r2 := taint_tracking 100 p icfg' in *)
(*       match r2 with *)
(*       | Some (os2', _, _) => checker (obs_eqb os1' os2') *)
(*       | None => checker false (* fail *) *)
(*       end)) *)
(*    | None => checker false (* discard *) *)
(*   end)))). *)

QuickChick (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_reg c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let r1 := taint_tracking 100 p icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let icfg' := (ipc, rs', m', istk) in
      let r2 := taint_tracking 100 p icfg' in
      match r2 with
      | Some (os2', _, _) => checker (obs_eqb os1' os2')
      | None => checker false (* fail *)
      end))
   | None => checker tt (* discard *)
  end)))).

(* +++ Passed 10000 tests (6354 discards) *)

(* direction generators *)
Definition gen_dbr : G direction :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G direction :=
  l <- (elems_ 0 (proc_hd pst));; ret (DCall (l, 0)).

(* dirs generator *)

Definition gen_spec_step (p:prog) (sc:spec_cfg) (pst: list nat) : G (option (spec_cfg * dirs * obs)) :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with
  | Some i =>
      let build_msg (reason: string) :=
        ("gen_spec_step FAILED. Reason: " ++ reason ++
        ". PC=" ++ show pc ++
        ", Inst=" ++ show i ++
        ", ct=" ++ show ct ++
        ", ms=" ++ show ms)%string
      in
      match i with
      | <{{branch e to l}}> =>
          d <- gen_dbr;;
          ret (match spec_step p sc [d] with
               | Some (sc', dir', os') => Some (sc', [d], os')
               | None => trace (build_msg "spec_step failed for BRANCH"%string) None
               end)
      | <{{call e}}> =>
          d <- gen_dcall pst;;
          ret (match spec_step p sc [d] with
               | Some (sc', dir', os') => Some (sc', [d], os')
               | None => trace (build_msg "spec_step failed for CALL"%string) None
               end)
      | _ =>
          ret (match spec_step p sc [] with
               | Some (sc', dir', os') => Some (sc', [], os')
               | None => trace (build_msg "spec_step failed for OTHER inst"%string) None
               end)
      end
  | None =>
      trace "PC fail" ret None
  end.

(* Definition gen_spec_step (p:prog) (sc:spec_cfg) (pst: list nat) : G (option (spec_cfg * dirs * obs)) := *)
(*   let '(c, ct, ms) := sc in *)
(*   let '(pc, r, m, sk) := c in *)
(*   match p[[pc]] with *)
(*   | Some i => *)
(*       let build_msg (reason: string) := *)
(*         ("gen_spec_step FAILED. Reason: " ++ reason ++ *)
(*          ". PC=" ++ (@show cptr _ pc) ++ *)
(*          ", Inst=" ++ (@show inst _ i) ++ *)
(*          ", ct=" ++ (@show bool _ ct) ++ *)
(*          ", ms=" ++ (@show bool _ ms))%string *)
(*       in *)
(*       match i with *)
(*       | <{{branch e to l}}> => *)
(*           d <- gen_dbr;; *)
(*           ret (match spec_step p sc [d] with *)
(*                | Some (sc', dir', os') => Some (sc', [d], os') *)
(*                | _ => (ret None) *)
(*                end) *)
(*       | <{{call e}}> => *)
(*           d <- gen_dcall pst;; *)
(*           ret (match spec_step p sc [d] with *)
(*                | Some (sc', dir', os') => Some (sc', [d], os') *)
(*                | _ => (ret None) *)
(*                end) *)
(*       | _ => *)
(*           ret (match spec_step p sc [] with *)
(*                | Some (sc', dir', os') => Some (sc', [], os') *)
(*                | _ => (ret None) *)
(*                end) *)
(*       end *)
(*   | None => ret None *)
(*   end. *)

Fixpoint gen_spec_steps_sized (f : nat) (p:prog) (sc:spec_cfg) (pst: list nat) : G (option (spec_cfg * dirs * obs)) :=
  match f with
  | 0 => ret (Some (sc, [], []))
  | S f' =>
      let '(c, _, _) := sc in
      let '(pc, _, _, _) := c in
      if (TaintTracking.final_cfg p pc)
      then ret (Some (sc, [], []))
      else ost <- gen_spec_step p sc pst;;
           match ost with
           | Some (sc', ds', os') => ost' <- gen_spec_steps_sized f' p sc' pst;;
                                    match ost' with
                                    | Some (sc'', ds'', os'') => ret (Some (sc'', ds' ++ ds'', os' ++ os''))
                                    | _ => trace ("Recursive call returned None" ++ show p) (ret None)
                                    end
           | _ => trace ("gen_spec_step returned None"  ++ show p) (ret None)
           end
  end.

(* Fixpoint gen_spec_steps_sized (f : nat) (p:prog) (sc:spec_cfg) (pst: list nat) : G (option (spec_cfg * dirs * obs)) := *)
(*   match f with *)
(*   | 0 => ret (Some (sc, [], [])) *)
(*   | S f' => ost <- gen_spec_step p sc pst;; *)
(*            match ost with *)
(*            | Some (sc', ds', os') => ost' <- gen_spec_steps_sized f' p sc' pst;; *)
(*                                     match ost' with *)
(*                                     | Some (sc'', ds'', os'') => ret (Some (sc'', ds' ++ ds'', os' ++ os'')) *)
(*                                     | _ => ret None *)
(*                                     end *)
(*            | _ => ret None *)
(*            end *)
(*   end. *)

(* Definition gen_dir (p: prog) (c: cfg) (pst: list nat) : G (option dirs) := *)
(*   let sc := (c, false, false) in *)
(*   res <- gen_spec_steps_sized 1557 p sc pst;; *)
(*   ret (match res with *)
(*        | Some (_, ds, _) => Some ds *)
(*        | _ => None *)
(*        end). *)

Derive Show for direction.
Derive Show for observation.

(* YH: keep failing... *)
Definition gen_the_dirs_only : G (option dirs) :=
  '(c, tm, pst, p) <- gen_prog_wt3 3 5;;
  rs <- gen_wt_reg c pst;;
  m <- gen_wt_mem tm pst;;
  let icfg := (ipc, rs, m, istk) in
  let r1 := taint_tracking 100 p icfg in
  match r1 with
  | Some _ =>
      let harden := uslh_prog p in
      let iscfg := (icfg, true, false) in
      let h_pst := pst_calc harden in
      ods <- gen_spec_steps_sized 100 harden iscfg h_pst;;
      ret (match ods with
           | Some (_, ds, _) => Some ds
           | None => None
           end)
  | _ => trace "seq fail" ret None
  end.

Sample (gen_the_dirs_only).

Definition gen_dir_test_aux : G (prog * spec_cfg * list nat) :=
  '(c, tm, pst, p) <- gen_prog_wt3 3 5;;
  rs <- gen_wt_reg c pst;;
  m <- gen_wt_mem tm pst;;
  let icfg := (ipc, rs, m, istk) in
  let iscfg := (icfg, true, false) in
  ret (p, iscfg, pst).

Definition gen_dir_test : G (prog * option (spec_cfg * dirs * obs)) :=
  '(p, iscfg, pst) <- gen_dir_test_aux;;
  let harden := uslh_prog p in
  let h_pst := pst_calc harden in
  res <- gen_spec_steps_sized 20 harden iscfg h_pst;;
  ret (p, res).

Sample (gen_dir_test).

(* QuickChick ( *)
(*   forAll (gen_prog_wt3 3 5) (fun '(c, tm, pst, p) => *)
(*   forAll (gen_wt_reg c pst) (fun rs => *)
(*   forAll (gen_wt_mem tm pst) (fun m => *)
(*   let icfg := (ipc, rs, m, istk) in *)
(*   let r1 := taint_tracking 100 p icfg in *)
(*   match r1 with *)
(*   | Some (os1', tvars, tms) => *)
(*       let P := (false, map (fun x => (x,true)) tvars) in *)
(*       let PM := tms_to_pm (Datatypes.length m) tms in *)
(*       forAll (gen_pub_equiv_same_ty P rs) (fun rs' => *)
(*       forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' => *)
(*       let icfg' := (ipc, rs', m', istk) in *)
(*       let harden := uslh_prog p in *)
(*       let iscfg := (icfg, true, false) in (* (cfg, ct, ms) *) *)
(*       let h_pst := pst_calc harden in *)
(*       forAll (gen_spec_steps_sized 100 harden iscfg h_pst) (fun ods => *)
(*       match ods with *)
(*       | Some (_, ds, os1) => checker ds *)
(*       | None => checker tt *)
(*       end) *)
(*         ) *)
(*         ) *)
(*    | None => checker tt (* discard *) *)
(*   end)))). *)


QuickChick (
  forAll (gen_prog_wt3 3 5) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_reg c pst) (fun rs =>
  forAll (gen_wt_mem tm pst) (fun m =>
  let icfg := (ipc, rs, m, istk) in
  let r1 := taint_tracking 100 p icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let icfg' := (ipc, rs', m', istk) in
      let harden := uslh_prog p in
      let iscfg := (icfg, true, false) in (* (cfg, ct, ms) *)
      let h_pst := pst_calc harden in
      forAll (gen_spec_steps_sized 100 harden iscfg h_pst) (fun ods =>
      match ods with
      | Some (_, ds, os1) =>
          let iscfg' := (icfg', true, false) in
          (* let res1 := spec_steps 100 harden iscfg ds in *)
          let res2 := spec_steps 100 harden iscfg' ds in
          match res2 with
          | Some (_, _, os2) => checker (obs_eqb os1 os2)
          | _ => checker tt
          end
      | None => checker tt
      end)
        )
        )
   | None => checker tt (* discard *)
  end)))).


(* Definition gen_store_in_ctx (gen_store : pub_vars -> pub_arrs -> reg -> list nat -> G inst) *)
(*     (pc:label) (P:pub_vars) (PA:pub_arrs) (rs: reg) (pst: list nat) : G inst := *)
(*   if pc then gen_store P PA rs pst *)
(*   else *)
(*     i <- get_addr PA secret;; (* secret location *) *)
(*     match i with *)
(*     | Some i => *)
(*         b <- arbitrary;; *)
(*         e <- gen_exp_for_offset i P rs b;; *)
(*         e' <- arbitrarySized 1;; *)
(*         ret (IStore e e') *)
(*     | None => ret <{ skip }> *)
(*     end. *)

(* Definition gen_pub_branch (P: pub_vars) (pl: nat) (pst: list nat) (rs: reg) : G inst := *)
(*   let vars := map_dom (snd rs) in *)
(*   e <- gen_pub_exp_no_ptr 1 P rs;; *)
(*   l <- elems_ 0 (nat_list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *) *)
(*   ret <{ branch e to l }>. *)

(* (* ex_vars = <{{ i[ ("X0"%string); ("X1"%string); ("X2"%string); ("X3"%string); ("X4"%string)] }}> *) *)
(* Definition ex_pub_vars : total_map label := (true,[("X0",true); ("X1",true); ("X2",true); *)
(*                                                    ("X3",false); ("X4",false)])%string. *)

(* Definition ex_pub_vars' : total_map label := (true,[("X0",false); ("X1",false); ("X2",false); *)
(*                                                    ("X3",true); ("X4",false)])%string. *)

(* Definition ex_rs : total_map val := (N 0,[("X0",N 42); ("X1",N 33); ("X2",FP 0); *)
(*                                           ("X3",FP 0); ("X4",FP 3)])%string. *)

(* Sample (gen_pub_branch ex_pub_vars 8 [3; 3; 1; 1] ex_rs). *)

(* Definition gen_branch_in_ctx (gen_branch: pub_vars -> nat -> list nat -> reg -> G inst) *)
(*   (pc:label) (P:pub_vars) (pl: nat) (pst: list nat) (rs: reg) : G inst := *)
(*   if pc then gen_branch P pl pst rs *)
(*   else *)
(*     e <- gen_exp_leaf_no_ptr rs;; *)
(*     l <- elems_ 0 (nat_list_minus (seq 0 (pl - 1)) (proc_hd pst));; *)
(*     ret <{ branch e to l }>. *)

(* Sample (gen_branch_in_ctx gen_pub_branch secret ex_pub_vars' 8 [3; 3; 1; 1] ex_rs). *)

(* Definition gen_pub_call (P:pub_vars) (pst: list nat) (rs: reg) : G inst := *)
(*   l <- gen_pub_exp_ptr 1 P pst rs;; *)
(*   ret <{ call l }>. *)

(* Sample (gen_pub_call ex_pub_vars [3; 3; 1; 1] ex_rs). *)

(* Definition gen_call_in_ctx (gen_call: pub_vars -> list nat -> reg -> G inst) *)
(*   (pc: label) (P:pub_vars) (pst: list nat) (rs: reg) : G inst := *)
(*   if pc then gen_call P pst rs *)
(*   else *)
(*     l <- gen_exp_ptr_in_ctx false 1 P pst rs;; *)
(*     ret <{ call l }>. *)

(* YH: Unlike non-interference, the relative security property is formally defined for all input pairs. It does not require input pairs to be public-equivalent.

 However, for the test to be meaningful, the premise of the property must hold.
 This means we must select input pairs for which the original program produces
 identical observations under sequential execution.

  => the taint analysis of TestingFlexSLH will be useful.
 *)

(* From SECF Require Import TestingSpecCT. *)

(* Notation label := TestingSpecCT.label. *)
(* Notation apply := ListMaps.apply. *)
(* Notation join := TestingSpecCT.join. *)




(** Better wf program generator - constant time *)
(* 1. public/secret
   2. ptr/not ptr
   3. wf          *)

Definition gen_pub_exp_leaf (P : pub_vars) (pst :list nat) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
         liftM FPtr (elems_ 0 (proc_hd pst)) ;;;
         (let pubs := (filter (apply P) (map_dom (snd P))) in
         if seq.nilp pubs then []
         else [liftM AId (elems_ ("X0"%string) pubs)])).

Sample (P <- arbitrary ;;
       exp <- gen_pub_exp_leaf P [3; 3; 1; 1];;
       ret (P, exp)).

Definition gen_exp_leaf_in_ctx (pc: label) (P : pub_vars) (pst :list nat) : G exp :=
  if pc then gen_pub_exp_leaf P pst
  else
    oneOf (liftM ANum arbitrary ;;;
             liftM FPtr (elems_ 0 (proc_hd pst)) ;;;
             (let vars := (map_dom (snd P)) in
              if seq.nilp vars then []
              else [liftM AId (elems_ ("X0"%string) vars)])).

(* move to somewhere *)
Definition string_eq_dec := Map.E.eq_dec.

Definition list_inter {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) (l1 l2: list A) : list A :=
  filter (fun x => if (in_dec eq_dec x l2) then true else false) l1.

Definition gen_pub_exp_leaf_ptr (P : pub_vars) (pst :list nat) (rs : reg) : G exp :=
  oneOf (liftM FPtr (elems_ 0 (proc_hd pst)) ;;;
           (let ptrs := filter (fun x => negb (is_not_ptr rs x)) (map_dom (snd rs)) in
            let pubs := (filter (apply P) (map_dom (snd P))) in
            let s := list_inter string_eq_dec ptrs pubs in
            if seq.nilp s then [] else
              [liftM AId (elems_ "X0"%string s)] ) ).

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_pub_exp_leaf_ptr P [3; 3; 1; 1] rs;;
        ret (P, rs, exp)).

Definition gen_exp_leaf_ptr_in_ctx (pc: label) (P : pub_vars) (pst :list nat) (rs : reg) : G exp :=
  if pc then gen_pub_exp_leaf_ptr P pst rs
  else
    let ptrs := filter (fun x => negb (is_not_ptr rs x)) (map_dom (snd rs)) in
    oneOf (liftM FPtr (elems_ 0 (proc_hd pst)) ;;;
             if seq.nilp ptrs then [] else [liftM AId (elems_ "X0"%string ptrs)] ).

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_exp_leaf_ptr_in_ctx false P [3; 3; 1; 1] rs;;
        ret (P, rs, exp)).

Definition gen_pub_exp_leaf_no_ptr (P : pub_vars) (rs : reg) : G exp :=
  oneOf (liftM ANum arbitrary ;;;
         (let not_ptrs := filter (is_not_ptr rs) (map_dom (snd rs)) in
          let pubs := (filter (apply P) (map_dom (snd P))) in
          let s := list_inter string_eq_dec not_ptrs pubs in
          if seq.nilp s then [] else
            [liftM AId (elems_ "X0"%string s)] ) ).

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_pub_exp_leaf_no_ptr P rs;;
        ret (P, rs, exp)).

Definition gen_exp_leaf_no_ptr_in_ctx (pc: label) (P : pub_vars) (rs : reg) : G exp :=
  if pc then gen_pub_exp_leaf_no_ptr P rs
  else
    oneOf (liftM ANum arbitrary ;;;
           let not_ptrs := filter (is_not_ptr rs) (map_dom (snd rs)) in
           if seq.nilp not_ptrs then [] else [liftM AId (elems_ "X0"%string not_ptrs)] ).

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_exp_leaf_no_ptr_in_ctx false P rs;;
        ret (P, rs, exp)).

Fixpoint gen_pub_exp_no_ptr (sz : nat) (P: pub_vars) (rs: reg) : G exp :=
  match sz with
  | O => gen_pub_exp_leaf_no_ptr P rs
  | S sz' =>
      freq [ (2, gen_pub_exp_leaf_no_ptr P rs);
             (sz, liftM3 ABin arbitrary (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_no_ptr sz' P rs));
             (sz, liftM3 ACTIf (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_no_ptr sz' P rs))
          ]
  end.

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_pub_exp_no_ptr 2 P rs;;
        ret (P, rs, exp)).

Fixpoint gen_exp_no_ptr_in_ctx (pc: label) (sz : nat) (P: pub_vars) (rs: reg) : G exp :=
  if pc then gen_pub_exp_no_ptr sz P rs
  else
    match sz with
    | O => gen_exp_leaf_no_ptr_in_ctx pc P rs
    | S sz' =>
        freq [ (2, gen_exp_leaf_no_ptr_in_ctx pc P rs);
               (sz, liftM3 ABin arbitrary (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_no_ptr_in_ctx pc sz' P rs));
               (sz, liftM3 ACTIf (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_no_ptr_in_ctx pc sz' P rs))
          ]
  end.

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_exp_no_ptr_in_ctx false 2 P rs;;
        ret (P, rs, exp)).

Fixpoint gen_pub_exp_ptr (sz : nat) (P: pub_vars) (pst: list nat) (rs: reg) : G exp :=
  match sz with
  | O => gen_pub_exp_leaf_ptr P pst rs
  | S sz' =>
      freq [ (2, gen_pub_exp_leaf_ptr P pst rs);
             (sz, liftM3 ACTIf (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_ptr sz' P pst rs) (gen_pub_exp_ptr sz' P pst rs))
          ]
  end.

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_pub_exp_ptr 2 P [3; 3; 1; 1] rs;;
        ret (P, rs, exp)).

Fixpoint gen_exp_ptr_in_ctx (pc: label) (sz : nat) (P: pub_vars) (pst: list nat) (rs: reg) : G exp :=
  if pc then gen_pub_exp_ptr sz P pst rs
  else
    match sz with
    | O => gen_exp_leaf_ptr_in_ctx false P pst rs
    | S sz' =>
        freq [ (2, gen_exp_leaf_ptr_in_ctx false P pst rs);
               (sz, liftM3 ACTIf (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_ptr_in_ctx pc sz' P pst rs) (gen_exp_ptr_in_ctx pc sz' P pst rs))
          ]
    end.

Sample (P <- arbitrary ;;
        rs <- arbitrary ;;
        exp <- gen_exp_ptr_in_ctx false 2 P [3; 3; 1; 1] rs;;
        ret (P, rs, exp)).


(* Better, but we still get discards. These cases are when the equality is generated between pointer *)
(*   and non-pointer. The following generator accounts for that: *)

(* Definition eitherOf {A} (a : G A) (b : G A) : G A := freq [(1, a); (1, b)]. *)

Fixpoint gen_pub_exp (sz : nat) (P: pub_vars) (rs : reg) (pst: list nat) : G exp :=
  match sz with
  | O => gen_pub_exp_leaf P pst
  | S sz' =>
          freq [
             (2, gen_pub_exp_leaf P pst);
             (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_no_ptr sz' P rs))
                    (liftM2 (ABin BinEq) (liftM FPtr arbitrary) (liftM FPtr arbitrary))
                | _ => liftM2 (ABin binop) (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp_no_ptr sz' P rs)
              end);
             (sz, liftM3 ACTIf (gen_pub_exp_no_ptr sz' P rs) (gen_pub_exp sz' P rs pst) (gen_pub_exp sz' P rs pst))
          ]
  end.

Fixpoint gen_exp_in_ctx (pc: label) (sz : nat) (P: pub_vars) (rs : reg) (pst: list nat) : G exp :=
  if pc then gen_pub_exp sz P rs pst
  else
    match sz with
    | O => gen_exp_leaf_in_ctx false P pst
    | S sz' =>
        freq [
            (2, gen_exp_leaf_in_ctx pc P pst);
            (sz, binop <- arbitrary;;
                 match binop with
                 | BinEq => eitherOf
                             (liftM2 (ABin BinEq) (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_no_ptr_in_ctx pc sz' P rs))
                             (liftM2 (ABin BinEq) (liftM FPtr arbitrary) (liftM FPtr arbitrary))
                 | _ => liftM2 (ABin binop) (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_no_ptr_in_ctx pc sz' P rs)
                 end);
            (sz, liftM3 ACTIf (gen_exp_no_ptr_in_ctx pc sz' P rs) (gen_exp_in_ctx pc sz' P rs pst) (gen_exp_in_ctx pc sz' P rs pst))
          ]
  end.

Definition gen_secure_asgn (P:pub_vars) (rs: reg) (pst: list nat) : G inst :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  e <- (if apply P x then gen_pub_exp 1 P rs pst else gen_pub_exp 1 P rs pst);;
  ret <{ x := e }>.

Definition gen_name (P:pub_vars) (label:bool) : G (option string) :=
  let names := filter (fun x => Bool.eqb label (apply P x))
                      (map_dom (snd P)) in
  match names with
  | x0 :: _ => liftM Some (elems_ x0 names)
  | [] => ret None
  end.

Definition get_addr (PA: pub_arrs) (label:bool) : G (option nat) :=
  let indices := seq 0 (Datatypes.length PA) in
  let idx_pa := combine indices PA in
  let filtered := filter (fun '(idx, b) => Bool.eqb label b) idx_pa in
  let indices' := map fst filtered in
  match indices' with
  | [] => ret None
  | hd::tl => liftM Some (elems_ hd indices')
  end.

Definition gen_asgn_in_ctx (gen_asgn : pub_vars -> reg -> list nat -> G inst)
    (pc:label) (P:pub_vars) (rs: reg) (pst: list nat) : G inst :=
  if pc then gen_asgn P rs pst
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
      e <- gen_exp_in_ctx false 1 P rs pst;;
      ret <{ x := e }>
    | None => ret <{ skip }>
    end.

Definition gen_exp_for_offset (n: nat) (P: pub_vars) (rs: reg) (label: bool) : G exp :=
  freq [(1, ret (ANum n));
        (1, let label_regs := filter (fun x => Bool.eqb label (apply P (fst x))) (snd rs) in
            let regs := filter (fun '(_, v) => match v with
                                            | N m => m <=? n
                                            | _ => false
                                            end) label_regs in
            match regs with
            | [] => ret (ANum n)
            | _ => '(name, vm) <- elems_ ("X0"%string, N 0) regs;;
                  match vm with
                  | N m => let ofs := n - m in
                          ret (ABin BinPlus (AId name) (ANum ofs))
                  | _ => ret (ANum n)
                  end
            end)
    ].

(* TODO: more complicate expression for address *)
Definition gen_secure_load (P:pub_vars) (PA:pub_arrs) (rs: reg) : G inst :=
  let vars := map_dom (snd P) in
  x <- elems_ "X0"%string vars;;
  if apply P x then
    i <- get_addr PA public;; (* public location *)
    match i with
    | Some i' =>
        i'' <- gen_exp_for_offset i' P rs true;;
        ret (ILoad x i'')
    | None => ret <{ skip }>
    end
  else
    (* x is secret *)
    b <- arbitrary;;
    i <- get_addr PA b;;
    match i with
    | Some i' =>
        i'' <- gen_exp_for_offset i' P rs b;;
        ret (ILoad x i'')
    | _ => ret <{ skip }>
    end.

Definition gen_load_in_ctx (gen_load : pub_vars -> pub_arrs -> reg -> G inst)
    (pc:label) (P:pub_vars) (PA:pub_arrs) (rs: reg) : G inst :=
  if pc then gen_load P PA rs
  else
    x <- gen_name P secret;; (* secret var *)
    match x with
    | Some x =>
        b <- arbitrary;;
        i <- get_addr PA b;;
        match i with
        | Some i' =>
            i'' <- gen_exp_for_offset i' P rs b;;
            ret (ILoad x i'')
        | _ => ret <{ skip }>
        end
    | None => ret <{ skip }>
    end.

Definition gen_secure_store (P:pub_vars) (PA:pub_arrs) (rs: reg) (pst: list nat) : G inst :=
  let indices := seq 0 (Datatypes.length PA) in
  i <- elems_ 0 indices;;
  if nth i PA true then
    (* PA is always larger than []. *)
    (* public location *)
    e <- gen_exp_for_offset i P rs true;;
    e' <- gen_pub_exp 1 P rs pst;;
    ret (IStore e e')
  else
    (* secret location *)
    b <- arbitrary;;
    e <- gen_exp_for_offset i P rs b;;
    e' <- arbitrarySized 1;;
    ret (IStore e e').

Definition gen_store_in_ctx (gen_store : pub_vars -> pub_arrs -> reg -> list nat -> G inst)
    (pc:label) (P:pub_vars) (PA:pub_arrs) (rs: reg) (pst: list nat) : G inst :=
  if pc then gen_store P PA rs pst
  else
    i <- get_addr PA secret;; (* secret location *)
    match i with
    | Some i =>
        b <- arbitrary;;
        e <- gen_exp_for_offset i P rs b;;
        e' <- arbitrarySized 1;;
        ret (IStore e e')
    | None => ret <{ skip }>
    end.

Definition gen_pub_branch (P: pub_vars) (pl: nat) (pst: list nat) (rs: reg) : G inst :=
  let vars := map_dom (snd rs) in
  e <- gen_pub_exp_no_ptr 1 P rs;;
  l <- elems_ 0 (list_minus (seq 0 (pl - 1)) (proc_hd pst));; (* 0 is unreachable *)
  ret <{ branch e to l }>.

(* ex_vars = <{{ i[ ("X0"%string); ("X1"%string); ("X2"%string); ("X3"%string); ("X4"%string)] }}> *)
Definition ex_pub_vars : total_map label := (true,[("X0",true); ("X1",true); ("X2",true);
                                                   ("X3",false); ("X4",false)])%string.

Definition ex_pub_vars' : total_map label := (true,[("X0",false); ("X1",false); ("X2",false);
                                                   ("X3",true); ("X4",false)])%string.

Definition ex_rs : total_map val := (N 0,[("X0",N 42); ("X1",N 33); ("X2",FP 0);
                                          ("X3",FP 0); ("X4",FP 3)])%string.

Sample (gen_pub_branch ex_pub_vars 8 [3; 3; 1; 1] ex_rs).

Definition gen_branch_in_ctx (gen_branch: pub_vars -> nat -> list nat -> reg -> G inst)
  (pc:label) (P:pub_vars) (pl: nat) (pst: list nat) (rs: reg) : G inst :=
  if pc then gen_branch P pl pst rs
  else
    e <- gen_exp_leaf_no_ptr rs;;
    l <- elems_ 0 (list_minus (seq 0 (pl - 1)) (proc_hd pst));;
    ret <{ branch e to l }>.

Sample (gen_branch_in_ctx gen_pub_branch secret ex_pub_vars' 8 [3; 3; 1; 1] ex_rs).

Definition gen_pub_call (P:pub_vars) (pst: list nat) (rs: reg) : G inst :=
  l <- gen_pub_exp_ptr 1 P pst rs;;
  ret <{ call l }>.

Sample (gen_pub_call ex_pub_vars [3; 3; 1; 1] ex_rs).

Definition gen_call_in_ctx (gen_call: pub_vars -> list nat -> reg -> G inst)
  (pc: label) (P:pub_vars) (pst: list nat) (rs: reg) : G inst :=
  if pc then gen_call P pst rs
  else
    l <- gen_exp_ptr_in_ctx false 1 P pst rs;;
    ret <{ call l }>.

Sample (gen_call_in_ctx gen_pub_call false ex_pub_vars' [3; 3; 1; 1] ex_rs).
  (* | IBranch : exp -> nat -> inst *)
  (* | IJump : nat -> inst *)
  (* | ICall : exp -> inst *)
  (* | IRet : inst. *)

Definition gen_inst2 (gen_asgn : label -> pub_vars -> reg -> G inst)
                     (gen_load : label -> pub_vars -> pub_arrs -> reg -> G inst)
                     (gen_store : label -> pub_vars -> pub_arrs -> reg -> G inst)
                     (gen_branch: label -> pub_vars -> nat -> list nat -> reg -> G inst)
                     (gen_jump: nat -> list nat -> G inst)
                     (gen_call: label -> pub_vars -> list nat -> reg -> G inst)
                     (P:pub_vars) (PA:pub_arrs) (rs: reg) (sz:nat) : G inst :=
  match sz with
  | O => freq [(1, ret ISkip);
               (4, thunkGen (fun _ => gen_asgn P rs));
               (4, thunkGen (fun _ => gen_load P PA rs));
               (4, thunkGen (fun _ => gen_store P PA rs))]
  | S sz' => freq [ (1, ret ISkip);
                   (1, ret IRet);
                   (sz, gen_asgn vars c);
                   (sz, gen_branch vars pl c);
                   (sz, gen_jump pl c);
                   (sz, gen_load vars pl c);
                   (sz, gen_store vars pl c);
                   (sz, gen_call c)]
  end.
