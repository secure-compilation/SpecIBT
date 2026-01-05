From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".
Require Import Stdlib.Classes.EquivDec.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.

From SECF Require Import MiniCET MapsFunctor ListMaps.

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

Derive Shrink for binop.
Derive Shrink for exp.
Derive Shrink for inst.

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