From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Reserved Notation "'dfa⟦' s '⟧'" (at level 20).
Reserved Notation "'nfa⟦' s '⟧'" (at level 20).


Inductive tNfa: Type :=
| NZero: tNfa
| NOne: tNfa
| NPlus: tNfa -> tNfa -> tNfa.

Inductive tDfa: Type :=
| DOne: tDfa
| DPlus: tDfa -> tDfa -> tDfa
| DMult: tDfa -> tDfa -> tDfa.

Fixpoint tNfaDenote (s: tNfa): finType :=
  (match s with
  | NZero => void
  | NOne => unit
  | NPlus a b => nfa⟦a⟧ + nfa⟦b⟧
  end)%type
where "'nfa⟦' s '⟧'" := (tNfaDenote s).

Fixpoint tDfaDenote (s: tDfa): finType :=
  (match s with
  | DOne => unit
  | DPlus a b => dfa⟦a⟧ + dfa⟦b⟧
  | DMult a b => dfa⟦a⟧ * dfa⟦b⟧
  end)%type
where "'dfa⟦' s '⟧'" := (tDfaDenote s).

Fixpoint pset (s: tNfa): tDfa :=
  match s with
  | NZero => DOne
  | NOne => DPlus DOne DOne
  | NPlus a b => DMult (pset a) (pset b)
  end.

(* Fixpoint tNfaEnum (s: tDfa): seq (dfa⟦s⟧). *)
(*   refine ( *)
(*   match s with *)
(*   | DOne => [:: tt] *)
(*   | DPlus a b => _ *)
(*   | DMult a b => _ *)
(*   end) => /=. *)


(* Fixpoint union {n: tNfa}: {set nfa⟦n⟧} -> {set dfa⟦pset n⟧}. *)
(* refine ( *)
(*   match n with *)
(*   | NZero => fun s => set0 *)
(*   | NOne => fun s => _ *)
(*   | NPlus a b => fun s => _ *)
(*   end) => /=; rewrite /= in s. *)
(*  - shelve. *)
(*  - *) 

(* Check [set x | x in s]. *)
(* Check [set (fun x => x) x | x in s]. *)
(*  - refine ([set _ | x in s]). *)
(*    Search (set_of _ -> bool). *)
(*    Search set0 bool. *)
(*    Compute set0 \in set0. *)

(*    refine ( *)
(*      match x with *)
(*      | inl l => inl x' *)
(*      | inr r => inr x' *)


(* ref [set *)
(*   (match x with *)
(*   | inl x' => inl x' *)
(*   | inr x' => inr x' *)
(*   end) *)
(*    | x in s]. *)

(* Check [set *)
(*   (match x with *)
(*   | inl x' => x *)
(*   | inr x' => x *)
(*   end) *)
(*    | x in s]. *)
(* Search ({set _} -> seq _). *)
(* Search (set_of _ -> seq _). *)
(* Search (set_of _) seq. *)
(* Search (set_of _) bool. *)
(* Check [set *) 

Module StateNotations.
  Declare Scope state_scope.
  Delimit Scope state_scope with state.

  Notation "'dfa⟦' s '⟧'" := (tDfaDenote s) (at level 20).
  Notation "'nfa⟦' s '⟧'" := (tNfaDenote s) (at level 20).

  Notation "{ 'sset' T }" := {set {set T}} (only parsing): type_scope.
End StateNotations.
