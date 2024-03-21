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

Fixpoint tDfaDenote (s: tDfa): Type :=
  match s with
	| DOne => unit
	| DPlus a b => dfa⟦a⟧ + dfa⟦b⟧
	| DMult a b => dfa⟦a⟧ * dfa⟦b⟧
	end
where "'dfa⟦' s '⟧'" := (tDfaDenote s).

Fixpoint pset (s: tNfa): tDfa :=
  match s with
  | NZero => DOne
  | NOne => DPlus DOne DOne
  | NPlus a b => DMult (pset a) (pset b)
  end.

(* Fixpoint eqbNfa {s: tNfa}: nfa⟦s⟧ -> nfa⟦s⟧ -> bool := fun a b => a == b. *)

(* Fixpoint eqbNfa {s: tNfa}: nfa⟦s⟧ -> nfa⟦s⟧ -> bool. refine( *)
(*   match s with *)
(*   | NZero => fun _ _ => true *)
(*   | NOne => fun a b => a == b *)
(*   | NPlus s1 s2 => _ *)
(*   end). *)

Module StateNotations.
  Declare Scope state_scope.
  Delimit Scope state_scope with state.

  Notation "'dfa⟦' s '⟧'" := (tDfaDenote s) (at level 20).
  Notation "'nfa⟦' s '⟧'" := (tNfaDenote s) (at level 20).
End StateNotations.
