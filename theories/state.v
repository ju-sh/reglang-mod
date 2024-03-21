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
  | NPlus a b => (tNfaDenote a) + (tNfaDenote b)
  end)%type.
 (* 𝟘 𝟙 𝟎 *)

Fixpoint tDfaDenote (s: tDfa): Type :=
  match s with
	| DOne => unit
	| DPlus a b => (tDfaDenote a) + (tDfaDenote b)
	| DMult a b => (tDfaDenote a) * (tDfaDenote b)
	end.

Fixpoint pset (s: tNfa): tDfa :=
  match s with
  | NZero => DOne
  | NOne => DPlus DOne DOne
  | NPlus a b => DMult (pset a) (pset b)
  end.

Module StateNotations.
  Declare Scope state_scope.
  Delimit Scope state_scope with state.

  Notation "'dfa⟦' s '⟧'" := (tDfaDenote s) (at level 20).
  Notation "'nfa⟦' s '⟧'" := (tNfaDenote s) (at level 20).
End StateNotations.
