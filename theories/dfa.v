From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
From aruvi Require re.
From aruvi Require nfa.
Import state.StateNotations.

Record t {A: Type}: Type := mkDfa {
  state: state.tDfa;
  start: dfa⟦state⟧;
  final: {set dfa⟦state⟧};
  tf: dfa⟦state⟧ -> A -> dfa⟦state⟧
}.
Arguments t: clear implicits.

(* Definition of_nfa {A: Type} (n: nfa.t A): t A := {| *)
(*   state := state.pset (nfa.state n); *)
(*   start := (nfa.start n) A; *)
(*   final := [set X | X :&: nfa_fin A != set0]; *)
(*   tf X a := [set q | [exists (p | p \in X), nfa_trans p a q]] *) 
(* |}. *)

