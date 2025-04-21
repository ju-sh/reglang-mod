From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From reglangmod Require state.
From reglangmod Require re.
From reglangmod Require nfa.
Import state.StateNotations.

Record t {A: Type}: Type := mkDfa {
  state: state.tNfa;
  start: {sset nfa⟦state⟧};
  final: {sset nfa⟦state⟧};
  tf: {sset nfa⟦state⟧} -> A -> {sset nfa⟦state⟧}
}.
Arguments t: clear implicits.

(*
Definition of_nfa {A: Type} (n: nfa.t A): t A. refine {|
  state := nfa.state n;
  start := _; (* [set (nfa.start n)]; *)
  (* start := [set [set x] | x in nfa.start n]; (1* [set (nfa.start n)]; *1) *)
  final := _;
  tf src ch := _
|}.
- Check [set  
- Check [set: dfa⟦state.pset (nfa.state n)⟧].
  Check [set x | x in [set: dfa⟦state.pset (nfa.state n)⟧]].
  Check [set x | x in [set: dfa⟦state.pset (nfa.state n)⟧]].
  Check [set x | x in [set: bool]].
  Check [set x in [set: bool] | true].
  Check [set x in [set: dfa⟦state.pset (nfa.state n)⟧] | true].

  Check [set x in [set: _] | true].
  Check [set x in [set: {set {set nfa⟦nfa.state n⟧}}] | true].
  Search {set _} bool.
  Search (set_of _ -> set_of _ -> bool).
  Check [set x in [set: {set {set nfa⟦nfa.state n⟧}}] | x :&: _ = false].

  Check [set x in [set: dfa⟦state.pset (nfa.state n)⟧] | x :&: _].
(*
[set p | p ∩ n.final != ∅
     & p in pset] *)

Check [set true; false].
Check [set true] == set0.
(* [set true; false] : {set Datatypes_bool__canonical__fintype_Finite} *)
- Check [set [set x] | x in nfa.final n]. 
Check [set: bool].
Check [set: bool].
(* [set: bool] : {set Datatypes_bool__canonical__fintype_Finite} *)


- Check nfa.state n.
  exact: [set (nfa.start n)].
  Check {set nfa⟦nfa.state n⟧}.
  Check [set x | x \in {set nfa⟦nfa.state n⟧}].
  Check [set x | set0 \notin (x :&: (nfa.start n)) & x \in {set nfa⟦nfa.state n⟧}].
  Check [set x | set0 \notin (x :&: (nfa.start n)) & x \in {set nfa⟦nfa.state n⟧}].
  Check [set x | x \in {set nfa⟦state⟧}].
  + exact: 
  Check [set X | X :&: nfa.final n != set0].
 *)
