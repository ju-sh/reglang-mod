From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
Import state.StateNotations.

Record t {A: Type}: Type := mkNfa {
  state: state.tNfa;
  start: {set nfa⟦state⟧};
  final: {set nfa⟦state⟧} -> bool;
  tf: nfa⟦state⟧ -> A -> {set nfa⟦state⟧}
}.
Arguments t: clear implicits.

Section FAs.
  Context {A: finType}.

  (* Like 𝟘 *)
  Definition nul: t A. refine {|
    state := state.NZero;
    start := set0;
    final := fun _ => false;
    tf src ch := set0
  |}.
  Defined.

  (* Like 𝟙 *)
  Definition eps: t A. refine {|
    state := state.NOne;
    start := [set tt];
    final := fun st => st :&: [set tt];
    tf src ch := set0
  |}.
  Defined.

  Definition char (f: A -> bool): t A. refine {|
    state := state.NPlus state.NOne state.NOne;
    start := [set (inl tt)];
    final := fun st => st \in [set (inr tt)];
    tf src ch :=
       if src \in [set (inl tt)] then
         if f ch then [set (inr tt)]
         else set0
       else set0
  |}.
  Defined.

  Definition cat (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := inl @: start n1;
    final := fun st =>
      match st with
      | inl s => false
      | inr s => (final n2) s
      end;
    tf src ch :=
      match src with
      | inl s =>
          let tmp := (tf n1) s ch in
          if tmp :&: (final n1) then _ else _
      | inr s =>
          let tmp := (tf n2) s ch in
          inr @: tmp
      end;
  |}.
  Check (final n1).

  Definition cat (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := inl @: start n1;
    final := fun st =>
      match st with
      | inl s => false
      | inr s => (final n2) s
      end;
    tf src ch :=
      match src with
      | inl s =>
          let tmp := (tf n1) s ch in
          if (final n1) tmp then
            (inl @: tmp) :|: (inr @: (start n2))
          else
            (inl @: tmp)
      | inr s =>
          let tmp := (tf n2) s ch in
          inr @: tmp
      end;
  |}.
  - rewrite /= in st.
    refine (
        match st with

  Abort.

  Definition alt (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := (inl @: start n1) :|: (inr @: start n2);
    final := fun st => _;
    tf src ch := _;
  |}.
  Abort.

  Definition star (n: t A): t A. refine {|
    state := state n;
    start := _;
    final := fun st => _;
    tf src ch := _;
  |}.
  Abort.
End FAs.
