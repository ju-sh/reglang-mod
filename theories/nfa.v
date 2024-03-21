From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
Import state.StateNotations.

Record t {A: Type}: Type := mkNfa {
  state: state.tNfa;
  start: {set nfa⟦state⟧};
  final: {set nfa⟦state⟧};
  tf: nfa⟦state⟧ -> A -> {set nfa⟦state⟧}
}.
Arguments t: clear implicits.

Section FAs.
  Context {A: finType}.

  (* Like 𝟘 *)
  Definition nul: t A. refine {|
    state := state.NZero;
    start := set0;
    final := set0;
    tf src ch := set0
  |}.
  Defined.

  (* Like 𝟙 *)
  Definition eps: t A. refine {|
    state := state.NOne;
    start := [set tt];
    final := [set tt];
    tf src ch := set0
  |}.
  Defined.

  Definition char (f: A -> bool): t A. refine {|
    state := state.NPlus state.NOne state.NOne;
    start := [set (inl tt)];
    final := [set (inr tt)];
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
    final := inr @: final n2;
    tf src ch :=
      match src with
      | inl s =>
          let tmp := (tf n1) s ch in
          if (final n1) :&: tmp == set0 then
            inl @: tmp
          else (inl @: tmp) :|: (inr @: (start n2))
      | inr s => 
          inr @: ((tf n2) s ch)
      end;
  |}.
  Defined.

  Definition alt (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := (inl @: start n1) :|: (inr @: start n2);
    final := (inl @: (start n1)) :|: (inr @: (start n2));
    tf src ch := 
      match src with
      | inl s => inl @: ((tf n1) s ch)
      | inr s => inr @: ((tf n2) s ch)
      end
  |}.
  Defined.

  Definition star (n: t A): t A. refine {|
    state := state n;
    start := start n;
    final := (final n) :|: (start n);
    tf src ch :=
      let tmp := (tf n) src ch in
      if (final n) :&: tmp == set0 then tmp
      else tmp :|: (start n)
  |}.
  Defined.
End FAs.
