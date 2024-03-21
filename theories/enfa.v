From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
Import state.StateNotations.

Record t {A: Type}: Type := mkEnfa {
  state: state.tNfa;
  start: {set nfa⟦state⟧};
  final: {set nfa⟦state⟧};
  tf: option A -> nfa⟦state⟧ -> nfa⟦state⟧ -> bool
}.
Arguments t: clear implicits.

Definition eps_closure {A: Type}
  (n: t A)(src: nfa⟦state n⟧) := [set dst | connect ((tf n) None) src dst].

Section FAs.
  Context {A: finType}.

  Definition nul: t A. refine {|
    state := state.NZero;
    start := set0;
    final := set0;
    tf ch src dst := false
  |}.
  Defined.

  Definition eps: t A. refine {|
    state := state.NOne;
    start := [set tt];
    final := [set tt];
    tf ch src dst :=
      match ch with
      | None => true
      | Some c => false
      end
  |}.
  Defined.

  Definition char (f: A -> bool): t A. refine {|
    state := state.NPlus state.NOne state.NOne;
    start := [set (inl tt)];
    final := [set (inr tt)];
    tf ch src dst :=
      match ch with
      | None => src == dst
      | Some c =>
          match src, dst with
          | inl _, inr _ => f c
          | _, _ => false
          end
      end
  |}.
  Defined.

  Definition cat (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := inl @: start n1;
    final := inr @: final n2;
    tf ch src dst :=
      match src, ch, dst with
      | inl s, Some _, inl d => (tf n1) ch s d 
      | inr s, Some _, inr d => (tf n2) ch s d 
      | inl s, None, inr d =>
          (s \in (final n1)) && (d \in (start n2))
      | _, _, _ => false
      end
  |}.
  Defined.

  Definition alt (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := (inl @: start n1) :|: (inr @: start n2);
    final := (inl @: (start n1)) :|: (inr @: (start n2));
    tf ch src dst := 
      match ch with
      | None => src == dst
      | Some c =>
          match src, dst with
          | inl s, inl d => (tf n1) ch s d
          | inr s, inr d => (tf n2) ch s d
          | _, _ => false
          end
      end
  |}.
  Defined.

  Definition star (n: t A): t A. refine {|
    state := state.NPlus state.NOne (state n);
    start := [set (inl tt)];
    final := [set (inl tt)];
    tf ch src dst :=
      match src, ch, dst with
      | inl _, None, inl _ => true
      (* | inl _, Some _, inl _ => false *)
      | inl _, None, inr d => d \in (start n)
      (* | inl _, Some _, inr d => d \in (start n) *)
      | inr s, None, inl _ => s \in (final n)
      (* | inr s, Some _, inl _ => s \in (final n) *)
      | inr s, None, inr d => s == d
      | inr s, Some _, inr d => (tf n) ch s d
      | _, _, _ => false
      end
  |}.
  Defined.
End FAs.
