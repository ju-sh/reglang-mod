From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
From aruvi Require enfa.
From aruvi Require re.
Import state.StateNotations.

Record t {A: Type}: Type := mkNfa {
  state: state.tNfa;
  start: {set nfa⟦state⟧};
  final: {set nfa⟦state⟧};
  tf: nfa⟦state⟧ -> A -> nfa⟦state⟧ -> bool
}.
Arguments t: clear implicits.

(* Section Coerce. *)
(*   Context {A: Type}. *)
(*   Parameter (n: t A). *)
(*   Definition nfa_to_state (n: t A): finType := nfa⟦state n⟧. *)
(*   Coercion nfa_to_state: n >-> finType. *)
(* End Coerce. *)

Definition of_enfa {A: Type} (n: enfa.t A): t A := {|
  state := enfa.state n;
  start := \bigcup_(p in enfa.start n) (enfa.eps_closure n p);
  final := enfa.final n;
  tf p a q := [exists p',
    (enfa.tf n) (Some a) p p' &&
    (q \in enfa.eps_closure n p')]
|}.

Section FAs.
  Context {A: Type}.

  (* Like 𝟘 *)
  Definition nul: t A. refine {|
    state := state.NZero;
    start := set0;
    final := set0;
    tf src ch dst := false
  |}.
  Defined.

  (* Like 𝟙 *)
  Definition eps: t A. refine {|
    state := state.NOne;
    start := [set tt];
    final := [set tt];
    tf src ch dst := false
  |}.
  Defined.

  Definition char (f: A -> bool): t A. refine {|
    state := state.NPlus state.NOne state.NOne;
    start := [set (inl tt)];
    final := [set (inr tt)];
    tf src ch dst :=
       match src, dst with
       | inl _, inr _ => f ch
       | _, _ => false
       end
  |}.
  Defined.

  (* Definition cat (n1 n2: t A): t A. refine {| *)
  (*   state := state.NPlus (state n1) (state n2); *)
  (*   start := inl @: start n1; *)
  (*   final := inr @: final n2; *)
  (*   tf src ch dst := *)
  (*     match src, dst with *)
  (*     | inl s, inl d => (tf n1) s ch d *) 
  (*     | inr s, inr d => (tf n2) s ch d *) 
  (*     | inl s, inr d => *)
  (*         (s \in (final n1)) && (d \in (start n2))  (1* TODO *1) *)
  (*     | _, _ => false *)
  (*     end *)
  (* |}. *)
  (* Defined. *)

  Definition alt (n1 n2: t A): t A. refine {|
    state := state.NPlus (state n1) (state n2);
    start := (inl @: start n1) :|: (inr @: start n2);
    final := (inl @: (start n1)) :|: (inr @: (start n2));
    tf src ch dst := 
      match src, dst with
      | inl s, inl d => (tf n1) s ch d
      | inr s, inr d => (tf n2) s ch d
      | _, _ => false
      end
  |}.
  Defined.


  (* Definition star (n: t A): t A. refine {| *)
  (*   state := state.NPlus state.NOne (state n); *)
  (*   start := [set (inl tt)]; *)
  (*   final := [set (inl tt)]; *)
  (*   tf src ch dst := *)
  (*     match src, dst with *)
  (*     | inl _, inl _ => false *)
  (*     | inl _, inr d => d \in (start n) *)
  (*     | inr s, inl _ => s \in (final n) *)
  (*     | inr s, inr d => s \in (final n) *)
  (*     (1* if (src \in final n) && (dst \in start n) *1) *)
  (*     (1* match *1) *) 

  (*     (1* let tmp := (tf n) src ch in *1) *)
  (*     (1* if (final n) :&: tmp == set0 then tmp *1) *)
  (*     (1* else tmp :|: (start n) *1) *)
  (* |}. *)
  (* Defined. *)
End FAs.

Section Sem.
  Context {A: Type}.

  Fixpoint accept (n: t A) (src: nfa⟦state n⟧)
    (w: list A): bool :=
    match w with
    | [::] => src \in (final n)
    | [:: ch & w'] =>
        [exists (dst | (tf n) src ch dst), accept n dst w']
    end.

  Definition to_lang (n: t A): lang.t A :=
    [pred w | [exists src, (src \in (start n)) && (accept n src w)]].
End Sem.

Lemma eps_correct {A: Type}:
  to_lang (A:=A) eps =i re.to_lang re.Eps.
Proof.
  rewrite /= => w.
  apply/exists_inP/idP.  (* ??? *)
  - move => [[_]] //=.
    case: w => [|a w'] //=.
    move/exists_inP.
    by move => [[]].
  - rewrite //=.
    case: w => [|a w'] //=.
    rewrite /lang.eps.
    rewrite unfold_in => _.
    by exists tt; rewrite inE.
Qed.

Lemma char_correct {A: Type} (f: A -> bool):
  to_lang (char f) =1 re.to_lang (re.Char f).
Proof.
  move => w //=.
  apply/exists_inP/idP => //=.
  - case w => [|a w'].
    + move => [src] //=.
      by case: src; case; rewrite !inE.
    + move => [src].
      case: src.
      * case; rewrite inE.
        move => _ /= /exists_inP.
        move => [src1].
        case src1; first by case.
        case.
        case (f a); last by [].
        move => _.
        rewrite /accept.
        rewrite /=.
        shelve.

      * by case; rewrite inE.
Restart.
  move => w //=.
  apply/exists_inP/idP => //=.
  - case w => [|a w'].
    + rewrite /=.
      move => [src].
      case: src; case; rewrite inE.
      * by rewrite inE.
      * by [].
    + move => [src].
      case: src; case; rewrite inE.
      * move => _.
Restart.
  move => w //=.
  apply/exists_inP/idP.
  - rewrite /=.
    move => [src].
    case w => [|a [|b w']]; first by case src eqn:Hsrc => //=; rewrite !inE.
    + case src eqn:Hsrc.
      * case u.
        rewrite inE => _.
        case (f a) eqn:Hfa.
        -- rewrite /=.
        rewrite /=.
        move/exists_inP.
        move => [src2].


    case w eqn:Hw.
    + rewrite /=.
      case src eqn:Hsrc.
      * rename u into l; case l.
        by rewrite !inE.
      * rename u into r; case r.
        by rewrite inE.
    + case src eqn:Hsrc.
      * rename l into w'.
        rename u into l. case l.
        rewrite inE => _.
        rewrite /lang.char.


        case (f a) eqn:Hfa.
        -- rewrite /=.
           move/exists_inP.
           move => [src2].
        rewrite /=.
        move/exists_inP.
        move => [H].
      * rename u into l; case l.


    case src.
    + move => l.
      rewrite inE. case: l => _.
      case w eqn:Hw => //=; first by rewrite /= inE.
      rename l into w'.
      move/exists_inP.
      move => [s].
      case s.
      * 
      case (f a) eqn:Hfa.
      * rewrite /=.
        move/exists_inP.
        move => [src2].
        case src2.
        -- move => l _ /=.

    case w eqn:Hw => //=.
    + case src; first by move => ?; rewrite inE.
      case.
      rewrite inE //=.

    move => a w'.
    move/exists_inP.
    case (f a).
    + case src.
      * move => H.
        move => [aa].
