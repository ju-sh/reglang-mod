From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require state.
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

Module Enfa.
  Record t {A: Type}: Type := mkEnfa {
    state: state.tNfa;
    start: {set nfa⟦state⟧};
    final: {set nfa⟦state⟧};
    tf: option A -> nfa⟦state⟧ -> nfa⟦state⟧ -> bool
  }.
  #[global] Arguments t: clear implicits.

  Inductive accept {A: Type} {n: t A}: nfa⟦state n⟧ -> seq A -> Prop :=
    | EnfaFin (s: nfa⟦state n⟧)
        : s \in final n -> accept s [::]
    | EnfaSome (s: nfa⟦state n⟧) (ch: A) (d: nfa⟦state n⟧) (w: seq A)
        : (tf n) (Some ch) s d -> accept d w -> accept s (ch::w)
    | EnfaNone (s d: nfa⟦state n⟧) (w: seq A)
        : (tf n) None s d -> accept d w -> accept s w.

  Definition to_lang {A: Type} (n: t A) (w: seq A) :=
    exists2 src: nfa⟦state n⟧, src \in (start n) & accept src w.

  Definition eps_closure {A: Type} (n: t A)(src: nfa⟦state n⟧) :=
    [set dst | connect ((tf n) None) src dst].

  Lemma lift_accept {A: Type} (n: t A) (src dst: nfa⟦state n⟧) (w: seq A)
    : dst \in eps_closure n src -> accept dst w -> accept src w.
  Proof.
    rewrite inE => /connectP [s].
    elim: s src w dst =>
      [ src w dst _ -> //
      | dst dsts IHw src w dst' /=].
    case/andP => /= Htf Hpath Heq HAccdst'.
    have H := IHw dst w dst' Hpath Heq HAccdst'.
    exact: (Enfa.EnfaNone src dst w Htf H).
  Qed.
End Enfa.

Definition of_enfa {A: Type} (n: Enfa.t A): t A := {|
  state := Enfa.state n;
  start := \bigcup_(p in Enfa.start n) (Enfa.eps_closure n p);
  final := Enfa.final n;
  tf p a q := [exists p',
    (Enfa.tf n) (Some a) p p' &&
    (q \in Enfa.eps_closure n p')]
|}.


Section EnfaFAs.
  Context {A: Type}.

  Definition ecat (n1 n2: t A): Enfa.t A. refine {|
    Enfa.state := state.NPlus (state n1) (state n2);
    Enfa.start := inl @: start n1;
    Enfa.final := inr @: final n2;
    Enfa.tf ch src dst :=
      match src, ch, dst with
      | inl s, Some c, inl d => (tf n1) s c d 
      | inr s, Some c, inr d => (tf n2) s c d 
      | inl s, None, inr d =>
          (s \in (final n1)) && (d \in (start n2))
      | _, _, _ => false
      end
  |}.
  Defined.

  Definition estar (n: t A): Enfa.t A. refine {|
    Enfa.state := state.NPlus state.NOne (state n);
    Enfa.start := [set (inl tt)];
    Enfa.final := [set (inl tt)];
    Enfa.tf ch src dst :=
      match src, ch, dst with
      | inl _, None, inl _ => true
      | inl _, None, inr d => d \in (start n)
      | inr s, None, inl _ => s \in (final n)
      | inr s, None, inr d => s == d
      | inr s, Some c, inr d => (tf n) s c d
      | _, _, _ => false
      end
  |}.
  Defined.
End EnfaFAs.

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


  Definition cat (n1 n2: t A): t A := of_enfa (ecat n1 n2).
  Definition star (n: t A): t A := of_enfa (estar n).

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
    by move/exists_inP => [[]].
  - case: w => [|a w'] //=.
    rewrite /lang.eps unfold_in => _.
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
      case: src; last by case; rewrite inE.
      case.
      rewrite inE => _ /= /exists_inP => [[src1]].
      case src1; first by case.
      case.
      case (f a) => [_|]; last by [].
      elim: w' => [|a2 w' IH] //=.
      move/exists_inP.
      by move => [src2].
  - rewrite /lang.char /=.
    case w => [|a [|b w']]; first by []; last by [].
    case (f a) eqn:Hfa => [_|]; last by [].
    exists (inl tt); first by rewrite inE.
    apply/exists_inP => //=. 
    rewrite Hfa.
    exists (inr tt); first by [].
    by rewrite inE.
Qed.


Lemma enfaE {A: Type} {n: Enfa.t A} (w: seq A) (src: nfa⟦Enfa.state n⟧):
  (Enfa.accept src w) <->
  (exists2 dst : nfa⟦state (of_enfa n)⟧,
    dst \in Enfa.eps_closure n src & accept (of_enfa n) dst w).
Proof.
  split => /=.
  - elim => {src w}
      [ fin H
      | src ch dst w H H1 [dst' Heps Hacc]
      | dst dst' w H H1 [s Heps Hacc]].
    + exists fin => //.
      by rewrite inE connect0.
    + exists src => /=; first by rewrite inE.
      apply/exists_inP.
      exists dst' => //.
      apply/exists_inP.
      by exists dst.
    + exists s; last by [].
      rewrite inE in Heps.
      rewrite inE.
      exact: (connect_trans (connect1 _) Heps).
  - elim: w src => //=.
    + move => src [s] Heps Hfin.
      apply: (Enfa.lift_accept n _ s) => //.
      by apply: (Enfa.EnfaFin s).
    + move => ch w IH.
      move => src [s] Heps.
      case/exists_inP.
      move => dst.
      move/exists_inP => [d Hsd Hdd] H.
      apply: (Enfa.lift_accept n src _ (ch::w) Heps).
      apply: (Enfa.EnfaSome s ch _ w Hsd).
      apply: IH.
      by exists dst.
Qed.

Lemma of_enfaP {A: Type} (n: Enfa.t A) (w: seq A)
  : reflect (Enfa.to_lang n w) (w \in to_lang (of_enfa n)).
Proof.
  apply: (iffP exists_inP).
  - move => [src Hin Hacc].
    case/bigcupP: Hin => begin H1 H2.
    rewrite /Enfa.to_lang.
    exists begin => //.
    apply/enfaE.
    exists src => //.
  - rewrite /Enfa.to_lang.
    move => [esrc Hestart] /enfaE [src HesrcEps Hacc].
    exists src => //.
    apply/bigcupP.
    by exists esrc.
Qed.

Lemma cat_correct {A: Type} (n1 n2: t A):
  to_lang (cat n1 n2) =i lang.cat (to_lang n1) (to_lang n2).
  (* lang.cat (re.to_lang r1) (re.to_lang r2) =i re.to_lang (re.Cat r1 r2). *)
Proof.
  move => w.
