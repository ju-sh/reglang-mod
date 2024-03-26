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
    start := [set s |
      match s with
      | inl s => s \in start n1
      | inr s => s \in start n2
      end];
    final := [set s |
      match s with
      | inl s => s \in final n1
      | inr s => s \in final n2
      end];
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

Section EnfaLemmas.
  Context {A: Type}.

  Lemma enfa_catIr (n1 n2: t A) (src: nfa⟦state n2⟧) (w: seq A)
    : accept n2 src w -> Enfa.accept (n:=ecat n1 n2) (inr src) w.
  Proof.
    elim: w src.
    - move => fin H. 
      constructor => /=.
      by apply: (imset_f inr).
    - move => ch w IHw src2 /= /exists_inP [dst2] Htf H.
      have HH := IHw dst2 H.
      exact: (Enfa.EnfaSome (n:=ecat n1 n2) (inr src2) ch (inr dst2) w Htf HH).
  Qed.

  Lemma enfa_catIl (n1 n2: t A) (src: nfa⟦state n1⟧) (w1 w2: seq A)
    : accept n1 src w1 -> w2 \in to_lang n2 ->
      Enfa.accept (n:=ecat n1 n2) (inl src) (w1++w2).
  Proof.
    elim: w1 src => /=.
    - move => fin1 H1.
      move/exists_inP => [src2] H2 H3.
      apply: ((Enfa.EnfaNone (n:=ecat n1 n2) (inl fin1)) (inr src2) w2); first by rewrite /= H1.
      exact: enfa_catIr n1 n2 src2 w2 H3.
    - move => ch w IHw src /exists_inP [s] Htf H1 H.
      apply: (Enfa.EnfaSome (n:=ecat n1 n2) (inl src) ch (inl s) (w++w2)) => //.
      exact: IHw s H1 H.
  Qed.

  Lemma enfa_catE (n1 n2: t A) (src: nfa⟦Enfa.state (ecat n1 n2)⟧) (w: seq A):
    Enfa.accept src w ->
    match src with
    | inl s => exists w1 w2: seq A,
        [/\ w = w1++w2, accept n1 s w1 & w2 \in to_lang n2]
    | inr s => accept n2 s w
    end.
  Proof.
    elim => {src w}.
    - by move => src /imsetP [dst] Hdst ->.
    - move => [src|src] ch [dst|dst] w //.
      + move => /= Htf Hacc [w1] [w2] [H1 H2 H3].
        exists (ch::w1).
        exists w2.
        subst.
        split => //.
        rewrite /accept.
        apply/exists_inP.
        by exists dst.
      + move => /= Htf Hacc Heacc.
        apply/exists_inP.
        by exists dst.
    - move => [src|src] [dst|dst] //=.
      move => w /andP [H1 H2] Heacc Hacc.
      exists [::] => /=.
      exists w => //=.
      split => //.
      apply/exists_inP.
      by exists dst.
  Qed.

  Lemma enfa_catP (n1 n2: t A) (w: seq A): reflect
    (Enfa.to_lang (ecat n1 n2) w)
    (lang.cat (to_lang n1) (to_lang n2) w).
  Proof.
    apply: (iffP (lang.catP (to_lang n1) (to_lang n2) w)).
    - move => [w1] [w2] [H1 [H2 H3]].
      case/exists_inP: H2 => src Hsrc Hacc.
      exists (inl src) => /=.
      apply: imset_f => //.
      rewrite H1.
      by apply: enfa_catIl.
    - rewrite /Enfa.to_lang.
      move => [[src|src]]; last by case/imsetP. (* TODO: How the last ?? *)
      move/imsetP => [src1] H1 H2 /enfa_catE [w1] [w2] [H3 H4 H5].
      exists w1; exists w2.
      split => //; split => //.
      apply/exists_inP.
      exists src1 => //.
      assert (src = src1); first by case: H2.
      by rewrite -H.
  Qed.

  Lemma enfaE {n: Enfa.t A} (w: seq A) (src: nfa⟦Enfa.state n⟧):
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

  Lemma of_enfaP (n: Enfa.t A) (w: seq A)
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

  Lemma enfa_star_cat (n: t A) (w1 w2: seq A) (src: nfa⟦Enfa.state (estar n)⟧):
    Enfa.accept src w1 ->
    Enfa.to_lang (estar n) w2 ->
    Enfa.accept src (w1 ++ w2).
  Proof.
    elim => {src w1}.
    - move => src.
      rewrite inE => /eqP ->.
      rewrite /Enfa.to_lang.
      case => s.
      by rewrite inE => /eqP ->.
    - move => src ch dst w /=.
      case src => src' //.
      case dst => dst' //.
      move => Htf Hacc IH H.
      (* Check (Enfa.EnfaSome (n:=estar n) (inr src') ch (inr dst') (ch :: w ++ w2) _). *)
      exact: Enfa.EnfaSome (IH H). (* TODO: How .... ? *)
    - move => src dst w Htf Hacc IH H.
      exact: Enfa.EnfaNone (IH H). (* TODO: How .... ? *)
  Qed.

  Lemma enfa_starP (n: t A) (w: seq A): reflect
    (Enfa.to_lang (estar n) w)
    (lang.star (to_lang n) w).
  Proof.
    apply: (iffP idP).
    - case/lang.starP => wl H ->.
      elim: wl H => /=.
      + move => _.
        rewrite /Enfa.to_lang.
        exists (inl tt).
        * by rewrite inE.
        * apply: Enfa.EnfaFin => /=.
          by rewrite inE.
      + move => w' wl IH /andP [/andP [H1 H2] H3].
        rewrite /Enfa.to_lang.
        exists (inl tt).
        * by rewrite inE.
        * 
  Abort.
End EnfaLemmas.
 

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

Lemma cat_correct {A: Type} (n1 n2: t A):
  to_lang (cat n1 n2) =i lang.cat (to_lang n1) (to_lang n2).
Proof.
  move => w.
  by apply/of_enfaP/idP; move => H; apply/enfa_catP.
Qed.

Lemma alt_correct {A: Type} (n1 n2: t A):
  to_lang (alt n1 n2) =i lang.alt (to_lang n1) (to_lang n2).
Proof.
  move => w.
  apply/idP/idP.
  - case/exists_inP => [[src|src]].
    + rewrite !inE => Hsrc Hacc.
      apply/orP.
      left.
      apply/exists_inP.
      exists src => //.
      elim: w src {Hsrc} Hacc => /=.
      * move => src. 
        by rewrite inE.
      * move => ch w IH src.
        case/exists_inP.
        move => [|] // s Htf /= /IH H.
        apply/exists_inP.
        by exists s.
    + rewrite !inE => Hsrc Hacc.
      apply/orP.
      right.
      apply/exists_inP.
      exists src => //.
      elim: w src {Hsrc} Hacc => /=.
      * move => src. 
        by rewrite inE.
      * move => ch w IH src.
        case/exists_inP.
        move => [|] // s Htf /= /IH H.
        apply/exists_inP.
        by exists s.
  - rewrite !inE.
    case/orP.
    + move/exists_inP => [start1] Hstart1 Hacc.
      apply/exists_inP.
      exists (inl start1).
      rewrite inE //.
      elim: w start1 {Hstart1} Hacc => //=.
      * move => start1 Hstart1.
        by rewrite inE.
      * move => ch w IH start1.
        move/exists_inP => [d] Htf /IH Hacc.
        apply/exists_inP.
        by exists (inl d).
    + move/exists_inP => [start2] Hstart2 Hacc.
      apply/exists_inP.
      exists (inr start2).
      rewrite inE //.
      elim: w start2 {Hstart2} Hacc => //=.
      * move => start2 Hstart2.
        by rewrite inE.
      * move => ch w IH start2.
        move/exists_inP => [d] Htf /IH Hacc.
        apply/exists_inP.
        by exists (inr d).
Qed.

Lemma star_correct {A: Type} (n: t A):
  to_lang (star n) =i lang.star (to_lang n).
Proof.
  move => w.
  apply/of_enfaP/idP.
Admitted.

Section OfRe.
  Context {A: Type}.

  Fixpoint of_re (r: re.t A): t A :=
    match r with
    | re.Eps => eps
    | re.Char f => char f
    | re.Cat r1 r2 => cat (of_re r1) (of_re r2)
    | re.Alt r1 r2 => alt (of_re r1) (of_re r2)
    | re.Star rr => star (of_re rr)
    end.

  Theorem of_re_correctness (r: re.t A):
    to_lang (of_re r) =i re.to_lang r.
  Proof.
    elim: r.
    - exact: eps_correct.
    - apply: char_correct.
    - move => r1 IHr1 r2 IHr2 w /=.
      rewrite cat_correct.
      exact: lang.cat_eq.
    - move => r1 IHr1 r2 IHr2 w /=.
      rewrite alt_correct.
      rewrite /lang.alt.
      rewrite inE IHr1 IHr2.
      by rewrite inE.
    - move => r IHr.
  Abort.
End OfRe.
