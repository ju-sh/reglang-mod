From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".


Section Lang.
  Definition t (A: Type) := pred (seq A).

  Context {A: Type}.

  Definition eps: t A :=  nilp (T:=A).

  Definition char (f: A -> bool): t A := fun w =>
    match w with
    | [:: x ] => f x
    | _ => false
    end.

  Definition cat (l1 l2: t A): t A := fun w =>
    [exists i : 'I_(size w).+1,
      l1 (seq.take i w) && l2 (seq.drop i w)].

  Definition alt  (l1 l2: t A): t A :=
    [pred w | (w \in l1) || (w \in l2)].

  Definition residual (l: t A) (x: A): t A := fun w =>
    l (x :: w).

  Definition star (l: t A): t A :=
    fix star w :=
      match w with
      | [:: x & w'] => cat (residual l x) star w'
      | [::] => true
      end.

  Lemma catP (l1 l2: t A) (w: seq A): reflect
    (exists w1 w2: seq A,
      w = w1 ++ w2 /\
      w1 \in l1 /\
      w2 \in l2)
    (w \in cat l1 l2).
  Proof.
    apply: (iffP exists_inP).
    - move => [i] Hl1 Hl2.
      exists (take i w).
      exists (drop i w).
      rewrite cat_take_drop.
      by split.
    - move => [w1 [w2 [Hw1w2 [H2 H3]]]].
      have Hi : size w1 < (size w).+1.
      + by rewrite Hw1w2 size_cat ltnS leq_addr.
      + exists (Ordinal Hi); subst.
        * by rewrite take_size_cat.
        * by rewrite drop_size_cat.
  Qed.
End Lang.

