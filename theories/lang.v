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

  Lemma cat_eq (l1 l2 l3 l4: t A):
    l1 =i l2 ->
    l3 =i l4 ->
    cat l1 l3 =i cat l2 l4.
  Proof.
    move => H1 H2 w.
    apply: eq_existsb => n. 
    by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
  Qed.

  (* Out of all words, there exists a list of words which is part of l and is
     not ε.
     Concatenation of all words in wl would also be in star l. Clever! *)
  Lemma starP (l: t A) (w: seq A): reflect
    (exists2 wl: seq (seq A),
       all [predD l & eps] wl & w = flatten wl)
    (w \in star l).
  Proof.
    (* TODO: ??? -2 and 1 should be same, right? And what's _.+1 *)
    (* elim: {w} _.+1 {-2}w (ltnSn (size w)) => //. *)
    elim: {w} _.+1 {-2}w (ltnSn (size w)); first by [].
    move => n IHw.
    case => /=.
    - move => Hsz.
      left.
      by exists [::].
    - move => ch w Hsz.
      apply (iffP (catP _ _ w)).
      + move => [w1] [w2] [Hw1w2] [H1].
        case/IHw.
        * rewrite -ltnS (leq_trans _ Hsz) //. (* TODO: How ?....? *)
          by rewrite Hw1w2 size_cat !ltnS leq_addl.
        * move => wl Hall H.
          exists ((ch::w1) :: wl); first by apply/andP; split.
          by rewrite Hw1w2 H.
      + move => [[|[|ch' w'] wl] //=].
        case/andP => Hw' Hall [Hch Hw].
        exists w'; exists (flatten wl).
        subst.
        do 2! split => //.
        apply/IHw.
        * rewrite -ltnS (leq_trans _ Hsz) //. (* TODO: How ?....? *)
          rewrite size_cat.
          rewrite 2!ltnS.
          apply: leq_addl.
        * by exists wl.
  Qed.

  Lemma star_cat (l: t A) (w1 w2: seq A):
    w1 \in l ->
    w2 \in (star l) ->
    w1 ++ w2 \in star l.
  Proof.
    case: w1 => [|a w1] // H1 /starP [wl Ha Hf].
    apply/starP.
    by exists ((a::w1) :: wl); rewrite ?Hf //= H1.
  Qed.

  Lemma star_eq (l1 l2: t A):
    l1 =i l2 -> star l1 =i star l2.
  Proof.
    move => H w.
    apply/starP/starP.
    - move => [wl] Hall Hflatten.
      exists wl => //.
      erewrite eq_all.
      eexact Hall.
      move => x /=.
      by rewrite H.
    - move => [wl] Hall Hflatten.
      exists wl => //.
      erewrite eq_all.
      eexact Hall.
      move => x /=.
      by rewrite H.
  Qed.
End Lang.
