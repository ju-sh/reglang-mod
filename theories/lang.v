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

  (* Lemma catI (l1 l2: t A) (w1 w2: seq A) *)
  (*   : w1 \in l1 -> *)
  (*     w2 \in l2 -> *)
  (*     w1 ++ w2 \in cat l1 l2. *)
  (* Proof. *)
  (*   move => Hl1 Hl2. *)
  (*   apply/catP. *)
  (*   by exists w1; exists w2. *)
  (* Qed. *)

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
        * rewrite -ltnS.
          rewrite (leq_trans _ Hsz) //. (* TODO: How ?....? *)
          by rewrite Hw1w2 size_cat !ltnS leq_addl.
        * move => wl Hall H.
          exists ((ch::w) :: wl).
          -- apply/andP.
             split => //.
             (* rewrite Hw1w2. *)
             subst.
             rewrite simpl_predE.
             apply/andP.
             split => //.
             (*
             H1 => ch :: w1 \in l
             Hall => flatten wl \in l
             => concat of these also \in l
             *)
             
          
             
(* ltnS : forall m n : nat, (m < n.+1) = (m <= n) *)

  Abort.    
End Lang.

