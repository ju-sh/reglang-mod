From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Reserved Notation "'set⟦' s '⟧'" (at level 20).
Reserved Notation "'pset⟦' s '⟧'" (at level 20).

Inductive t: Type :=
| zero: t
| one: t
| mop: t -> t -> t.

Fixpoint tSetDenote (s: t): Type :=
  (match s with
  | zero => void
  | one => unit
  | mop a b => set⟦a⟧ + set⟦b⟧
  end)%type
where "'set⟦' s '⟧'" := (tSetDenote s).

Fixpoint tPsetDenote (s: t): finType :=
  (match s with
  | zero => unit
  | one => unit + unit
  | mop a b => pset⟦a⟧ * pset⟦b⟧
  end)%type
where "'pset⟦' s '⟧'" := (tPsetDenote s).

Fixpoint abstr {s: t}: pset⟦s⟧ -> (set⟦s⟧ -> bool).
Proof.
  refine (
    match s with
    | zero => fun ps vd => true
    | one => fun lr =>
        match lr with
        | inl _ => fun _ => false
        | inr _ => fun _ => true
        end
    | mop a b => _
    end).
  move => /= [a' b']; case.
  - exact: abstr a a'. 
  - exact: abstr b b'. 
Defined.

Fixpoint reify {s: t}: (set⟦s⟧ -> bool) -> pset⟦s⟧.
refine (
  match s with
  | zero => fun f => tt
  | one => fun f =>
      if (f tt) then inr tt  (* TODO *)
      else inl tt
  | mop a b => fun f => (_, _)
  end).
- apply: reify => sa.
  exact: f (inl sa).
- apply: reify => sb.
    exact: f (inr sb).
Defined.

Lemma foo1 {s: t}: forall (p: pset⟦s⟧),
  reify (abstr p) = p.
Proof.
  elim: s => [||s1 IHs1 s2 IHs2 /= [p1 p2]].
  - by case.
  - by case; case.
  - by rewrite IHs1 IHs2.
Qed.

Lemma foo2 {s: t}: forall (f: set⟦s⟧ -> bool),
  abstr (reify f) =i f.
Proof.
  move => f a.
  rewrite !unfold_in /= -/abstr.
  case: s f a => //=.
  - move => f a.
    case (f tt) eqn:Hftt.
    case: a.
    + case (f a) => //.

