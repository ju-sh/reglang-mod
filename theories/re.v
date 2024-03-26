From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

From aruvi Require lang.

Inductive t {A: Type}: Type :=
| Eps: t
| Char: (A -> bool) -> t
| Cat: t -> t -> t
| Alt: t -> t -> t
| Star: t -> t.
Arguments t: clear implicits.

Section Combinators.
  Context {A: Type}.

  Definition any: t A := Char (fun _ => true).

  Fixpoint repn (r: t A) (n: nat): t A :=
    match n with
    | O => Eps
    | S n' => Cat r (repn r n')
    end.

  Definition repnm (r: t A) (low high: nat): t A :=
    match Nat.ltb high low with
    | true => Eps
    | _ =>
        let idxs := List.seq 0 ((high-low).+1) in
        let rs := List.map (repn r) idxs in
        let rn := repn r low in
        let rs' := List.map (Cat rn) rs in
        List.fold_right (fun x acc => Alt acc x) Eps rs'
    end.
End Combinators.

Fixpoint to_lang {A: Type} (r: t A): lang.t A :=
  match r with
  | Eps => lang.eps
  | Char f => lang.char f
  | Cat r1 r2 => lang.cat (to_lang r1) (to_lang r2)
  | Alt r1 r2 => lang.alt (to_lang r1) (to_lang r2)
  | Star rr => lang.star (to_lang rr)
  end.

Module ReNotations.
  Declare Scope re_scope.
  Delimit Scope re_scope with re.

  Notation "'↑' c" := (Char c) (at level 25, no associativity): re_scope.
  Notation "r '⁎'" := (Star r) (at level 30, right associativity): re_scope.
  Infix ";" := Cat (at level 35, right associativity): re_scope.
  Infix "│" := Alt (at level 41, right associativity): re_scope.
  Notation "'ε'" := Eps: re_scope.
  Notation "'⋅'" := any: re_scope.
  Notation "r '❴' n '❵'" := (repn r n) (at level 20): re_scope.
  Notation "r '❴' low ',' high '❵'" := (repnm r low high)
    (at level 20): re_scope.

  Notation "'⟦' c '⟧'" := (Char (Nat.eqb c)) (at level 50): re_scope.
  Notation "'❮' c '❯'" := (Char (Bool.eqb c)) (at level 50): re_scope.
End ReNotations.
