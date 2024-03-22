From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".


Section Lang.
  Definition t (A: Type) := pred (seq A).

  Context {A: Type}.

  Definition eps: t A :=  nilp (T:=A).
		(* match w with *)
		(* | [::] => true *)
    (* | _ => false *)
		(* end. *)

	Definition char (f: A -> bool): t A := fun w =>
		match w with
    | [:: x ] => f x
    | _ => false
		end.

	Definition cat (l1 l2: t A): t A :=
		fun v => [exists i : 'I_(size v).+1,
			l1 (seq.take i v) && l2 (seq.drop i v)].

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
End Lang.
