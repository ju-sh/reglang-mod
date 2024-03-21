From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Inductive tNfa: Type :=
| NZero: tNfa
| NOne: tNfa
| NPlus: tNfa -> tNfa -> tNfa.

Inductive tDfa: Type :=
| DOne: tDfa
| DPlus: tDfa -> tDfa -> tDfa
| DMult: tDfa -> tDfa -> tDfa.

Fixpoint tNfaDenote (s: tNfa): Type :=
  match s with
  | NZero => unit
  | NOne => unit + unit
  | NPlus a b => (tNfaDenote a) * (tNfaDenote b)
  end.

Fixpoint tDfaDenote (s: tDfa): Type :=
  match s with
	| DOne => unit
	| DPlus a b => (tDfaDenote a) + (tDfaDenote b)
	| DMult a b => (tDfaDenote a) * (tDfaDenote b)
	end.

Fixpoint pset (s: tNfa): tDfa :=
  match s with
  | NZero => DOne
  | NOne => DPlus DOne DOne
  | NPlus a b => DMult (pset a) (pset b)
  end.


(* Inductive t: Type := *)
(* | Zero *)
(* | One *)
(* | Plus: t -> t -> t *)
(* | Mult: t -> t -> t. *)

(* Fixpoint pset (e: t): t. refine ( *)
(*   match e with *)
(*   | Zero => One *)
(*   | One => Plus One One *)
(*   | Plus a b => Mult (pset a) (pset b) *)
(*   | Mult a b => _ *)
(*   end). *)
(*   refine ( *)
(*     match a with *)
(*     | Zero => pset b *)
(*     | One => Mult (Plus One One) (pset b) *)
(*     | Plus x y => Mult (pset (Mult x b)) (pset (Mult y b)) *)
(*     | Mult x y => _ *)
(*     end). *)
(* Abort. *)
