(* begin hide *)
Require Import signal.
Declare Scope hsignal_scope.
Delimit Scope hsignal_scope with hsignal.
(* end hide *)

(* * Hetrogeneous Signals

In a signal all values are of the same type. A signal is therefore
like a list (but co-inductive and hence infinite). A hetrogeneous
signal is a signal whose elements have potentially different types.
It can be seen as a generalisation of hetrogeneous lists.

 *)

CoInductive t {sort : Type}(A : sort -> Type) : signal.t sort -> Type :=
| HCons : forall s : sort,  A s -> forall sgn : signal.t sort, t A sgn -> t A (s :- sgn)%signal.

Arguments HCons {sort}{A}{s} _ {sgn}.

Infix ":-" := HCons  (at level 70, right associativity) : hsignal_scope.
