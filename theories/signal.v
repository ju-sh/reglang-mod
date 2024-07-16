(* begin hide *)
Require List.
Require Import Coq.Program.Basics.
Open Scope program_scope.
Import List.ListNotations.
Require Streams.

Declare Scope signal_scope.
Delimit Scope signal_scope with signal.
(* end hide *)

(** * Signals.

Signals a captured by coinductive streams.

 *)

Definition t A := Streams.Stream A.

Notation " X :- Y " := (Streams.Cons X Y) (at level 70, right associativity) : signal_scope.
Infix "≡" := Streams.EqSt  (at level 70, no associativity) : signal_scope.
Bind Scope signal_scope with t.

Section Operations.
  Context {A : Type}.

  Definition const (a : A) : t A :=
    cofix ainf := (a :- ainf)%signal.

  Definition hd {A} := Streams.hd (A:=A).
  Definition tl {A} := Streams.tl (A:=A).
  Definition map {B}:= Streams.map (A := A) (B :=B).
  Definition zipWith {B C} := Streams.zipWith (A := A)(B := B)(C := C).
  Definition apply {B}(sf : t (A -> B))(sa : t A) := Streams.zipWith (fun f x => f x) sf sa.

  Definition prepend (l : list A) (sA : t A) : t A :=
    (List.fold_right (fun a s => a :- s) sA l)%signal.


  (** Emit a given value instead of the current value *)
  Definition emit  (a : A)(sA : t A) := (a :- Streams.tl sA)%signal.

  (** Emit multiple values replacing the corresponding values from the current stream *)
  Fixpoint emits (l : list A)(sA : t A) :=
    match l with
    | [] => sA
    | (x :: xs) => (x :- emits xs (Streams.tl sA))%signal
    end%list.

End Operations.


(**  * Mealy and Moore machines *)
Section Automaton.

  Context {state input output : Type}.

  CoFixpoint mealy (mf : state -> input -> state * output) (s0 : state) (inp : t input) : t output :=
    match inp with
    | i :- irest => let (s,o) := mf s0 i in
                o :- mealy mf s irest
    end%signal.

  Context (tr : state -> input -> state) (ofun : state -> output).
  CoFixpoint moore (s0 : state) (inp : t input) : t output :=
    match inp with
    | i :- irest => ofun s0 :- moore (tr s0 i) irest
    end%signal.

End Automaton.

(** * Signal properties *)


Definition sProp A  := t A -> Prop.

Section Modal.

  Context {A : Type}.

  Definition satisfy (P : A -> Prop) : sProp A := P  ∘ Streams.hd (A:=A).
  Definition here  (a : A)  : sProp A := satisfy (fun x => x = a).

  Context (sP : sProp A).
  Definition next    : sProp A   := sP ∘ Streams.tl (A:=A).
  Definition always  : sProp A   := Streams.ForAll sP.
  Definition eventually : sProp A   := Streams.Exists sP.

End Modal.

Section Lift.

  Context {A : Type}.
  Definition lift (fn : Prop -> Prop)      (P   : sProp A) : sProp A := fn ∘ P.
  Definition lift2 (fn : Prop -> Prop -> Prop) (P Q : sProp A) : sProp A := fun xs =>  fn (P xs) (Q xs).

  Definition sAnd := lift2 and.
  Definition sOr := lift2 or.
  Definition implies := lift2 (fun P Q => P -> Q).
  Definition iff     := lift2 (fun P Q => P <-> Q).

End Lift.

Infix "/\" := sAnd (at level 80, right associativity) : signal_scope.
Infix "\/" := sOr  (at level 85, right associativity) : signal_scope.
Infix "~ P" := (lift not P) (at level 75): signal_scope.

Fixpoint startsWith {A}(xs : list A) : sProp A :=
  match xs with
  | []    => fun _ => True
  | x :: xs => (here x /\ startsWith xs)%signal
  end%list.

Fixpoint within {A}(n : nat)(sP : sProp A) : sProp A :=
  match n with
  | 0 => sP
  | S m => (sP \/ next (within m sP))%signal
  end.

Module Until.
  Section Until.
    Context {A : Type}(sP sQ : sProp A).

    (** The weak until operation on signal predicates *)
    CoInductive wt  (xs : t A) :  Prop :=
    | Done : sQ xs -> wt xs
    | Step : sP xs -> wt (Streams.tl xs) -> wt xs.


    (** Strong until. When we have weak until as well as sQ to eventually hold *)
    Definition t := (wt /\ eventually sQ)%signal.

  End Until.
End Until.
