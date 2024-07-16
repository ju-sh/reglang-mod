(* begin hide *)
Require Import signal.
Require List.
Import List.ListNotations.
Require Import Coq.Program.Basics.
Open Scope program_scope.
Global Declare Scope event_scope.
Global Delimit Scope event_scope with event.
(* end hide *)

(** * Events

Events are essentially signals that are enabled once in a while.


*)

Definition t A := signal.t (option A).

Section OneEventType.
  Context {A : Type}.
  (** Prefix an event by a particular value *)
  Definition prefix (a : A)(eA : t A) : t A := (Some a :- eA)%signal.

  (** Delay a given event by a single cycle *)
  Definition delay (eA : t A)  := (None :- eA)%signal.

  (** Prepend a list of values to the event stream *)
  Definition prepend (l : list A):= signal.prepend (List.map Some l).

  (** The event that is always disabled *)
  Definition null : t A := signal.const None.
  Definition single (a : A) : t A := prefix a null.

  (** Emit a given value instead of the current event *)
  Definition emit (a : A) := signal.emit (Some a).
  (** Emit a list of events, at the beginning of an event stream, ignoring
      whatever events is currently being produced
   *)
  Definition emits (l : list A) := signal.emits (List.map Some l).
  Definition delayBy (n : nat) := Nat.iter n delay.

  Definition option_join (ooa : option (option A)) : option A :=
    match ooa with
    | Some x => x
    | None   => None
    end.

  Definition events : t (option A) -> t A := signal.map option_join.

End OneEventType.


(** * Merging  even streams *)


Section Merge.

  Context {A B : Type}.


  Section MergeWith.
    Context {C : Type}(a2c  : A -> C)(b2c  : B -> C).

    Definition opt_merge (ab2c : A -> B -> C) (oa : option A)(ob : option B) : option C :=
      match oa, ob with
      | Some a, Some b => Some (ab2c a b)
      | Some a, _      => Some (a2c a)
      | _     , Some b => Some (b2c b)
      | _     , _      => None
      end.

    Definition mergeWith (ab2c : A -> B -> C) := signal.zipWith (opt_merge ab2c) .

    (** Left biased merging *)
    Definition mergeWithL := mergeWith (fun a b => a2c a).

    (** Right biased merging *)
    Definition mergeWithR := mergeWith (fun a b => b2c b).

  End MergeWith.

  (** Left biased merge *)
  Definition mergeL := mergeWithL inl inr.

  (** Right biased merge *)
  Definition mergeR := mergeWithR inl inr.

End Merge.

Definition combineL {A} := mergeWithL (A := A) id id.
Definition combineR {A} := mergeWithL (A := A) id id.
