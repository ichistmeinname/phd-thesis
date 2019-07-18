Inductive peano : Type :=
| z : peano
| s : peano -> peano.

Definition isZero (p : peano) : bool :=
  match p with
  | z   => true
  | s _ => false
  end.

Fixpoint add (p1 p2 : peano) : peano :=
  match p1 with
  | z => p2
  | s p => s (add p p2)
  end.

(* Check Set. *)
(* Check Prop. *)

(* Set Printing All. *)
(* Set Printing Universes. *)
(* Check Type. *)

Notation "p1 + p2" := (add p1 p2) (left associativity, at level 50).

Compute (s z + s z).

Inductive list (A : Type) :=
| nil  : list A
| cons : A -> list A -> list A.

Check cons.

Definition Cons (A : Type) : A -> list A -> list A :=
  fun x xs => cons A x xs.

Fail Compute (cons z nil).

Compute (cons peano z (nil peano)).
Compute (cons _ z (nil _)).

Fixpoint length (A : Type) (xs : list A) : peano :=
  match xs with
  | nil       => z
  | cons _ ys => s (length ys)
  end.