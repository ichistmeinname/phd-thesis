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

Set Implicit Arguments.
Arguments nil [_].
Arguments cons [_].

Fixpoint length (A : Type) (xs : list A) : peano :=
  match xs with
  | nil       => z
  | cons _ ys => s (length ys)
  end.

Fixpoint map (A B : Type) (f : A -> B) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | cons y ys => cons (f y) (map f ys)
  end.

Lemma map_length' (A B : Type) (f : A -> B) (xs : list A) : length xs = length (map f xs).
Proof.
  induction xs as [ | y ys H ].
  - simpl. reflexivity.
  - simpl.
    rewrite -> H.
    reflexivity.
Qed.

Fixpoint map_length (A B : Type) (f : A -> B) (xs : list A) : length xs = length (map f xs) :=
  match xs with
  | nil => eq_refl (length nil)
  | cons y ys => let H := map_length f ys in eq_ind_r (fun p => s p = s _) eq_refl H
  end.

Inductive vector (A : Type) : peano -> Type :=
| vnil  : vector A z
| vcons : forall n, A -> vector A n -> vector A (s n).

Arguments vnil [_].

Fixpoint vmap (A B : Type) (n : peano) (f : A -> B) (xs : vector A n) : vector B n :=
  match xs with
  | vnil       => vnil
  | vcons y ys => vcons (f y) (vmap f ys)
  end.

Definition vlength (A : Type) (n : peano) (xs : vector A n) : peano := n.

Lemma vmap_vlength : forall A B (n : peano) (f : A -> B) (xs : vector A n),
    vlength xs = vlength (vmap f xs).
Proof.
  reflexivity.
Qed.