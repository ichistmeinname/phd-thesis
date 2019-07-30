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

Fail Fixpoint test (b : bool) (n m : peano) : bool :=
  match (n,m) with
  | (z,_)      => true
  | (_,z)      => false
  | (s p, s q) => if b then test b p m else test b n q
  end.


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

Inductive vmap_spec (A B : Type) (f : A -> B) :
  forall (n m : peano), vector A n -> vector B m -> Prop :=
| spec_nil  : vmap_spec f vnil vnil
| spec_cons : forall (n m : peano) (x : A) (y : B)
                (xs : vector A n) (ys : vector B m),
    vmap_spec f xs ys -> f x = y -> vmap_spec f (vcons x xs) (vcons y ys).

Lemma z_not_s : forall x, z = s x -> False.
Proof.
  intros x Heq.
  discriminate Heq.
Qed.

Lemma z_not_s2 : forall x, z <> s x.
Proof.
  intros x.
  unfold not.
  apply z_not_s.
Qed.

Lemma s_not_eq : forall (n m : peano), s n <> s m -> n <> m.
Proof.
  intros n m HnotS Hnot.
  destruct Hnot.
  contradiction.
Qed.

Lemma not_eq_s : forall (n m : peano), n <> m -> s n <> s m.
Proof.
  intros n m Hnot HnotS.
  injection HnotS; intros Heq; destruct Heq.
  contradiction.
Qed.

Section vmap_spec_proofs.

  Variable A B : Type.
  Variable n m : peano.
  Variable f : A -> B.
  Variable xs : vector A n.

  Lemma vmap_fulfils_spec : vmap_spec f xs (vmap f xs).
  Proof.
    induction xs as [ | n' y ys IHys ]; simpl.
    - apply spec_nil.
    - apply spec_cons.
      + apply IHys. apply ys.
      + reflexivity.
  Qed.

  Lemma vmap_different_length : forall (ys : vector B m),
      n <> m -> vmap_spec f xs ys -> False.
  Proof.
    intros ys Hnot Hspec.
    induction Hspec.
    - contradiction.
    - apply IHHspec.
      apply s_not_eq.
      apply Hnot.
  Qed.

  Lemma vmap_same_length : forall (ys : vector B m),
      vmap_spec f xs ys -> n = m.
  Proof.
    intros ys Hspec.
    induction Hspec.
    - reflexivity.
    - rewrite IHHspec; reflexivity.
  Qed.

  Lemma vmap_different_length_exists :
    n <> m -> (exists (ys : vector B m), vmap_spec f xs ys) -> False.
  Proof.
    intros Hnot Hexists.
    destruct Hexists as [ ys Hspec ].
    induction Hspec.
    - contradiction.
    - apply s_not_eq in Hnot.
      apply (IHHspec Hnot).
  Qed.

  Lemma vmap_same_length_exists :
    (exists (ys : vector B m), vmap_spec f xs ys) -> n = m.
  Proof.
    intros Hexists.
    destruct Hexists as [ ys Hspec ].
    induction Hspec.
    - reflexivity.
    - rewrite IHHspec; reflexivity.
  Qed.

End vmap_spec_proofs.