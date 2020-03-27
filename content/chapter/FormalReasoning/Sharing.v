Require Import Equality.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Module Free.

  Fail Inductive Free F A :=
  | pure   : A -> Free F A
  | impure : F (Free F A) -> Free F A.

  Inductive Free (Shape : Type) (Pos : Shape -> Type) A :=
  | pure   : A -> Free Pos A
  | impure : forall s, (Pos s -> Free Pos A) -> Free Pos A.

  Arguments Free : clear implicits.
  Arguments pure {_} {_} {_}.
  Arguments impure {_} {_} {_}.

  Section ForFree.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.
    Variable A : Type.
    Variable P : A -> Prop.

    Inductive ForFree : Free Sh Ps A -> Prop :=
    | forPure   : forall x   , P x -> ForFree (pure x)
    | forImpure : forall s pf, (forall p, ForFree (pf p)) -> ForFree (impure s pf).

    Inductive InFree (x : A) : Free Sh Ps A -> Prop :=
    | inPure   : InFree x (pure x)
    | inImpure : forall s pf, (exists p, InFree x (pf p)) -> InFree x (impure s pf).

    Lemma ForFree_forall :
      forall (fx : Free Sh Ps A),
        ForFree fx <-> (forall (x : A), InFree x fx -> P x).
    Proof.
      intros fx.
      split.
      - intros HFree x HIn.
        induction HFree; dependent destruction HIn.
        + apply H.
        + destruct H1 as [p HIn].
          specialize (H0 p).
          apply H0.
          apply HIn.
      - intros HxIn.
        induction fx as [ x | s pf]; simpl.
        + apply forPure. apply HxIn. apply inPure.
        + apply forImpure. intros p. apply H. intros x Hin.
          apply HxIn. apply inImpure. exists p. apply Hin.
    Qed.

  End ForFree.

  Arguments forPure {_} {_} {_}.
  Arguments forImpure {_} {_} {_} {_} {_} {_}.

  Section Args.
      
    Variable Shape : Type.
    Variable Pos : Shape -> Type.

    Definition free_bind A B (f : A -> Free Shape Pos B) (fx : Free Shape Pos A)
      : Free Shape Pos B :=
      let fix free_bind' fx :=
          match fx with
          | pure x      => f x
          | impure s pf => impure s (fun p => free_bind' (pf p))
          end
      in free_bind' fx.

  End Args.

  Global Notation "fx >>= f" := (free_bind f fx) (at level 40, left associativity).

  Section bind_lemmas.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.

    Lemma ForFree_bind :
      forall A B (fx : Free Sh Ps A) (f: A -> Free Sh Ps B) (g: A -> Free Sh Ps B),
        ForFree (fun x => f x = g x) fx -> fx >>= f = fx >>= g.
    Proof.
      intros A B fx f g HFor.
      induction HFor; simpl.
      - apply H.
      - repeat apply f_equal.
        extensionality x. apply H0.
    Qed.

  End bind_lemmas.

End Free.

