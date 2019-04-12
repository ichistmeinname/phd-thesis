Set Implicit Arguments.

Require Import FunctionalExtensionality.

(* Require Import List. *)

(* Fail Definition exampleList (A : Type) : list A := cons (head (nil : list A)) nil. *)

Module Option.

  Inductive List (A : Type) :=
  | nil : List A
  | cons : option A -> option (List A) -> List A.
  
  Arguments nil {_}.
  
  Definition Nil (A : Type) : option (List A) :=
    Some nil.
  Definition Cons (A : Type) (ox : option A) (oxs : option (List A))
    : option (List A) :=
    Some (cons ox oxs).
  
  Definition head (A : Type) (oxs : option (List A)) : option A :=
    match oxs with
    | None    => None
    | Some xs => match xs with
                | nil       => None
                | cons ox _ => ox
                end
    end.
  
  Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs} : option (List A) :=
    match oxs with
    | None    => None
    | Some xs => match xs with
                | nil         => oys
                | cons oz ozs => Cons oz (append ozs oys)
                end
    end.
  
  Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs} : option (List A) :=
    match oxs with
    | None    => None
    | Some xs =>
      let fix append' xs oys :=
          match xs with
          | nil         => oys
          | cons oz ozs => Cons oz (append ozs oys)
          end
      in append' xs oys
    end.
  
  Definition append_ (A : Type) (oxs oys : option (List A)) : option (List A) :=
    match oxs with
    | None    => None
    | Some xs =>
      let fix append' xs oys :=
          match xs with
          | nil         => oys
          | cons oz ozs => Cons oz (match ozs with
                                    | None => None
                                    | Some zs => append' zs oys
                                    end)
          end
      in append' xs oys
    end.
  
  
  
  
  Fixpoint append' (A : Type) (xs : List A) (oys : option (List A)) : option (List A) :=
    match xs with
    | nil         => oys
    | cons oz ozs => Cons oz (match ozs with
                              | None    => None
                              | Some zs => append' zs oys
                              end)
    end.
  
  Definition append (A : Type) (oxs oys : option (List A)) : option (List A) :=
    match oxs with
    | None    => None
    | Some xs => append' xs oys
    end.

End Option.

Module Partial.

Inductive partial (A : Type) :=
| undefined : partial A
| defined   :  A -> partial A.

Arguments undefined {_}.

Inductive List (A : Type) :=
| nil  : List A
| cons : partial A -> partial (List A) -> List A.

Arguments nil {_}.

Definition Nil (A : Type) : partial (List A) :=
  defined nil.
Definition Cons (A : Type) (ox : partial A) (oxs : partial (List A))
  : partial (List A) :=
  defined (cons ox oxs).

Definition head (A : Type) (oxs : partial (List A)) : partial A :=
  match oxs with
  | undefined  => undefined
  | defined xs => match xs with
                 | nil       => undefined
                 | cons ox _ => ox
                 end
  end.

Fail Fixpoint append (A : Type) (oxs oys : partial (List A)) {struct oxs} : partial (List A) :=
  match oxs with
  | undefined  => undefined
  | defined xs => match xs with
                 | nil         => oys
                 | cons oz ozs => Cons oz (append ozs oys)
                 end
  end.

Fail Fixpoint append (A : Type) (oxs oys : partial (List A)) {struct oxs} : partial (List A) :=
  match oxs with
  | undefined  => undefined
  | defined xs =>
    let fix append' xs oys :=
        match xs with
        | nil         => oys
        | cons oz ozs => Cons oz (append ozs oys)
        end
    in append' xs oys
  end.

Definition append_ (A : Type) (oxs oys : partial (List A)) : partial (List A) :=
  match oxs with
  | undefined  => undefined
  | defined xs =>
    let fix append' xs oys :=
        match xs with
        | nil         => oys
        | cons oz ozs => Cons oz (match ozs with
                                  | undefined => undefined
                                  | defined zs => append' zs oys
                                  end)
        end
    in append' xs oys
  end.

Fixpoint append' (A : Type) (xs : List A) (oys : partial (List A)) : partial (List A) :=
  match xs with
  | nil         => oys
  | cons oz ozs => Cons oz (match ozs with
                            | undefined    => undefined
                            | defined zs => append' zs oys
                            end)
  end.

Definition append (A : Type) (oxs oys : partial (List A)) : partial (List A) :=
  match oxs with
  | undefined  => undefined
  | defined xs => append' xs oys
  end.

End Partial.

Module Total.

Inductive total (A : Type) :=
| totality : A -> total A.

End Total.

Module GenericList.

Fail Inductive List (M : Type -> Type) (A : Type) :=
| nil : List M A
| cons : M A -> M (List M A) -> List M A.

End GenericList.

Fail Inductive NonStrictlyPos :=
| con : (NonStrictlyPos -> nat) -> NonStrictlyPos.

Inductive StrictlyPos :=
| con : StrictlyPos -> (nat -> StrictlyPos) -> StrictlyPos.

Fail Definition applyFun (t : NonStrictlyPos) : nat :=
  match t with
  | con f => f t
  end.

Fail Inductive Mu A :=
| mu : (Mu A -> A) -> Mu A.

Definition Cont R A := (A -> R) -> R.

Fail Inductive ListCont R A :=
| nilC  : ListCont R A
| consC : ((A -> R) -> R) -> ((ListCont R A -> R) -> R) -> ListCont R A.

Module SigmaUniverse.

  Variable U : Type.
  Variable El : U -> Type.

  Inductive ExtSigma :=
  | extsigma : forall (a : U), ((El a -> U) -> U) -> ExtSigma.

End SigmaUniverse.
Module General.

  Inductive General (S : Type) (T : S -> Type) A :=
  | res : A -> General T A
  | req : forall s, (T s -> General T A) -> General T A.

  Arguments res {_} {_} {_}.

  Fixpoint foldG {S T X Y} (r : X -> Y) (c : forall s, (T s -> Y) -> Y) (g : @General S T X) : Y :=
    match g with
    | res x => r x
    | req s k => c s (fun t => foldG r c (k t))
    end.

  Notation "g >>= k" := (foldG k (fun s f => req s f) g) (at level 50, left associativity).

  Definition call {S T} (s : S) : General T (T s) :=
    req s (fun x => res x).

  Definition PiG (S : Type) (T : S -> Type) :=
    forall (s : S), General T (T s).

  Inductive Nat :=
  | zero : Nat
  | suc  : Nat -> Nat.

  Fail Fixpoint fusc (n : Nat) : Nat :=
    match n with
    | zero  => zero
    | suc n => suc (fusc (fusc n))
    end.
  
  Definition fusc : @PiG Nat (fun _ => Nat) :=
    fun n =>
      match n with
      | zero  => res zero
      | suc n => call n >>= fun fn => call fn >>= fun ffn => res (suc ffn)
      end.

  Compute (fusc zero).
  Compute (fusc (suc zero)).
  Compute (fusc (suc (suc zero))).
  
End General.
  
Module Free.

Fail Inductive Free F A :=
| pure   : A -> Free F A
| impure : F (Free F A) -> Free F A.

Inductive Ext (Shape : Type) (Pos : Shape -> Type) A :=
| ext : forall s, (Pos s -> A) -> Ext Pos A.

Arguments Ext Shape Pos A : clear implicits.
Arguments ext {_} {_} {_}.

Inductive Free (Shape : Type) (Pos : Shape -> Type) A :=
| pure   : A -> Free Pos A
| impure : Ext Shape Pos A -> Free Pos A.

Arguments Free : clear implicits.

Arguments pure {_} {_} {_}.

Inductive One (A : Type) :=
| one : One A.

Arguments one {_}.

Definition One__S := unit.
Inductive Empty : Type := .
Definition One__P (s : One__S) := Empty.

Definition from_One A (o : One A) : Ext One__S One__P A :=
  ext tt (fun (p : One__P tt) => match p with end).

Definition to_One A (e : Ext One__S One__P A) : One A :=
  one.

Arguments from_One / _ _ .
Arguments to_One / _ _.

Lemma from_to_One : forall (A : Type) (e : Ext One__S One__P A),
    from_One (to_One e) = e.
Proof.
  intros A e.
  destruct e as [[] pf]; simpl.
  f_equal. extensionality p. destruct p.
Qed.

Lemma to_from_One : forall (A : Type) (o : One A),
    to_One (from_One o) = o.
Proof.
  intros A o.
  destruct o; reflexivity.
Qed.

Import Partial.

Definition to_partial A (fx : Free One__S One__P A) : partial A :=
  match fx with
  | pure x   => defined x
  | impure e => undefined
  end.

Definition from_partial A (p : partial A) : Free One__S One__P A :=
  match p with
  | undefined => impure (from_One one)
  | defined x => pure x
  end.

Lemma from_to_partial : forall (A : Type) (fx : Free One__S One__P A),
    from_partial (to_partial fx) = fx.
Proof.
  intros A fx.
  destruct fx as [x | [[] pf]]; simpl.
  - reflexivity.
  - do 2 f_equal. extensionality p. destruct p.
Qed.

Lemma to_from_partial : forall (A : Type) (p : partial A),
    to_partial (from_partial p) = p.
Proof.
  intros A p.
  destruct p; reflexivity.
Qed.

Inductive Zero (A : Type) := .

Definition Zero__S := Empty.
Definition Zero__P (s : Zero__S) := Empty.

Definition from_Zero A (u : Zero A) : Ext Zero__S Zero__P A :=
  match u with end.

Definition to_Zero A (e : Ext Zero__S Zero__P A) : Zero A :=
  match e with
  | ext s pf => match s with end
  end.

Arguments from_Zero / _ _ .
Arguments to_Zero / _ _.

Lemma from_to_Zero : forall (A : Type) (e : Ext Zero__S Zero__P A),
    from_Zero (to_Zero e) = e.
Proof.
  intros A e.
  destruct e as [[] pf].
Qed.

Lemma to_from_Zero : forall (A : Type) (z : Zero A),
    to_Zero (from_Zero z) = z.
Proof.
  intros A z.
  destruct z.
Qed.

Import Total.

Definition to_total A (fx : Free Zero__S Zero__P A) : total A :=
  match fx with
  | pure x   => totality x
  | impure (ext s _) => match s with end
  end.

Definition from_total A (t : total A) : Free Zero__S Zero__P A :=
  match t with
  | totality x => pure x
  end.

Lemma from_to_total : forall (A : Type) (fx : Free Zero__S Zero__P A),
    from_total (to_total fx) = fx.
Proof.
  intros A fx.
  destruct fx as [x | [[] pf]]; reflexivity.
Qed.

Lemma to_from_total : forall (A : Type) (t : total A),
    to_total (from_total t) = t.
Proof.
  intros A t.
  destruct t; reflexivity.
Qed.

End Free.