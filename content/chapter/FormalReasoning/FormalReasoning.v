Set Implicit Arguments.
Require Import List.
Print hd_error.
Search (forall a, _ -> list a -> a).
Print hd.
Check head.

Fail Definition exampleList (A : Type) : list A := cons (head (nil : list A)) nil.

Inductive List (A : Type) :=
| nil_ : List A
| cons_ : option A -> option (List A) -> List A.

Arguments nil_ {_}.

Definition Nil (A : Type) : option (List A) :=
  Some nil_.
Definition Cons (A : Type) (ox : option A) (oxs : option (List A))
  : option (List A) :=
  Some (cons_ ox oxs).

Definition head (A : Type) (oxs : option (List A)) : option A :=
  match oxs with
  | None    => None
  | Some xs => match xs with
              | nil_       => None
              | cons_ ox _ => ox
              end
  end.

Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs} : option (List A) :=
  match oxs with
  | None    => None
  | Some xs => match xs with
              | nil_         => oys
              | cons_ oz ozs => Cons oz (append ozs oys)
              end
  end.

Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs} : option (List A) :=
  match oxs with
  | None    => None
  | Some xs =>
    let fix append' xs oys :=
        match xs with
        | nil_         => oys
        | cons_ oz ozs => Cons oz (append ozs oys)
        end
    in append' xs oys
  end.

Definition append_ (A : Type) (oxs oys : option (List A)) : option (List A) :=
  match oxs with
  | None    => None
  | Some xs =>
    let fix append' xs oys :=
        match xs with
        | nil_         => oys
        | cons_ oz ozs => Cons oz (match ozs with
                                  | None => None
                                  | Some zs => append' zs oys
                                  end)
        end
    in append' xs oys
  end.


Fixpoint append' (A : Type) (xs : List A) (oys : option (List A)) : option (List A) :=
  match xs with
  | nil_         => oys
  | cons_ oz ozs => Cons oz (match ozs with
                            | None    => None
                            | Some zs => append' zs oys
                            end)
  end.

Definition append (A : Type) (oxs oys : option (List A)) : option (List A) :=
  match oxs with
  | None    => None
  | Some xs => append' xs oys
  end.