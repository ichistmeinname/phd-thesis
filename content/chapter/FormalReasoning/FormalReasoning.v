Set Implicit Arguments.
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

Module General.

Fail Inductive List (M : Type -> Type) (A : Type) :=
| nil : List M A
| cons : M A -> M (List M A) -> List M A.

End General.

Fail Inductive NonStrictlyPos :=
| con : (NonStrictlyPos -> nat) -> NonStrictlyPos.

Inductive StrictlyPos :=
| con : StrictlyPos -> (nat -> StrictlyPos) -> StrictlyPos.

Fail Definition applyFun (t : NonStrictlyPos) : nat :=
  match t with
  | con f => f t
  end.