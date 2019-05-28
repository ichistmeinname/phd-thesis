Set Implicit Arguments.

Require Import FunctionalExtensionality.
Require Import Equality.
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
  
  Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs}
    : option (List A) :=
    match oxs with
    | None    => None
    | Some xs => match xs with
                | nil         => oys
                | cons oz ozs => Cons oz (append ozs oys)
                end
    end.
  
  Fail Fixpoint append (A : Type) (oxs oys : option (List A)) {struct oxs}
    : option (List A) :=
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
  
  Definition append_ (A : Type) (oxs oys : option (List A))
    : option (List A) :=
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
  
  
  
  
  Fixpoint append' (A : Type) (xs : List A) (oys : option (List A))
    : option (List A) :=
    match xs with
    | nil         => oys
    | cons oz ozs => Cons oz (match ozs with
                              | None    => None
                              | Some zs => append' zs oys
                              end)
    end.
  
  Definition append (A : Type) (oxs oys : option (List A))
    : option (List A) :=
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

  Fail Fixpoint append (A : Type) (oxs oys : partial (List A)) {struct oxs}
    : partial (List A) :=
    match oxs with
    | undefined  => undefined
    | defined xs => match xs with
                   | nil         => oys
                   | cons oz ozs => Cons oz (append ozs oys)
                   end
    end.

  Fail Fixpoint append (A : Type) (oxs oys : partial (List A)) {struct oxs}
    : partial (List A) :=
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

  Definition append_ (A : Type) (oxs oys : partial (List A))
    : partial (List A) :=
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

  Fixpoint append' (A : Type) (xs : List A) (oys : partial (List A))
    : partial (List A) :=
    match xs with
    | nil         => oys
    | cons oz ozs => Cons oz (match ozs with
                             | undefined    => undefined
                             | defined zs => append' zs oys
                             end)
    end.

  Definition append (A : Type) (oxs oys : partial (List A))
    : partial (List A) :=
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

Module StrictPos.

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

End StrictPos.
  
Module SigmaUniverse.

  Section ExtSigma.

    Variable U : Type.
    Variable El : U -> Type.

    Inductive ExtSigma :=
    | extsigma : forall (a : U), ((El a -> U) -> U) -> ExtSigma.

  End ExtSigma.

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

  (* Compute (fusc zero). *)
  (* Compute (fusc (suc zero)). *)
  (* Compute (fusc (suc (suc zero))). *)
  
End General.
  
Module Container.

  Inductive Ext (Shape : Type) (Pos : Shape -> Type) A :=
  | ext : forall s, (Pos s -> A) -> Ext Pos A.

  Arguments Ext Shape Pos A : clear implicits.
  Arguments ext {_} {_} {_}.

End Container.

Module Free.

  Fail Inductive Free F A :=
  | pure   : A -> Free F A
  | impure : F (Free F A) -> Free F A.

  Export Container.

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

  Module withSection.

    Section Args.
      
      Variable Shape : Type.
      Variable Pos : Shape -> Type.

      Section free_bind.

        Variable A B : Type.
        Variable f : A -> Free Shape Pos B.

        Fixpoint free_bind (fx : Free Shape Pos A) : Free Shape Pos B :=
          match fx with
          | pure x => f x
          | impure s pf => impure s (fun p => free_bind (pf p))
          end.

      End free_bind.

    End Args.

  End withSection.
  Module withLocal.

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

  End withLocal.

  Import withLocal.
  
  Notation "fx >>= f" := (free_bind f fx) (at level 40, left associativity).

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

Inductive Empty : Type := .

Module Partiality.

  Import Container.

  Inductive One (A : Type) :=
  | one : One A.

  Arguments one {_}.

  Definition One__S := unit.
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
  Import Free.

  Definition to_partial A (fx : Free One__S One__P A) : partial A :=
    match fx with
    | pure x     => defined x
    | impure _ _ => undefined
    end.

  Definition from_partial A (p : partial A) : Free One__S One__P A :=
    match p with
    | undefined => let '(ext s pf) := from_One one in impure s pf
    | defined x => pure x
    end.

  Lemma from_to_partial : forall (A : Type) (fx : Free One__S One__P A),
      from_partial (to_partial fx) = fx.
  Proof.
    intros A fx.
    destruct fx as [x | [] pf]; simpl.
    - reflexivity.
    - do 2 f_equal. extensionality p. destruct p.
  Qed.

  Lemma to_from_partial : forall (A : Type) (p : partial A),
      to_partial (from_partial p) = p.
  Proof.
    intros A p.
    destruct p; reflexivity.
  Qed.

End Partiality.

Module Totality.

  Import Container.

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
  Import Free.

  Definition to_total A (fx : Free Zero__S Zero__P A) : total A :=
    match fx with
    | pure x   => totality x
    | impure s _ => match s with end
    end.

  Definition from_total A (t : total A) : Free Zero__S Zero__P A :=
    match t with
    | totality x => pure x
    end.

  Lemma from_to_total : forall (A : Type) (fx : Free Zero__S Zero__P A),
      from_total (to_total fx) = fx.
  Proof.
    intros A fx.
    destruct fx as [x | [] pf]; reflexivity.
  Qed.

  Lemma to_from_total : forall (A : Type) (t : total A),
      to_total (from_total t) = t.
  Proof.
    intros A t.
    destruct t; reflexivity.
  Qed.

End Totality.

Module FreeList.

  Import Free.

  Unset Elimination Schemes.
  Inductive List (Shape : Type) (Pos : Shape -> Type) A :=
  | nil : List Pos A
  | cons : Free Shape Pos A -> Free Shape Pos (List Pos A) -> List Pos A.
  Set Elimination Schemes.

  Arguments List Shape Pos A : clear implicits.
  Arguments nil {_} {_} {_}.

  Notation Nil := (pure nil).
  Notation Cons fx fxs := (pure (cons fx fxs)).

  Section List_ind.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.
    Variable A : Type.
    Variable P : List Sh Ps A -> Prop.

    Hypothesis nilP : P nil.
    Hypothesis consP : forall fx fxs, ForFree P fxs -> P (cons fx fxs).

    Fixpoint List_ind' (xs : List Sh Ps A) : P xs.
      destruct xs as [ | fy fys ].
      - apply nilP.
      - apply consP.
        induction fys as [ ys | s pf IH ].
        + apply forPure.
          apply List_ind'.
        + apply forImpure.
          apply IH.
    Defined.
    
    Fixpoint List_ind (xs : List Sh Ps A) : P xs :=
      match xs with
      | nil         => nilP
      | cons fy fys =>
        consP fy (let fix free_ind (fxs : Free Sh Ps (List Sh Ps A)) : ForFree P fxs :=
                      match fxs with
                      | pure xs => forPure P xs (List_ind xs)
                      | impure s pf => forImpure (fun p => free_ind (pf p))
                      end in free_ind fys)
      end.

  End List_ind.


  Section append.

    Variable S : Type.
    Variable P : S -> Type.

    Fail Fixpoint append' A (xs : List S P A) (fys : Free S P (List S P A)) :=
      match xs with
      | nil => fys
      | cons fz fzs => Cons fz (match fzs with
                               | pure zs     => append' zs fys
                               | impure s pf => _ (* what to do here? *)
                               end)
      end.

    Fixpoint free_bind A B (fx : Free S P A) (f : A -> Free S P B) : Free S P B :=
      match fx with
      | pure x      => f x
      | impure s pf => impure s (fun p => free_bind (pf p) f)
      end.

    Fail Fixpoint append' A (xs : List S P A) (fys : Free S P (List S P A)) {struct xs}:=
      match xs with
      | nil => fys
      | cons fz fzs => Cons fz (free_bind fzs (fun zs => append' zs fys))
      end.

    Fixpoint append' A (xs : List S P A) (fys : Free S P (List S P A)) :=
      match xs with
      | nil => fys
      | cons fz fzs => Cons fz (fzs >>= fun zs => append' zs fys)
      end.

    Definition append A (fxs fys : Free S P (List S P A)) : Free S P (List S P A) :=
      fxs >>= fun xs => append' xs fys.

  End append.

  Notation "xs +++ ys" := (append xs ys) (at level 40, left associativity).

  Section Utilities.

    Variable S : Type.
    Variable P : S -> Type.

    Definition singleton A (fx : Free S P A) : Free S P (List S P A) :=
      Cons fx Nil.

  End Utilities.    

End FreeList.

Module rose_map.

  Inductive List A :=
  | Nil  : List A
  | Cons : A -> List A -> List A.
  Arguments Nil {_}.

  Inductive Rose A :=
  | Leaf     : A -> Rose A
  | Branches : List (Rose A) -> Rose A.

  Module wo_section.

    Fixpoint map A B (f : A -> B) (xs : List A) : List B :=
      match xs with
      | Nil       => Nil
      | Cons x xs => Cons (f x) (map f xs)
      end.

    Fail Fixpoint mapRose A B (f : A -> B) (r : Rose A) {struct r} : Rose B :=
      match r with
      | Leaf x      => Leaf (f x)
      | Branches rs => Branches (map (fun x => mapRose f x) rs)
      end.

  End wo_section.

  Module w_section.

    Section map.

      Variable A B : Type.
      Variable f : A -> B.
    
      Fixpoint map (xs : List A) : List B :=
        match xs with
        | Nil       => Nil
        | Cons x xs => Cons (f x) (map xs)
        end.

    End map.

    Fixpoint mapRose A B (f : A -> B) (r : Rose A) : Rose B :=
      match r with
      | Leaf x      => Leaf (f x)
      | Branches rs => Branches (map (mapRose f) rs)
      end.

  End w_section.

  Module local_fix.

    Definition map A B (f : A -> B) (xs : List A) : List B :=
      let fix map' xs :=
          match xs with
          | Nil       => Nil
          | Cons x xs => Cons (f x) (map' xs)
          end in
      map' xs.

    Fixpoint mapRose A B (f : A -> B) (r : Rose A) : Rose B :=
      match r with
      | Leaf x      => Leaf (f x)
      | Branches rs => Branches (map (mapRose f) rs)
      end.

  End local_fix.

End rose_map.

Module LtacGoodies.

  Import Free.

  Ltac simplifyInductionHypothesis ident1 ident2 :=
    match goal with
    | [ ident1 : ForFree ?P (pure _) |- _ ] => inversion ident1 as [ Heq ident2 |]; clear ident1; subst; simpl
    | [ ident1 : ForFree ?P (impure ?s ?pf) |- _ ] =>
      dependent destruction ident1;
      match goal with
      | [ H1 : forall p : ?T, ForFree ?P (?pf p), H0 : forall p, ForFree ?P (?pf p) -> _ = _,
            p : ?T |- _ ] =>
        specialize (H0 p (H1 p)) as ident2; clear H1; clear H0; simpl
      end
    end.

  Tactic Notation "simplify" ident(H) "as" ident(IH) := (simplifyInductionHypothesis H IH).

  Ltac rewriteBindInductionHypothesis ident1 :=
    match goal with
    | [ ident1 : ForFree ?P ?fx |- _ ] => apply ForFree_bind in ident1
    end.

  Tactic Notation "simplBind" ident(H) := (rewriteBindInductionHypothesis H).

  Ltac autoInductionHypothesis :=
    match goal with
    | [ H : ForFree ?P (impure ?s ?pf) |- ?h ?s ?pf1 = ?h ?s ?pf2 ] =>
      f_equal; let x := fresh in extensionality x; simplify H as Hnew; assumption
      (*   try apply newH) *)
    | [ H : ForFree ?P (pure ?x) |- _ ] =>
      let newH := fresh in simplify H as newH; rename newH into IH
    | [ H : forall p : ?T, ?f = ?g |- ?h ?s ?pf1 = ?h ?s ?pf2 ] =>
      f_equal; let x := fresh in extensionality x; apply H
    end.

  Tactic Notation "autoIH" := (autoInductionHypothesis).

  Tactic Notation "inductFree" ident(fx) "as" simple_intropattern(pat) := (induction fx as pat; simpl; try autoIH).

  Import FreeList.

  Ltac inductionFreeCons :=
    match goal with
    | [ |- Cons ?fx (?fxs >>= ?g1) = Cons ?fx ?g2 ] => do 2 f_equal; try inductionFreeCons
    | [ |- (?fxs >>= ?f) = ?f1 (?fxs >>= ?g) ] => inductFree fxs as [xs|]; simpl
    end.

  Tactic Notation "inductFreeList" ident(fxs) "as" simple_intropattern(pat) :=
    (induction fxs as [xs|]; simpl; try autoIH; try induction xs as pat; simpl; try inductionFreeCons).

End LtacGoodies.
  

Module append_assoc.

  Import Free.
  Import FreeList.

  Import Totality.
  Import Partiality.

  Import LtacGoodies.

  (* Require Import Setoid. *)

  Lemma append_assoc_total :
    forall (A : Type) (fxs fys fzs : Free Zero__S Zero__P (List Zero__S Zero__P A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    intros A fxs fys fzs.
    destruct fxs as [ xs | s pf ]; simpl.
    (* fxs = pure xs *)
    - induction xs as [ | fx fxs IH ]; simpl.
      (* xs = nil *)
      + reflexivity.
      (* xs = cons fx fxs; induction hypothesis IH *)
      + do 2 f_equal.
        destruct IH as [ xs H | s pf ]; simpl.
        * rewrite H. reflexivity.
        * contradiction.
    (* fxs = impure s pf *)
    - contradiction.
  Qed.

  Lemma append_assoc_partial :
    forall (A : Type) (fxs fys fzs : Free One__S One__P (List One__S One__P A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    intros A fxs fys fzs.
    destruct fxs as [ xs | [] pf ]; simpl.
    - induction xs as [ | fx fxs IH ]; simpl.
      + reflexivity.
      + do 2 f_equal.
        destruct IH as [ xs H | [] pf ]; simpl.
        * rewrite H. reflexivity.
        * do 2 f_equal. extensionality p.
          contradiction.
    - do 2 f_equal. extensionality p.
      contradiction.
  Qed.

  Lemma append_assoc_generic :
    forall (Sh : Type) (Ps : Sh -> Type) (A : Type)
      (fxs fys fzs : Free Sh Ps (List Sh Ps A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    intros Sh Ps A fxs fys fzs.
    induction fxs as [ xs | s pf IH ]; simpl.
    - (* fxs = pure xs *) induction xs as [ | fx fxs IH ]; simpl.
      + (* xs = nil *) reflexivity.
      + (* xs = cons fx fxs *) do 2 f_equal.
        induction IH as [ xs H | s pf _ IH' ]; simpl.
        * (* fxs = pure xs *) rewrite H. reflexivity.
        * (* fxs = impure s pf *) do 2 f_equal. extensionality p.
          apply IH'.
    - (* fxs = impure s pf *) do 2 f_equal. extensionality p.
      apply IH.
  Qed.

  Lemma append_assoc_total' :
    forall (A : Type) (fxs fys fzs : Free Zero__S Zero__P (List Zero__S Zero__P A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    apply append_assoc_generic.
  Qed.

  Lemma append_assoc_partial' :
    forall (A : Type) (fxs fys fzs : Free One__S One__P (List One__S One__P A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    apply append_assoc_generic.
  Qed.

  Lemma append_assoc_generic_simplified :
    forall (Sh : Type) (Ps : Sh -> Type) (A : Type) (fxs fys fzs : Free Sh Ps (List Sh Ps A)),
      append fxs (append fys fzs) = append (append fxs fys) fzs.
  Proof.
    intros Sh Ps A fxs fys fzs.
    inductFree fxs as [xs |].
    induction xs as [ | fx fxs IH ]; simpl.
    - reflexivity.
    - do 2 f_equal.
      inductFree fxs as [xs |].
      apply IH.
  Qed.
  
End append_assoc.


Module list_properties.

  Import Free.
  Import FreeList.

  Import LtacGoodies.

  Section Definitions.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.

    Fixpoint map' A B (f : Free Sh Ps A -> Free Sh Ps B) (xs : List Sh Ps A)
      : Free Sh Ps (List Sh Ps B) :=
      match xs with
      | nil         => Nil
      | cons fx fxs => Cons (f fx) (fxs >>= fun xs => map' f xs)
      end.

    Definition map A B (f : Free Sh Ps A -> Free Sh Ps B) (fxs : Free Sh Ps (List Sh Ps A))
      : Free Sh Ps (List Sh Ps B) :=
      fxs >>= fun xs => map' f xs.

  End Definitions.

  Section Properties.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.

    Lemma map_id : forall (A : Type) (fxs : Free Sh Ps (List Sh Ps A)),
        map (fun fx => fx) fxs = fxs.
    Proof.
      intros A fxs.
      inductFree fxs as [xs |]; simpl.
      induction xs as [ | fx fxs IH]; simpl.
      + reflexivity.
      + do 2 f_equal.
        inductFree fxs as [xs |].
        apply IH.
    Qed.

    Lemma map_compose : forall (A B C : Type)
                          (f : Free Sh Ps A -> Free Sh Ps B)
                          (g : Free Sh Ps B -> Free Sh Ps C)
                          (fxs : Free Sh Ps (List Sh Ps A)),
        map (fun fx => g (f fx)) fxs = map g (map f fxs).
    Proof.
      intros A B C f g fxs.
      inductFree fxs as [xs |]; simpl.
      induction xs as [ | fx fxs IH]; simpl.
      + reflexivity.
      + do 2 f_equal.
        inductFree fxs as [xs |].
        apply IH.
    Qed.

    Lemma map_compose' : forall (A B C : Type)
                           (f : Free Sh Ps A -> Free Sh Ps B)
                           (g : Free Sh Ps B -> Free Sh Ps C)
                           (fxs : Free Sh Ps (List Sh Ps A)),
        map (fun fx => g (f fx)) fxs = map g (map f fxs).
    Proof.
      intros A B C f g fxs.
      inductFreeList fxs as [| fx fxs IH]; simpl.
      + reflexivity.
      + apply IH.
    Qed.

    Lemma append_assoc_generic' :
      forall (A : Type) (fxs fys fzs : Free Sh Ps (List Sh Ps A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros A fxs fys fzs.
      inductFreeList fxs as [ | fx fxs IH ]; simpl.
      - reflexivity.
      - apply IH.
    Qed.

  End Properties.

End list_properties.

Module Primitives.

  Import Free.

  Section Definitions.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.

    Definition TTrue  : Free Sh Ps bool := pure true.
    Definition FFalse : Free Sh Ps bool := pure false.

    Definition liftM1 A R (f : A -> R) (x : Free Sh Ps A) : Free Sh Ps R :=
      x >>= fun x' => pure (f x').
    Definition liftM2 A B R (f : A -> B -> R) (x : Free Sh Ps A) (y : Free Sh Ps B) : Free Sh Ps R :=
      x >>= fun x' => y >>= fun y' => pure (f x' y').
    Definition liftM3 A B C R (f : A -> B -> C -> R) (x : Free Sh Ps A) (y : Free Sh Ps B) (z : Free Sh Ps C) : Free Sh Ps R :=
      x >>= fun x' => y >>= fun y' => z >>= fun z' => pure (f x' y' z').

  End Definitions.

  Arguments TTrue {_} {_}.
  Arguments FFalse {_} {_}.

End Primitives.

Module Razor.

  Import Free.
  Import Primitives.
  Import FreeList.

  Import LtacGoodies.

  Section Polymorphic_Definitions.

    Variable Sh : Type.
    Variable Ps : Sh -> Type.

    Unset Elimination Schemes.
    Inductive Expr :=
    | val : Free Sh Ps nat -> Expr
    | add : Free Sh Ps Expr -> Free Sh Ps Expr -> Expr.
    Set Elimination Schemes.

    Section Expr_ind.

      Variable P : Expr -> Prop.

      Hypothesis valP : forall fn, P (val fn).
      Hypothesis addP : forall fe1 fe2, ForFree P fe1 -> ForFree P fe2 -> P (add fe1 fe2).

      Fixpoint Expr_ind (e : Expr) : P e :=
        match e with
        | val fn => valP fn
        | add fe1 fe2 =>
          let fix free_ind (fe : Free Sh Ps Expr) : ForFree P fe :=
              match fe with
              | pure e      => forPure P e (Expr_ind e)
              | impure s pf => forImpure (fun p => free_ind (pf p))
              end in
          addP (free_ind fe1) (free_ind fe2)
        end.

    End Expr_ind.

    Definition Val (fn : Free Sh Ps nat) : Free Sh Ps Expr :=
      pure (val fn).

    Definition Add (fe1 fe2 : Free Sh Ps Expr) : Free Sh Ps Expr :=
      pure (add fe1 fe2).

    Fixpoint eval' (e : Expr) : Free Sh Ps nat :=
      match e with
      | val fn    => fn
      | add fx fy => liftM2 plus (fx >>= eval') (fy >>= eval')
      end.

    Definition eval (fe : Free Sh Ps Expr) : Free Sh Ps nat :=
      fe >>= eval'.

    Definition Stack := List Sh Ps nat.

    Unset Elimination Schemes.
    Inductive Op :=
    | push_ : Free Sh Ps nat -> Op
    | add_  : Op.
    Set Elimination Schemes.

    Section Op_ind.

      Variable P : Op -> Prop.

      Hypothesis add_P : P add_.
      Hypothesis push_P : forall fn, P (push_ fn).

      Fixpoint Op_ind (op : Op) : P op :=
        match op with
        | add_ => add_P
        | push_ fn => push_P fn
        end.

    End Op_ind.

    Definition PUSH (fn : Free Sh Ps nat) : Free Sh Ps Op :=
      pure (push_ fn).

    Definition ADD : Free Sh Ps Op :=
      pure add_.

    Definition Code := List Sh Ps Op.

    Fixpoint comp' (e : Expr) : Free Sh Ps Code :=
      match e with
      | val fn    => singleton (PUSH fn)
      | add fx fy => append (fx >>= comp') (append (fy >>= comp') (singleton ADD))
      end.

    Definition comp (fe : Free Sh Ps Expr) : Free Sh Ps Code :=
      fe >>= comp'.

  End Polymorphic_Definitions.

  Arguments add_ {_} {_}.
  Import Partiality.

  Section Partial_Definitions.

    Definition undefined (A : Type) : Free One__S One__P A :=
      let '(ext s pf) := from_One one in impure s pf.

    Definition FreeP := Free One__S One__P.
    Definition StackP := Stack One__P.
    Definition CodeP  := Code One__P.
    
    Fixpoint exec' (fs : FreeP StackP) (c : CodeP) : FreeP StackP :=
      match c with
      | nil          => fs
      | cons fc fops => fc >>= fun c =>
          match c with
          | push_ fn => fops >>= exec' (Cons fn fs)
          | add_     => fs >>= fun s =>
              match s with
              | nil => @undefined StackP
              | cons fn fxs => fxs >>= fun xs =>
                  match xs with
                  | nil => @undefined StackP
                  | cons fm fs' => fops >>= exec' (Cons (liftM2 plus fm fn) fs')
                  end
              end
          end
      end.

    Definition exec (fs : FreeP StackP) (fc : FreeP CodeP) : FreeP StackP :=
      fc >>= exec' fs.

    (* Fixpoint exec2' (s : StackP) (fc : FreeP CodeP) : FreeP StackP := *)
    (*   let help fc fs := fc >>= fun c => match c with *)
    (*                                 | nil          => fs *)
    (*                                 | cons fc fops => fc >>= fun c1 => *)
    (*                                                           match c1 with *)
    (*                                                           | push_ fn => fops >>= exec' (Cons fn fs) *)
    (*                                                           | add_     => @undefined StackP *)
    (*                                                           end *)
    (*                                 end in *)
    (*   match s with *)
    (*   | nil => help fc Nil *)
    (*   | cons fn fxs => *)
    (*     fxs >>= fun xs => *)
    (*               match xs with *)
    (*               | nil => help fc (Cons fn Nil) *)
    (*               | cons fm fs' => *)
    (*                 fc >>= fun c => match c with *)
    (*                              | nil          => Cons fn (Cons fm fs') *)
    (*                              | cons fc fops => *)
    (*                                fc >>= fun c1 => match c1 with *)
    (*                                              | push_ fn =>fops >>= exec' (Cons fn (Cons fn (Cons fm fs'))) *)
    (*                                              | add_     => fops >>= exec' (Cons (liftM2 plus fm fn) fs') *)
    (*                                              end *)
    (*                              end *)
    (*               end *)
    (*   end. *)

    Fixpoint exec2' (s : StackP) (c : CodeP) : FreeP StackP :=
      match c with
      | nil          => pure s
      | cons fc fops => fc >>= fun c =>
          match c with
          | push_ fn => fops >>= exec2' (cons fn (pure s))
          | add_     => match s with
                       | nil => @undefined StackP
                       | cons fn fxs => fxs >>= fun xs =>
                                                 match xs with
                                                 | nil => @undefined StackP
                                                 | cons fm fs' => fops >>= exec' (Cons (liftM2 plus fm fn) fs')
                                                 end
                       end
          end
      end.
    
    Definition exec2 (fs : FreeP StackP) (fc : FreeP CodeP) : FreeP StackP :=
      fc >>= fun c => fs >>= fun s => exec2' s c.

  End Partial_Definitions.

  Section Propositions.

    Inductive ListEffectFree (Sh : Type) (Ps : Sh -> Type) (A : Type) (P__A : Free Sh Ps A -> Prop)
      : Free Sh Ps (List Sh Ps A) -> Prop :=
    | free_nil : ListEffectFree P__A (pure nil)
    | free_cons : forall fx fxs, P__A fx -> ListEffectFree P__A fxs -> ListEffectFree P__A (pure (cons fx fxs)).
    
    Lemma append_effectFree :
      forall (A : Type) (Sh : Type) (Ps : Sh -> Type) (P__A : Free Sh Ps A -> Prop)
        (fxs fys : Free Sh Ps (List Sh Ps A)),
        ListEffectFree P__A fxs -> ListEffectFree P__A fys -> ListEffectFree P__A (fxs +++ fys).
    Proof.
      intros A Sh Ps P__A fxs fys Hxs Hys.
      inductFree Hxs as [ | fz fzs IH ]; eauto; try econstructor; try assumption.
    Qed.

    Lemma append_effectFree_and :
      forall (A : Type) (Sh : Type) (Ps : Sh -> Type) (P__A : Free Sh Ps A -> Prop)
        (fxs fys : Free Sh Ps (List Sh Ps A)),
        ListEffectFree P__A (fxs +++ fys) ->
        ListEffectFree P__A fxs /\ ListEffectFree P__A fys.
    Proof.
      intros A Sh Ps P__A fxs fys Hfree.
      split.
      - inductFree fxs as [ xs | fz fzs IH ].
        + induction xs as [ | fx fxs IH ];
            try econstructor; simpl in *;
              inversion Hfree; clear Hfree; subst;
                try assumption.
          induction IH; simpl in *.
          * apply H. apply H2.
          * inversion H2.
        + inversion Hfree.
      - inductFree fxs as [ xs | fz fzs IH ].
        + induction xs as [ | fx fxs IH ]; try assumption.
          induction IH; simpl in *; inversion Hfree; clear Hfree; subst.
          * apply H. apply H3.
          * inversion H4.
        + inversion Hfree.
    Qed.

    Inductive OpEffectFree (Sh : Type) (Ps : Sh -> Type) : Free Sh Ps (Op Ps) -> Prop :=
    | free_push_ : forall fn, OpEffectFree (pure (push_ fn))
    | free_add_ : OpEffectFree (pure add_).

    Inductive ExpEffectFree (Sh : Type) (Ps : Sh -> Type)
      : Free Sh Ps (Expr Ps) -> Prop :=
    | free_val : forall fx, ExpEffectFree (pure (val fx))
    | free_add : forall fx fy, ExpEffectFree fx -> ExpEffectFree fy ->
                          ExpEffectFree (pure (add fx fy)).

    Definition IdProp {A : Type} (x : A) : Prop := True.

    Lemma elemProp_to_idProp :
      forall (A : Type) (Sh : Type) (Ps : Sh -> Type) (P__A : Free Sh Ps A -> Prop)
        (fxs : Free Sh Ps (List Sh Ps A)),
        ListEffectFree P__A fxs -> ListEffectFree IdProp fxs.
    Proof.
      intros A Sh Ps P__A fxs Hfree.
      inductFree Hfree as [ | fz fzs IH ]; eauto;
        try econstructor; try assumption; try constructor.
    Qed.

    Axiom exec_strict : forall fxs, exec (@undefined StackP) fxs = (@undefined StackP).

    Ltac find_pure_effectfree :=
      match goal with
      | [ Hcons4 : ListEffectFree ?P2 (?Cons ?xs) |- ListEffectFree ?P2 (Cons _ ?xs) ] =>
        inversion Hcons4 as [| ? ? Hhead Htail]; subst; clear Hcons4;
        try constructor; try (apply Htail); try constructor; try assumption
      | [ Hcons3 : ListEffectFree ?P2 ?xs |- ListEffectFree ?P2 (Cons ?x ?xs) ] =>
        try constructor; try (apply Hcons3); try constructor; try assumption
      | [ Hcons2 : ListEffectFree ?P2 (Cons _ (pure ?xs)) |- ListEffectFree ?P2 (pure ?xs) ] =>
        inversion Hcons2 as [| ? ? Hhead Htail]; clear Hcons2; subst;
        apply Htail
      | [ Hcons1 : ?P1 ?P2 (Cons (pure ?x) _) |- ?P2 (pure ?x) ] =>
        inversion Hcons1 as [| ? ? Hhead Htail]; clear Hcons1; subst;
        apply Hhead
      | [ Hexp : ExpEffectFree ?arg |- ?P (pure ?x) ] => inversion Hexp; subst; try assumption
      end.

    Ltac inversion_impure :=
      match goal with
      | [ Himp   : context [ ?f (impure _ _) ] |- _ ] => inversion Himp; subst; inversion_impure
      end.

    Lemma exec_distr :
      forall fxs,
        ListEffectFree (@OpEffectFree One__S One__P) fxs ->
        forall fys,
          ListEffectFree IdProp fys ->
          forall fs,
            ListEffectFree IdProp fs ->
            exec fs (fxs +++ fys) = exec (exec fs fxs) fys.
    Proof with (simpl; try inversion_impure).
      inductFree fxs as [ xs | [] pf IH ]; intros HxsFree...
      induction xs as [ | fx fxs IH ]; simpl.
      - reflexivity.
      - intros fys HysFree fs HfsFree.
        inductFree fx as [ x | [] pf IH2]...
        + destruct x; simpl.
          * inductFree IH as [ xs IH | [] pf IH ]...
            fold (exec (Cons f fs) (append' xs fys)).
            rewrite IH; try reflexivity; try assumption;
              find_pure_effectfree.
          * inductFree fs as [ st | [] pf IH2 ]...
            induction st as [ | fs fsts IH2 ]; simpl.
            -- rewrite exec_strict; reflexivity.
            -- inductFree IH2 as [sts IH2 | s pf IH2]...
               destruct sts; simpl.
               ++ apply IH2; find_pure_effectfree.
               ++ inductFree fxs as [ xs | s pf IH3 ]...
                  fold (exec (Cons (liftM2 Nat.add f fs) f0) (append' xs fys)).
                  rewrite IH; try reflexivity; try assumption;
                    try find_pure_effectfree; try (repeat constructor).
                    inversion HxsFree; inversion HfsFree; try assumption;
                      inversion H6; try constructor; try assumption.
    Qed.

    (* `fe` needs to be pure;
        restrictions on `fs` and `comp fe` come from the usage of `exec_distr` *)
    Lemma correctness : forall fe fs,
        ExpEffectFree fe ->
        ListEffectFree IdProp fs ->
        ListEffectFree (@OpEffectFree One__S One__P) (comp fe) ->
        exec fs (comp fe) = Cons (eval fe) fs.
    Proof with (simpl; try inversion_impure).
      intros fe.
      inductFree fe as [exp | s pf IH]; intros fs Hfe Hfs Hcomp...
      generalize dependent fs.
      induction exp as [ fn | fx fy ]; simpl.
        + reflexivity.
        + intros fs Hfs.
          apply append_effectFree_and in Hcomp;
            destruct Hcomp as [ Hfx Hrest ].
          rewrite exec_distr; try assumption; try (apply elemProp_to_idProp in Hrest; assumption).
          inductFree fx as [ x | s pf IHx ]...
          rewrite IH; try assumption; try constructor; try find_pure_effectfree.
          -- clear IH.
             apply append_effectFree_and in Hrest;
               destruct Hrest as [ Hfy Hsingle ].
             rewrite exec_distr; repeat (try constructor; try assumption).
             fold (comp fy).
             inductFree fy as [ y | s pf IHy ]...
             rewrite IH; try reflexivity; try assumption; try find_pure_effectfree.
    Qed.

    Lemma exec_singleton : forall fe,
        ExpEffectFree fe ->
        ListEffectFree (@OpEffectFree One__S One__P) (comp fe) ->
        exec Nil (comp fe) = singleton (eval fe).
    Proof.
      intros fe Hfe HfreeList.
      apply correctness; try assumption; try constructor.
    Qed.

  End Propositions.

End Razor.

Section InductionPrinciple.

  (* nat_ind : forall P : nat -> Prop, *)
  (*   P 0 -> *)
  (*   (forall n : nat, P n -> P (S n)) -> *)
  (*   forall n : nat, P n *)

  Fixpoint even (n : nat) : bool :=
    match n with
    | 0   => true
    | S 0 => false
    | S (S n) => even n
    end.

  Definition double (n : nat) : nat :=
    n * 2.

  Lemma even_double : forall (n : nat),
      even (double n) = true.
  Proof.
    intros n.
    induction n as [ | n' IH ]; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma even_double' : forall (n : nat),
      even (double n) = true.
  Proof.
    apply nat_ind.
    - reflexivity.
    - intros n IH. apply IH.
  Qed.

End InductionPrinciple.

Module Tree.

  Inductive tree (A : Type) :=
  | empty  : tree A
  | leaf   : A -> tree A
  | branch : tree A -> tree A -> tree A.

  Arguments empty {_}.

End Tree.    

Module Nondeterminism.

  Import Container.

  Inductive ND (A : Type) :=
  | choice : A -> A -> ND A
  | failed : ND A.

  Arguments failed {_}.

  Definition ND__S := bool.
  Definition ND__P (s : ND__S) :=
    match s with
    | true  => bool
    | false => Empty
    end.

  Definition from_ND A (nd : ND A) : Ext ND__S ND__P A :=
    match nd with
    | choice x y => ext true (fun (p : ND__P true) => if p then x else y)
    | failed     => ext false (fun (p : ND__P false) => match p with end)
    end.

  Definition to_ND A (e : Ext ND__S ND__P A) : ND A :=
    match e with
    | ext true  pf => choice (pf true) (pf false)
    | ext false pf => failed
    end.

  Arguments from_ND / _ _ .
  Arguments to_ND / _ _.

  Lemma from_to_ND : forall (A : Type) (e : Ext ND__S ND__P A),
      from_ND (to_ND e) = e.
  Proof.
    intros A e.
    destruct e as [s pf]; simpl.
    dependent destruction s; simpl.
    - f_equal; extensionality p; destruct p;
      reflexivity.
    - f_equal; extensionality p; destruct p.
  Qed.

  Lemma to_from_ND : forall (A : Type) (nd : ND A),
      to_ND (from_ND nd) = nd.
  Proof.
    intros A nd.
    destruct nd; reflexivity.
  Qed.

  Import Tree.
  Import Free.

  Fixpoint to_tree A (fx : Free ND__S ND__P A) : tree A :=
    match fx with
    | pure x          => leaf x
    | impure true  pf => branch (to_tree (pf true)) (to_tree (pf false))
    | impure false pf => empty
    end.

  Fixpoint from_tree A (t : tree A) : Free ND__S ND__P A :=
    match t with
    | empty        => let '(ext s pf) := from_ND failed in impure s pf
    | leaf x       => pure x
    | branch t1 t2 => let '(ext s pf) := from_ND (choice (from_tree t1) (from_tree t2)) in impure s pf
    end.

  Lemma from_to_tree : forall (A : Type) (fx : Free ND__S ND__P A),
      from_tree (to_tree fx) = fx.
  Proof.
    intros A fx.
    induction fx as [x | s pf]; simpl;
      try reflexivity.
    dependent destruction s; simpl;
      do 2 f_equal; extensionality p; destruct p;
        apply H.
  Qed.

  Lemma to_from_tree : forall (A : Type) (t : tree A),
      to_tree (from_tree t) = t.
  Proof.
    intros A t.
    induction t as [ | x | t1 IHt1 t2 IHt2 ]; simpl;
      try rewrite IHt1, IHt2; reflexivity.
  Qed.

End Nondeterminism.

Module ND_Examples.

  Import LtacGoodies.
  Import Nondeterminism.
  Import Free.
  Import FreeList.
  Import Primitives.

  Definition FreeND := Free ND__S ND__P.
  Definition ListND := List ND__S ND__P.

  Definition Failed (A : Type) : FreeND A := impure false (fun (p : ND__P false) => match p with end).
  Notation "x ? y" := (impure true (fun (p : ND__P true) => if p then x else y)) (at level 28, right associativity).

  Arguments Failed {_}.
  
  Definition coin : FreeND bool :=
    TTrue ? FFalse.

  Definition oneOrTwo : FreeND nat :=
    pure 1 ? pure 2.
  
  Section Generic.

    Variable Sh : Type.
    Variable Pos : Sh -> Type.
    Definition Free' := Free Sh Pos.
    Definition List' := List Sh Pos.

    Fixpoint insert' (fx : Free' nat) (xs : List' nat) : Free' (List' nat) :=
      match xs with
      | nil         => Cons fx Nil
      | cons fy fys => fx >>= fun x => fy >>= fun y =>
                                            if Nat.leb x y
                                            then Cons (pure x) (Cons (pure y) fys)
                                            else Cons (pure y) (fys >>= fun ys => insert' fx ys)
      end.
    
    Definition insert (fx : Free' nat) (fxs : Free' (List' nat)) : Free' (List' nat) :=
      fxs >>= fun xs => insert' fx xs.

    Fixpoint sort' (xs : List' nat) : Free' (List' nat) :=
      match xs with
      | nil => Nil
      | cons fx fxs => insert fx (fxs >>= sort')
      end.

    Definition sort (fxs : Free' (List' nat)) : Free' (List' nat) :=
      fxs >>= sort'.

    Fixpoint length' (A : Type) (xs : List' A) : Free' nat :=
      match xs with
      | nil        => pure 0
      | cons _ fxs => liftM1 (fun n => S n) (fxs >>= fun xs => length' xs)
      end.

    Definition length (A : Type) (fxs : Free' (List' A)) : Free' nat :=
      fxs >>= fun xs => length' xs.

    Fixpoint replicate' (A : Type) (n : nat) (fx : Free' A) : Free' (List' A) :=
      match n with
      | 0   => Nil
      | S n => Cons fx (replicate' n fx)
      end.

    Definition replicate (A : Type) (fn : Free' nat) (fx : Free' A) : Free' (List' A) :=
      fn >>= fun n => replicate' n fx.

    Definition even (fn : Free' nat) : Free' bool :=
      liftM1 Nat.even fn.

    Definition inc (fn : Free' nat) : Free' nat :=
      liftM1 (fun n => S n) fn.

    Section Normalform.

      Variable A : Type.
      Variable nfA : Free' A -> Free' A.

      Fixpoint nfList' (xs : List' A) : Free' (List' A) :=
        match xs with
        | nil         => Nil
        | cons fx fxs => nfA fx >>= fun x' => fxs >>= fun xs => nfList' xs >>= fun xs' => Cons (pure x') (pure xs')
        end.

      Definition nfList (fxs : Free' (List' A)) : Free' (List' A) :=
        fxs >>= nfList'.

      Definition nfNat (fn : Free' nat) : Free' nat :=
        fn >>= fun n =>
                 match n with
                 | 0   => pure 0
                 | S n => pure (S n)
                 end.

    End Normalform.

  End Generic.


  Section ND_specific.

    Fixpoint ndInsert' (A : Type) (fx : FreeND A) (xs : ListND A)
      : FreeND (ListND A) :=
      match xs with
      | nil         => Cons fx Nil
      | cons fy fys => (Cons fx (Cons fy fys))
                    ? (Cons fy (fys >>= fun ys => ndInsert' fx ys))
      end.

    Definition ndInsert (A : Type) (fx : FreeND A) (fxs : FreeND (ListND A))
      : FreeND (ListND A) :=
      fxs >>= fun xs => ndInsert' fx xs.

    Fixpoint perm' (A : Type) (xs : ListND A) : FreeND (ListND A) :=
      match xs with
      | nil         => Nil
      | cons fx fxs => ndInsert fx (fxs >>= fun xs => perm' xs)
      end.

    Definition perm (A : Type) (fxs : FreeND (ListND A)) : FreeND (ListND A) :=
      fxs >>= fun xs => perm' xs.

    Fixpoint replicateND' (A : Type) (n : nat) (fx : FreeND A) : FreeND A :=
      match n with
      | 0   => fx
      | S n => fx ? (replicateND' n fx)
      end.

    Definition replicateND (A : Type) (fn : FreeND nat) (fx : FreeND A) : FreeND A :=
      fn >>= fun n => replicateND' n fx.


  End ND_specific.
  Section Examples.

    Lemma hInFreeNDCoin : InFreeND eq TTrue coin.
    Proof.
      repeat constructor.
    Qed.

    Import Primitives.
    Import ListEffectFree.

    Lemma even_coin' :
      even (liftM2 mult oneOrTwo (pure 2)) = TTrue ? TTrue.
    Proof.
      simpl.
      f_equal; extensionality p.
      destruct p; reflexivity.
    Qed.

    Lemma even_coin :
      even (liftM2 mult oneOrTwo (pure 2)) = TTrue ? TTrue.
    Proof.
      simpl even.
      f_equal; extensionality p.
      destruct p.
      + simpl liftM2.
        simpl even.
        reflexivity.
      + simpl liftM2.
        simpl even.
        reflexivity.
    Qed.

    Lemma even_coin_forFree :
      ForFree (fun b => b = true) (even (liftM2 mult oneOrTwo (pure 2))).
    Proof.
      simpl; constructor.
      intros p; destruct p; repeat constructor.
    Qed.

    Lemma even_coin_allND :
      AllND (fun fb => fb = TTrue) (even (liftM2 mult oneOrTwo (pure 2))).
    Proof.
      simpl; constructor.
      intros p; destruct p; repeat constructor.
    Qed.

    Lemma pulltab_inc :
      forall (fx fy : FreeND nat),
        inc (fx ? fy) = inc fx ? inc fy.
    Proof with (simpl).
      intros fx fy...
      f_equal; extensionality p.
      destruct p; reflexivity.
    Qed.
      
    Lemma pulltab_f_strict :
      forall (A B : Type) (f : FreeND A -> FreeND B) (fx fy : FreeND A),
        (forall fz, f fz = fz >>= fun z => f (pure z)) ->
        f (fx ? fy) = f fx ? f fy.
    Proof with (simpl).
      intros A B f fx fy Hstrict.
      rewrite (Hstrict (fx ? fy))...
      f_equal; extensionality p.
      destruct p; rewrite Hstrict; reflexivity.
    Qed.

    Lemma length_Cons : forall (fx : FreeND nat) fxs,
        length (Cons fx fxs) = liftM1 (fun n => S n) (length fxs).
    Proof.
      intros fx fxs.
      inductFree fxs as [xs |].
      induction xs; reflexivity.
    Qed.

    Lemma ndInsert_inc :
      AllND (fun fxs => length fxs = pure 3)
            (ndInsert (pure 1) (Cons (pure 1) (Cons (pure 2) Nil))).
    Proof.
      simpl. apply forImpure.
      intros p; destruct p.
      - apply forPure. reflexivity.
      - apply forPure.
        rewrite length_Cons.
        rewrite pulltab_f_strict
          with (f := fun fx => liftM1 (fun n => S n) (length fx)); simpl.
          * admit.
          * intros fxs; inductFree fxs as [ xs| ]; reflexivity.
    Abort.
    
    Lemma ndInsert_inc :
      AllND (fun fxs => length fxs = pure 3) (nfList (fun x => x) (ndInsert (pure 1) (Cons (pure 1) (Cons (pure 2) Nil)))).
    Proof with (simpl).
      simpl; constructor.
      intros p; destruct p...
      - constructor; reflexivity.
      - constructor...
        intros p; destruct p...
        + constructor; reflexivity.
        + constructor; reflexivity.
    Qed.

    Section CallTimeChoice.

      Section Definitions.

        Variable Sh : Type.
        Variable Ps : Sh -> Type.

        Definition and (fb1 fb2 : Free Sh Ps bool) : Free Sh Ps bool :=
          fb1 >>= fun b1 => match b1 with
                         | true  => fb2
                         | false => FFalse
                         end.

        Definition doublePlus (fx : Free Sh Ps nat) : Free Sh Ps nat :=
          liftM2 plus fx fx.

        Definition doubleMult (fx : Free Sh Ps nat) : Free Sh Ps nat :=
          liftM2 mult fx (pure 2).

      End Definitions.

      Section Propositions.

        Import Partiality.

        Definition Undefined (A : Type) : Free One__S One__P A :=
          impure tt (fun p : One__P tt => match p with end).

        Arguments Undefined / {_}.

        Lemma even_doubleMult_Undefined :
          even (doubleMult Undefined) = Undefined.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p.
        Qed.

        Lemma even_doublePlus_Undefined :
          even (doublePlus Undefined) = Undefined.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p.
        Qed.

        Lemma even_doubleMult_Failed :
          even (doubleMult Failed) = Failed.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p.
        Qed.

        Lemma even_doubleMult_Choice :
          even (doubleMult oneOrTwo) = TTrue ? TTrue.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p; reflexivity.
        Qed.

        Lemma even_doublePlus_Failed :
          even (doublePlus Failed) = Failed.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p.
        Qed.

        Lemma even_doublePlus_Choice :
          even (doublePlus oneOrTwo) = TTrue ? TTrue.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p.
          - (* even (pure 1 + oneOrTwo) = TTrue *)
            admit.
          - (* even (pure 2 + oneOrTwo) = TTrue *)
            admit.
        Abort.

        Lemma even_doublePlus_Choice :
          even (doublePlus oneOrTwo) = (TTrue ? FFalse) ? (FFalse ? TTrue).
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p; simpl.
          - f_equal; extensionality p.
            destruct p; reflexivity.
          - f_equal; extensionality p.
            destruct p; reflexivity.
        Qed.

        Lemma doublePlus_inline :
          doublePlus oneOrTwo = liftM2 plus oneOrTwo oneOrTwo.
        Proof.
          reflexivity.
        Qed.

        Lemma doubleMult_inline :
          doubleMult oneOrTwo = pure 2 ? pure 4.
        Proof.
          simpl. f_equal. extensionality p.
          destruct p; reflexivity.
        Qed.

        Definition doubleSharePos (fn : FreeND nat) : FreeND nat :=
          match fn with
          | pure _      => liftM2 plus fn fn
          | impure s pf => impure s (fun p => doublePlus (pf p))
          end.

        Lemma even_doubleSharePos_Choice :
          even (doubleSharePos oneOrTwo) = TTrue ? TTrue.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p; reflexivity.
        Qed.

        Definition shareStrict (A : Type) (fx : FreeND A) : FreeND (FreeND A) :=
          match fx with
          | pure x      => pure (pure x)
          | impure s pf => impure s (fun p => pure (pf p))
          end.

        Definition doubleShare (fn : FreeND nat) : FreeND nat :=
          shareStrict fn >>= fun fn' => doublePlus fn'.

        Lemma even_doubleShare_Choice :
          even (doubleShare oneOrTwo) = TTrue ? TTrue.
        Proof.
          simpl.
          f_equal; extensionality p.
          destruct p; reflexivity.
        Qed.

        Definition const2 (A B C: Type)
                   (fx : FreeND A) (fy : FreeND B) (fz : FreeND C) :=
          fx.
        (* const2 42 x x *)
        Definition example_with_const2 (A B : Type) (fx : FreeND A) (fy : FreeND B) :=
          shareStrict fy >>= fun fy' => const2 fx fy' fy'.

        Lemma share_with_const2 :
          forall (A : Type) (fx : FreeND A),
            example_with_const2 fx oneOrTwo = fx.
        Proof.
          intros A fx.
          unfold example_with_const2; simpl.
          (* const2 fx (pure 1) (pure 1) ? const2 fx (pure 2) (pure 2) = fx *)
          admit.
        Abort.

        Lemma share_with_const2 :
          forall (A : Type) (fx : FreeND A),
            example_with_const2 fx oneOrTwo = fx ? fx.
        Proof.
          intros A fx.
          unfold example_with_const2; simpl.
          f_equal; extensionality p; destruct p; reflexivity.
          (* const2 fx (pure 1) (pure 1) = fx *)
          (* const2 fx (pure 2) (pure 2) = fx *)
        Qed.
          
      End Propositions.

    End CallTimeChoice.

  End Examples.

End ND_Examples.