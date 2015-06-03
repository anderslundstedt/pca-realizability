(**
* A vector library
I am probably more or less reinventing the wheel here,
but I found the standard library's vector implementations
([Coq.Vectors.*])
insufficient for two reasons.
The first reason is that
vectors are defined as separate inductive types,
instead of as functions to [Type],
with which a lot would come for free by computation
and with which induction proofs would be easier.
The second reason is that
all functions are defined under the interpretation that
vectors are built by appending a vector to an element.
For my purposes the reverse interpretation---that
vectors are built by appending an element to a vector---is
more suitable.
*)

Require Import Coq.Classes.Morphisms.

Require Import fin.

Import FIN.NOTATIONS.
Local Open Scope FIN.

Module VEC.

  (**
  ** Definition
  For each type [A],
  there is one [A]-vector of length [0]---the empty vector---and
  the type of [A]-vectors of length [S n] is
  the product of the type of [A]-vectors of length [n] and [A].
  *)

  Inductive Empty (A : Type) := empty.
  Arguments empty {_}.

  Fixpoint t A (n : nat) : Type :=
  match n with
  | O   => Empty A
  | S n => prod (t A n) A
  end.
  Local Notation "()" := (empty : t _ 0).
  Local Infix ";;" :=
    ((fun A n (v : t A n) (a : A) => ((v, a) : t A (S n))) _ _)
    (at level 40, left associativity).

  (**
  ** Accessing elements of a vector
  *)

  Fixpoint nth {A} {n} : t A n -> FIN.t n -> A :=
  match n with
  | O   => fun _ x => False_rect _ (FIN.t0Empty x)
  | S n => fun v x => let (v, a) := v in
                      match x with
                      | inl x => nth v x
                      | inr _ => a
                      end
  end.

  (**
  ** Equality is pointwise equality
  *)

  Lemma pointwiseEquality {A} {n} (v w : t A n) :
    v = w <-> (forall x : FIN.t n, nth v x = nth w x).
  Proof.
    split; [intro; subst; tauto | ].
    intro H.
    induction n as [ | n IHn].
    - destruct v, w. reflexivity.
    - destruct v as [v a], w as [w b].
      specialize (IHn v w).
      pose proof (H FIN.last) as H'. simpl in H'. rewrite H'. clear H'.
      lapply IHn; [intro; subst; tauto | ]. clear IHn.
      intro x. exact (H ++x).
  Qed.

  (**
  ** Vectors of copies of an element
  *)

  Fixpoint copies {A} (n : nat) (a : A) : t A n :=
  match n with
  | O   => ()
  | S n => (copies n a, a)
  end.

  Lemma nthCopiesEq {A} {n} (a : A) (x : FIN.t n) : nth (copies n a) x = a.
  Proof.
    induction n as [ | n IHn]; simpl.
    - inversion x.
    - destruct x as [x | x].
      + apply IHn.
      + reflexivity.
  Qed.

  (**
  ** Concatenation of vectors
  *)

  Fixpoint concat {A} {n m} (v : t A n) : t A m -> t A (m + n) :=
  match m with
  | O   => fun _ => v
  | S m => fun w => let (w, a) := w in (concat v w, a)
  end.

  (**
  ** Mapping functions on vectors
  The map of
  [f : A -> B]
  over an [A]-vector
  [((), a1, a2, .., an)]
  is the [B]-vector
  [((), f a1, f a2, ..., f an)].
  *)

  Fixpoint map {A B} {n} (f : A -> B) : t A n -> t B n :=
  match n with
  | O   => fun _ => ()
  | S n => fun v => let (v, a) := v in (map f v, f a)
  end.

  Lemma mapRespectful {A B} {n} (f g : A -> B) (v : t A n) :
    (forall a : A, f a = g a) -> map f v = map g v.
  Proof.
    intro H.
    induction n as [ | n IHn].
    - reflexivity.
    - destruct v as [v a]. simpl. rewrite IHn, H. reflexivity.
  Qed.

  Instance mapProper {A B} {n} :
    Proper ((fun f g => forall a : A, f a = g a) ==> eq ==> eq) (@map A B n).
  Proof. intros f g Hfg v w Hvw. subst. apply mapRespectful. exact Hfg. Qed.

  Lemma mapComposeEq {A B C} {n} (f : A -> B) (g : B -> C) (v : t A n) :
    map g (map f v) = map (fun a => g (f a)) v.
  Proof.
    induction n as [ | n IHn].
    - reflexivity.
    - destruct v as [v a]. simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma nthMapEq {A B} {n} (f : A -> B) (v : t A n) (x : FIN.t n) :
    nth (map f v) x = f (nth v x).
  Proof.
    induction n as [ | n IHn].
    - inversion x.
    - destruct v as [v a]. destruct x as [x | x].
      + apply IHn.
      + reflexivity.
  Qed.

  Lemma mapConcatEq {A B} {n m} (f : A -> B) (v : VEC.t A n) (w : VEC.t A m) :
    map f (concat v w) = concat (map f v) (map f w).
  Proof.
    induction m as [ | m IHm]; simpl.
    - reflexivity.
    - destruct w as [w a]. rewrite IHm. reflexivity.
  Qed.

  (**
  ** Vectors as the image of functions on the canonically finite sets
  *)

  Fixpoint finMap {A} {n} : (FIN.t n -> A) -> t A n :=
  match n with
  | O   => fun _ => ()
  | S n => fun f => (finMap (fun x => f ++x), f FIN.last)
  end.

  Lemma nthFinMapEq {A} {n} (f : FIN.t n -> A) (x : FIN.t n) :
    VEC.nth (finMap f) x = f x.
  Proof.
    induction n as [ | n IHn].
    - inversion x.
    - destruct x as [x | x]; simpl.
      + rewrite IHn. reflexivity.
      + destruct x. reflexivity.
  Qed.

  Lemma finMapComposeEq {A B} {n} (f : FIN.t n -> A) (g : A -> B) :
    map g (finMap f) = finMap (fun x => g (f x)).
  Proof.
    induction n as [ | n IHn].
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Definition finMap' {A} {n k} (f : FIN.t (k + n) -> A) : t A n :=
    finMap (fun x => f (FIN.up' x)).

  Lemma nthFinMapEq' {A} {n k} (f : FIN.t (k + n) -> A) (x : FIN.t n) :
    VEC.nth (finMap' f) x = f (FIN.up' x).
  Proof. unfold finMap'. rewrite nthFinMapEq. reflexivity. Qed.

  Lemma finMapComposeEq' {A B} {n k} (f : FIN.t (k+n) -> A) (g : A -> B) :
    map g (finMap' f) = finMap' (fun x => g (f x)).
  Proof. unfold finMap'. apply finMapComposeEq. Qed.

  (**
  ** Left fold
  *)

  Fixpoint foldl {A} {n} (f : A -> A -> A) : A -> t A n -> A :=
  match n with
  | O   => fun a _ => a
  | S n => fun a v => let (v, b) := v in f (foldl f a v) b
  end.

  Lemma foldlConcatEq {A} {n m} (f : A -> A -> A) (a : A) (v : t A n)
                      (w : t A m) :
    foldl f a (concat v w) = foldl f (foldl f a v) w.
  Proof.
    induction m as [ | m IHm]; simpl.
    - reflexivity.
    - destruct w as [w b]. rewrite IHm. reflexivity.
  Qed.

  (**
  ** Notations
  *)

  Module NOTATIONS.
    Delimit Scope VEC with VEC.
    Notation "()" := () : VEC.
    Infix ";;" := (fun v a => v;; a) (at level 40, left associativity) : VEC.
  End NOTATIONS.

End VEC.
