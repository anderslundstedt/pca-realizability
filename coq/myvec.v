Require Import Coq.Classes.Morphisms.

Module FIN.

  Inductive Singleton (n : nat) := lift :> Singleton n.

  Fixpoint t (n : nat) : Type := match n with
  | O   => Empty_set
  | S n => sum (t n) (Singleton n)
  end.

  Definition last {n} : t (S n) := inr (lift n).

  Definition up {n} (x : t n) : t (S n) := inl x.
  Local Notation "++ x" := (up x) (at level 6, right associativity).

  Fixpoint up' {n k} (x : t n) : t (k+n) := match k with
  | O   => x
  | S k => ++(up' x)
  end.


  Definition ofNat (n k : nat) : t (k + S n) := up' last.

  Lemma t0Empty (x : t 0) : False.
  Proof. destruct x. Qed.

  Lemma t1Singleton (x : t 1) : x = last.
  Proof. destruct x as [x | x]; destruct x. reflexivity. Qed.

  Fixpoint toNat {n} : t (S n) -> nat := match n with
  | O   => fun x => 0
  | S n => fun x => match x with
                    | inl x => toNat x
                    | inr x => n
                    end
  end.

  Module NOTATIONS.
    Delimit Scope FIN with FIN.
    Notation "++ x" := ++x (at level 6, right associativity) : FIN.
  End NOTATIONS.

End FIN.

Module VEC.

  Import FIN.NOTATIONS.
  Local Open Scope FIN.

  Fixpoint t A (n : nat) : Type := match n with
  | O   => unit
  | S n => prod (t A n) A
  end.

  Local Notation "()" := (tt : t _ 0).

  Local Infix ";;" :=
    ((fun A n (v : t A n) (a : A) => ((v, a) : t A (S n))) _ _)
    (at level 40, left associativity).

  Fixpoint nth {A} {n} : t A n -> FIN.t n -> A := match n with
  | O   => fun _ x => False_rect _ (FIN.t0Empty x)
  | S n => fun v x => let (v, a) := v in match x with
                      | inl x => nth v x
                      | inr _ => a
                      end
  end.

  Lemma pointwiseEquality {A} {n} (v w : t A n) :
    (forall x : FIN.t n, nth v x = nth w x) <-> v = w.
  Proof.
    split; [ | intro; subst; tauto].
    intro H.
    induction n as [ | n IHn].
    - destruct v, w. reflexivity.
    - destruct v as [v a], w as [w b].
      specialize (IHn v w).
      pose proof (H FIN.last) as H'. simpl in H'. rewrite H'. clear H'.
      lapply IHn; [intro; subst; tauto | ]. clear IHn.
      intro x. exact (H (++x)).
  Qed.

  Lemma uniqueEmptyVector {A} (v : t A 0) : v = tt.
  Proof. destruct v. reflexivity. Qed.

  Fixpoint map {A B} {n} (f : A -> B) : t A n -> t B n := match n with
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

  Lemma mapCompose {A B C} {n} (f : A -> B) (g : B -> C) (v : t A n) :
    map g (map f v) = map (fun a => g (f a)) v.
  Proof.
    induction n as [ | n IHn].
    - reflexivity.
    - destruct v as [v a]. simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma mapNth {A B} {n} (f : A -> B) (v : t A n) (x : FIN.t n) :
    nth (map f v) x = f (nth v x).
  Proof.
    induction n as [ | n IHn].
    - inversion x.
    - destruct v as [v a]. destruct x as [x | x].
      + apply IHn.
      + reflexivity.
  Qed.

  Fixpoint finMap {A} {n} : (FIN.t n -> A) -> t A n := match n with
  | O   => fun _ => ()
  | S n => fun f => (finMap (fun x => f ++x);; f FIN.last)
  end.

  Lemma finMapNth {A} {n} (f : FIN.t n -> A) (x : FIN.t n) :
    VEC.nth (finMap f) x = f x.
  Proof.
    induction n as [ | n IHn].
    - inversion x.
    - destruct x as [x | x]; simpl.
      + rewrite IHn. reflexivity.
      + destruct x. reflexivity.
  Qed.

  Lemma finMapCompose {A B} {n} (f : FIN.t n -> A) (g : A -> B) :
    map g (finMap f) = finMap (fun x => g (f x)).
  Proof.
    induction n as [ | n IHn].
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Definition finMap' {A} {n k} (f : FIN.t (k+n) -> A) : t A n :=
    finMap (fun x => f (FIN.up' x)).

  Lemma finMapNth' {A} {n k} (f : FIN.t (k+n) -> A) (x : FIN.t n) :
    VEC.nth (finMap' f) x = f (FIN.up' x).
  Proof.
    destruct n as [ | n].
    - inversion x.
    - destruct x as [x | x]; simpl.
      + rewrite finMapNth. reflexivity.
      + destruct x. reflexivity.
  Qed.

  Lemma finMapCompose' {A B} {n k} (f : FIN.t (k+n) -> A) (g : A -> B) :
    map g (finMap' f) = finMap' (fun x => g (f x)).
  Proof. unfold finMap'. apply finMapCompose. Qed.

  Definition init {A} {n} (v : t A (S n)) : t A n := let (v, _) := v in v.

  Definition last {A} {n} (v : t A (S n)) : A := let (_, a) := v in a.

  Lemma initLastEq {A} {n} (v : t A (S n)) : v = (init v, last v).
  Proof. destruct v as [v a]. reflexivity. Qed.

  Fixpoint concat {A} {n m} (v : t A n) : t A m -> t A (m+n) :=
  match m with
  | O   => fun _ => v
  | S m => fun w => let (w, a) := w in (concat v w, a)
  end.

  Lemma concatMap {A B} {n m} (f : A -> B) (v : VEC.t A n) (w : VEC.t A m) :
    map f (concat v w) = concat (map f v) (map f w).
  Proof.
    induction m as [ | m IHm]; simpl.
    - reflexivity.
    - destruct w as [w a]. rewrite IHm. reflexivity.
  Qed.

  Fixpoint head {A} {n} : t A (S n) -> A := match n with
  | O   => fun v => let (_, a) := v in a
  | S n => fun v => let (v, _) := v in head v
  end.

  Fixpoint tail {A} {n} : t A (S n) -> t A n := match n with
  | O   => fun _ => tt
  | S n => fun v => let (v, a) := v in (tail v, a)
  end.

  Fixpoint foldL {A} {n} (f : A -> A -> A) : A -> t A n -> A := match n with
  | O   => fun a _ => a
  | S n => fun a v => let (v, b) := v in f (foldL f a v) b
  end.

  Fixpoint foldR {A} {n} (f : A -> A -> A) : A -> t A n -> A := match n with
  | O   => fun b _ => b
  | S n => fun b v => let (v, a) := v in foldR f (f a b) v
  end.

  Lemma concatFoldLEq {A} {n m} (f : A -> A -> A) (a : A) (v : t A n)
                      (w : t A m) :
    foldL f a (concat v w) = foldL f (foldL f a v) w.
  Proof.
    induction m as [ | m IHm]; simpl.
    - reflexivity.
    - destruct w as [w b]. rewrite IHm. reflexivity.
  Qed.

  Fixpoint copies {A} (n : nat) (a : A) : t A n := match n with
  | O   => ()
  | S n => (copies n a, a)
  end.

  Lemma nthCopies {A} {n} (a : A) (x : FIN.t n) : nth (copies n a) x = a.
  Proof.
    induction n as [ | n IHn]; simpl.
    - inversion x.
    - destruct x as [x | x].
      + apply IHn.
      + reflexivity.
  Qed.

  Module NOTATIONS.
    Delimit Scope VEC with VEC.
    Notation "()" := () : VEC.
    Infix ";;" := (fun v a => v;; a) (at level 40, left associativity) : VEC.
  End NOTATIONS.

End VEC.
