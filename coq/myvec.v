Require Import Coq.Classes.Morphisms.
Require Coq.Arith.Compare_dec.

Module FIN.

  Inductive Nat (n : nat) := lift :> Nat n.

  Fixpoint t (n : nat) : Type := match n with
  | O   => Empty_set
  | S n => sum (t n) (Nat n)
  end.

  Definition last {n} : t (S n) := inr (lift n).

  Definition up {n} (x : t n) : t (S n) := inl x.
  Local Notation "++ x" := (up x) (at level 6, right associativity).

  Fixpoint up' {n m} (x : t n) : t (m + n) := match m with
  | O   => x
  | S n => ++(up' x)
  end.

  Definition ofNatType (x n : nat) : Type :=
  match Compare_dec.le_lt_dec n x with
  | left  _ => n <= x
  | right _ => t n
  end.

  Definition ofNat (x n : nat) : ofNatType x n.
  Proof.
    induction n as [ | n IHn].
    - exact (Le.le_0_n x).
    - unfold ofNatType in *.
      destruct (Compare_dec.le_lt_dec n x) as [H | H].
      + destruct (Compare_dec.le_lt_dec (S n) x) as [H' | H'].
        * exact H'.
        * exact last.
      + destruct (Compare_dec.le_lt_dec (S n) x) as [H' | H'].
        * exfalso. apply (Lt.lt_not_le x n H). apply Le.le_Sn_le. exact H'.
        * exact ++IHn.
  Defined.

  Lemma t0Empty (x : t 0) : False.
  Proof. destruct x. Qed.

  Lemma t1Singleton (x : t 1) : x = last.
  Proof. destruct x as [x | x]; destruct x. reflexivity. Qed.

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
  | O   => fun _ => tt
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

  Definition init {A} {n} (v : t A (S n)) : t A n := let (v, _) := v in v.

  Definition last {A} {n} (v : t A (S n)) : A := let (_, a) := v in a.

  Lemma initLastEq {A} {n} (v : t A (S n)) : v = (init v, last v).
  Proof. destruct v as [v a]. reflexivity. Qed.

  Fixpoint concat {A} {n m} (v : t A n) : t A m -> t A (m + n) :=
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

Module FIN_VEC.

  Import FIN.NOTATIONS.
  Import VEC.NOTATIONS.
  Local Open Scope FIN.
  Local Open Scope VEC.

  Fixpoint t (n : nat) : VEC.t (FIN.t n) n := match n with
  | O   => ()
  | S n => (VEC.map FIN.up (t n);; FIN.last)
  end.

  Lemma nthEq (n : nat) (x : FIN.t n) : VEC.nth (t n) x = x.
  Proof.
    induction n as [ | n IHn].
    - inversion x.
    - destruct x as [x | x].
      + simpl. rewrite VEC.mapNth, IHn. reflexivity.
      + destruct x. reflexivity.
  Qed.

  Lemma nthMap {A} {n} (f : FIN.t n -> A) (x : FIN.t n) :
    VEC.nth (VEC.map f (t n)) x = f x.
  Proof. rewrite VEC.mapNth, nthEq. reflexivity. Qed.

  Fixpoint t' (n m : nat) : VEC.t (FIN.t (m + n)) n := match m with
  | O   => t n
  | S m => VEC.map FIN.up (t' n m)
  end.

  Lemma nthEq' (n m : nat) (x : FIN.t n) : VEC.nth (t' n m) x = FIN.up' x.
  Proof.
    induction m as [ | m IHm].
    - apply nthEq.
    - simpl. rewrite VEC.mapNth, IHm. reflexivity.
  Qed.

  Lemma nthMap' {A} {n m} (f : FIN.t (m + n) -> A) (x : FIN.t n) :
    VEC.nth (VEC.map f (t' n m)) x = f (FIN.up' x).
  Proof. rewrite VEC.mapNth, nthEq'. reflexivity. Qed.

End FIN_VEC.
