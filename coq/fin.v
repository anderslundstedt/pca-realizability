(**
* Canonical finite types
[FIN.t n] is a type with [n] members,
one member naturally corresponding to each [m < n].
*)

Module FIN.

  (**
  ** Definition
  [t 0] is the empty type.
  [t (S n)] is the sum of
  [t n] and the singleton of [n].
  *)

  Inductive Singleton (n : nat) := lift : Singleton n.

  Fixpoint t (n : nat) : Type :=
  match n with
  | O   => Empty_set
  | S n => sum (t n) (Singleton n)
  end.

  Definition last {n} : t (S n) := inr (lift n).

  Lemma t0Empty (x : t 0) : False.
  Proof. destruct x. Qed.

  Lemma t1Singleton (x : t 1) : x = last.
  Proof. destruct x as [x | x]; destruct x. reflexivity. Qed.

  (**
  An element of
  [FIN.t n]
  is also an element of
  [FIN.t (S n)].
  More generally,
  it is also an element of
  [FIN.t (k + n)].
  *)

  Definition up {n} (x : t n) : t (S n) := inl x.
  Local Notation "++ x" := (up x) (at level 6, right associativity).

  Fixpoint up' {n k} (x : t n) : t (k + n) :=
  match k with
  | O   => x
  | S k => ++(up' x)
  end.

  (**
  ** Functions to and from naturals
  *)

  Definition ofNat (n k : nat) : t (k + S n) := up' last.

  Fixpoint toNat {n} : t (S n) -> nat :=
  match n with
  | O   => fun x => 0
  | S n => fun x => match x with
                    | inl x => toNat x
                    | inr x => n
                    end
  end.

  (**
  Now one would want to prove
  the correctness of [ofNat] and [toNat],
  i.e. that [ofNat (toNat x) k = up' x] and
  that [toNat (ofNat n k) = n].
  It is however nontrivial to even state these,
  since [(k + S n) = (S _)] does not automatically typecheck.
  For my purposes,
  I do not need to prove their correctness so
  I will skip doing so.
  *)

  (**
  ** Notations
  *)

  Module NOTATIONS.
    Delimit Scope FIN with FIN.
    Notation "++ x" := ++x (at level 6, right associativity) : FIN.
  End NOTATIONS.

End FIN.
