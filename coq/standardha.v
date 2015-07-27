(**
* Standard interpretation of Heyting arithmetic
*)

Require Import Coq.Setoids.Setoid.

Require Import fin.
Require Import heytingarithmetic.
Require Import vec.

Import FIN.NOTATIONS.
Import HA.
Import HA.NOTATIONS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.
Local Open Scope HA.

Module STD_HA.

  (**
  ** Definitions
  *)

  (**
  *** Term valuation
  *)

  Fixpoint termVal {n} (t : term n) : VEC.t nat n -> nat :=
  match t with
  | O'     => fun _ => 0
  | var x  => fun f => VEC.nth f x
  | S' t   => fun f => S (termVal t f)
  | u ﬩ v  => fun f => termVal u f + termVal v f
  | u ⋅ v  => fun f => termVal u f * termVal v f
  end.

  Definition termVecVal {n m} (f : VEC.t (term m) n) (g : VEC.t nat m) :
    VEC.t nat n := VEC.map (fun t => termVal t g) f.

  (**
  *** Atomic truth
  *)

  Definition AtomicTruthPred {n} (A : atom n) : VEC.t nat n -> Prop :=
  match A with
  | FF    => fun _ => False
  | u ≐ v => fun f => (termVal u f) = (termVal v f)
  end.

  (**
  *** Truth
  *)

  Fixpoint TruthPred {n} (A : formula n) : VEC.t nat n -> Prop :=
  match A with
  | fAtom A => AtomicTruthPred A
  | A ∧ B   => fun f => TruthPred A f /\ TruthPred B f
  | A ∨ B   => fun f => TruthPred A f \/ TruthPred B f
  | A → B   => fun f => TruthPred A f -> TruthPred B f
  | ∃A      => fun f => exists x : nat, TruthPred A (f, x)
  | ∀A      => fun f => forall x : nat, TruthPred A (f, x)
  end.

  Definition Truth {n} (A : formula n) : Prop :=
    forall f : VEC.t nat n, TruthPred A f.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    Declare Instance interpretation : Interpretation (@Truth).

    Axiom termVecValIdVecEq :
      forall {n} (f : VEC.t nat n), termVecVal idVec f = f.

    Axiom termVecValIdVecUpEq :
      forall {n} (f : VEC.t nat n) (x : nat), termVecVal idVecUp (f, x) = f.

    Axiom termValTermUpEq :
      forall {n} (t : term n) (f : VEC.t nat n) (x : nat),
      termVal (termUp t) (f, x) = termVal t f.

    Axiom termVecValTermVecUpEq :
      forall {n m} (f : VEC.t (term m) n) (g : VEC.t nat m) (x : nat),
      termVecVal (termVecUp f) (g, x) = termVecVal f g.

    Axiom termVecValTermVecUpEq' :
      forall {n m} (f : VEC.t (term m) n) (g : VEC.t nat m) (x : nat),
      termVecVal (termVecUp f;; var FIN.last) (g;; x) = (termVecVal f g;; x).

    Axiom termValTermSubstEq :
      forall {n m} (t : term n) (f : VEC.t (term m) n) (g : VEC.t nat m),
      termVal (termSubst t f) g = termVal t (termVecVal f g).

    Axiom atomicTruthSubstEq :
      forall {n m} (A : atom n) (f : VEC.t (term m) n) (g : VEC.t nat m),
      AtomicTruthPred (atomSubst A f) g <->
      AtomicTruthPred A (termVecVal f g).

    Axiom truthSubstEq :
      forall {n m} (A : formula n) (f : VEC.t (term m) n) (g : VEC.t nat m),
      TruthPred (A // f) g <-> TruthPred A (termVecVal f g).

    Axiom truthLastSubstEq :
      forall {n} (A : formula (S n)) (t : term (S n)) (f : VEC.t nat n)
             (x : nat),
      TruthPred (A /+ t) (f, x) <-> TruthPred A (f, termVal t (f, x)).

    Axiom truthDownSubstEq :
      forall {n} (A : formula (S n)) (t : term n) (f : VEC.t nat n),
      TruthPred (A /- t) f <-> TruthPred A (f, termVal t f).

    Axiom truthUpEq :
      forall {n} (A : formula n) (f : VEC.t nat n) (x : nat),
      TruthPred (up A) (f, x) <-> TruthPred A f.

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Theorem termVecValIdVecEq {n} (f : VEC.t nat n) :
      termVecVal idVec f = f.
    Proof.
      unfold idVec, termVecVal. rewrite VEC.THMS.finMapComposeEq. simpl.
      apply VEC.THMS.pointwiseEquality, VEC.THMS.nthFinMapEq.
    Qed.

    Theorem termVecValIdVecUpEq {n} (f : VEC.t nat n) (x : nat) :
      termVecVal idVecUp (f, x) = f.
    Proof.
      unfold idVecUp, termVecVal. rewrite VEC.THMS.finMapComposeEq'. simpl.
      apply VEC.THMS.pointwiseEquality, VEC.THMS.nthFinMapEq.
    Qed.

    Theorem termValTermUpEq {n} (t : term n) (f : VEC.t nat n) (x : nat) :
      termVal (termUp t) (f, x) = termVal t f.
    Proof.
      induction t as [a | y | t IH | u IHu v IHv | u IHu v IHv]; simpl.
      - reflexivity.
      - reflexivity.
      - rewrite IH. reflexivity.
      - rewrite IHu, IHv. reflexivity.
      - rewrite IHu, IHv. reflexivity.
    Qed.

    Theorem termVecValTermVecUpEq {n m} (f : VEC.t (term m) n) (g : VEC.t nat m)
                                  (x : nat) :
      termVecVal (termVecUp f) (g, x) = termVecVal f g.
    Proof.
      setoid_rewrite VEC.THMS.mapComposeEq.
      apply VEC.THMS.mapRespectsExtensionality; [ | reflexivity].
      intro t. apply termValTermUpEq.
    Qed.

    Theorem termVecValTermVecUpEq' {n m} (f : VEC.t (term m) n)
                                   (g : VEC.t nat m) (x : nat) :
      termVecVal (termVecUp f;; var FIN.last) (g;; x) = (termVecVal f g;; x).
    Proof.
      assert
        (termVecVal (termVecUp f;; var FIN.last) (g;; x) =
         (termVecVal (termVecUp f) (g;; x), x))
      as H by reflexivity.
      setoid_rewrite H. clear H.
      rewrite termVecValTermVecUpEq.
      reflexivity.
    Qed.

    Theorem termValTermSubstEq {n m} (t : term n) (f : VEC.t (term m) n)
                               (g : VEC.t nat m) :
      termVal (termSubst t f) g = termVal t (termVecVal f g).
    Proof.
      induction t as [a | x | t IH | u IHu v IHv | u IHu v IHv]; simpl.
      - reflexivity.
      - unfold termVecVal. rewrite VEC.THMS.nthMapEq. reflexivity.
      - rewrite IH. reflexivity.
      - rewrite IHu, IHv. reflexivity.
      - rewrite IHu, IHv. reflexivity.
    Qed.

    Theorem atomicTruthSubstEq {n m} (A : atom n) (f : VEC.t (term m) n)
                               (g : VEC.t nat m) :
      AtomicTruthPred (atomSubst A f) g <-> AtomicTruthPred A (termVecVal f g).
    Proof.
      destruct A as [ | u v]; simpl.
      - tauto.
      - setoid_rewrite termValTermSubstEq. tauto.
    Qed.

    Theorem truthSubstEq {n m} (A : formula n) (f : VEC.t (term m) n)
                         (g : VEC.t nat m) :
      TruthPred (A // f) g <-> TruthPred A (termVecVal f g).
    Proof.
      generalize dependent m.
      induction A as
        [n A | n A IHA B IHB | n A IHA B IHB | n A IHA B IHB | n A IH | n A IH];
        intros m f g; simpl.
      - apply atomicTruthSubstEq.
      - rewrite IHA, IHB. tauto.
      - rewrite IHA, IHB. tauto.
      - rewrite IHA, IHB. tauto.
      - setoid_rewrite IH. setoid_rewrite termVecValTermVecUpEq'. tauto.
      - setoid_rewrite IH. setoid_rewrite termVecValTermVecUpEq'. tauto.
    Qed.

    Theorem truthLastSubstEq {n} (A : formula (S n)) (t : term (S n))
                             (f : VEC.t nat n) (x : nat) :
      TruthPred (A /+ t) (f, x) <-> TruthPred A (f, termVal t (f, x)).
    Proof.
      setoid_rewrite truthSubstEq.
      assert
        (termVecVal (idVecUp;; t) (f;; x) =
         (termVecVal idVecUp (f;; x));; termVal t (f;; x))
      as H by reflexivity.
      setoid_rewrite H. clear H.
      rewrite termVecValIdVecUpEq.
      tauto.
    Qed.

    Theorem truthDownSubstEq {n} (A : formula (S n)) (t : term n)
                                     (f : VEC.t nat n) :
      TruthPred (A /- t) f <-> TruthPred A (f, termVal t f).
    Proof.
      setoid_rewrite truthSubstEq.
      assert (termVecVal (idVec;; t) f = (termVecVal idVec f, termVal t f))
        as H by reflexivity.
      setoid_rewrite H. clear H.
      rewrite termVecValIdVecEq.
      tauto.
    Qed.

    Theorem truthUpEq {n} (A : formula n) (f : VEC.t nat n) (x : nat) :
      TruthPred (up A) (f, x) <-> TruthPred A f.
    Proof.
      unfold formulaUp. rewrite truthSubstEq, termVecValIdVecUpEq. tauto.
    Qed.

    Instance interpretation : Interpretation (@Truth).
    Proof.
      split; unfold Truth; simpl.
      - intro H. exact (H ()).
      - firstorder.
      - firstorder.
      - intros n A H [f x]. apply truthUpEq. apply H.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - tauto.
      - setoid_rewrite truthDownSubstEq. eauto.
      - setoid_rewrite truthUpEq. firstorder.
      - setoid_rewrite truthUpEq. firstorder.
      - setoid_rewrite truthDownSubstEq. auto.
      - congruence.
      - congruence.
      - congruence.
      - congruence.
      - congruence.
      - congruence.
      - intros [_ x] H. eapply n_Sn. eauto.
      - firstorder.
      - firstorder.
      - firstorder.
      - firstorder.
      - firstorder.
      - intros n A f H IH.
        rewrite truthDownSubstEq in H.
        setoid_rewrite truthLastSubstEq in IH.
        induction x as [ | x IHx].
        + exact H.
        + exact (IH x IHx).
    Qed.

  End THMS.

End STD_HA.
