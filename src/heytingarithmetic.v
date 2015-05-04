Require Coq.omega.Omega.

Require Import myvec.

Import FIN.NOTATIONS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.

Module HA.

  (**********)
  (* SYNTAX *)
  (**********)

  Inductive term (n : nat) :=
  | O'    : term n
  | var   : FIN.t n -> term n
  | S'    : term n -> term n
  | plus' : term n -> term n -> term n
  | mult' : term n -> term n -> term n.
  Arguments O' {_}.
  Arguments S' {_} _.
  Arguments var {_} _.
  Arguments plus' {_} _ _.
  Arguments mult' {_} _ _.
  Local Infix "﬩" := plus' (at level 64).
  Local Infix "⋅" := mult' (at level 63).

  Definition x11 : term 1 := var (FIN.ofNat 0 1).
  Definition x12 : term 2 := var (FIN.ofNat 0 2).
  Definition x22 : term 2 := var (FIN.ofNat 1 2).
  Definition x13 : term 3 := var (FIN.ofNat 0 3).
  Definition x23 : term 3 := var (FIN.ofNat 1 3).
  Definition x33 : term 3 := var (FIN.ofNat 2 3).
  Definition x14 : term 4 := var (FIN.ofNat 0 4).
  Definition x24 : term 4 := var (FIN.ofNat 1 4).
  Definition x34 : term 4 := var (FIN.ofNat 2 4).
  Definition x44 : term 4 := var (FIN.ofNat 3 4).

  Inductive atom (n : nat) :=
    FF     : atom n
  | atomEq : term n -> term n -> atom n.
  Arguments FF {_}.
  Arguments atomEq {_} _ _.
  Local Infix "≐" := atomEq (at level 65).

  Inductive formula n :=
    fAtom : atom n -> formula n
  | fAnd  : formula n -> formula n -> formula n
  | fOr   : formula n -> formula n -> formula n
  | fImp  : formula n -> formula n -> formula n
  | fEx   : formula (S n) -> formula n
  | fFa   : formula (S n) -> formula n.
  Arguments fAtom {_} _.
  Arguments fAnd {_} _ _.
  Arguments fOr {_} _ _.
  Arguments fImp {_} _ _.
  Arguments fEx {_} _.
  Arguments fFa {_} _.
  Local Coercion fAtom : atom >-> formula.
  Local Infix "∧" := fAnd (at level 67, left associativity).
  Local Infix "∨" := fOr (at level 68, left associativity).
  Local Infix "→" := fImp (at level 69, right associativity).
  Local Notation "¬ A" := (A → FF) (at level 66, right associativity).
  Local Infix "≠" := (fun u v => ¬(u ≐ v)) (at level 65).
  Local Notation "∃ A" := (fEx A) (at level 5).
  Local Notation "∀ A" := (fFa A) (at level 5).

  (****************)
  (* SUBSTITUTION *)
  (****************)

  Fixpoint termSubst {n m} (t : term n) (f : VEC.t (term m) n) : term m :=
  match t with
  | O'    => O'
  | var x => VEC.nth f x
  | S' t  => S' (termSubst t f)
  | u ﬩ v => termSubst u f ﬩ termSubst v f
  | u ⋅ v => termSubst u f ⋅ termSubst v f
  end.

  Definition atomSubst {n m} (A : atom n) (f : VEC.t (term m) n) : atom m :=
  match A with
  | FF    => FF
  | u ≐ v => termSubst u f ≐ termSubst v f
  end.

  Fixpoint termUp {n : nat} (t : term n) : term (S n) := match t with
  | O'    => O'
  | var x => var ++x
  | S' t  => S' (termUp t)
  | u ﬩ v => (termUp u) ﬩ (termUp v)
  | u ⋅ v => (termUp u) ⋅ (termUp v)
  end.

  Definition termVecUp {n m : nat} (f : VEC.t (term m) n)
    : VEC.t (term (S m)) n := (VEC.map termUp f).

  Definition termVecUp' {n m : nat} (f : VEC.t (term m) n)
    : VEC.t (term (S m)) (S n) := (termVecUp f, var FIN.last).

  Definition idVec {n} : VEC.t (term n) n := VEC.map var (FIN_VEC.t n).

  Definition idVecUp {n} : VEC.t (term (S n)) n := VEC.map var (FIN_VEC.t' n 1).

  Fixpoint formulaSubstitution {n m} (A : formula n) (f : VEC.t (term m) n)
    : formula m :=
  match A with
  | fAtom A => atomSubst A f
  | A ∧ B   => formulaSubstitution A f ∧ formulaSubstitution B f
  | A ∨ B   => formulaSubstitution A f ∨ formulaSubstitution B f
  | A → B   => formulaSubstitution A f → formulaSubstitution B f
  | ∃A      => ∃(formulaSubstitution A (termVecUp' f))
  | ∀A      => ∀(formulaSubstitution A (termVecUp' f))
  end.
  Local Infix "//" := formulaSubstitution (at level 62, left associativity).

  Definition lastSubstitution {n} (A : formula (S n)) (t : term (S n))
    : formula (S n) := A // (idVecUp, t).
  Local Infix "/+" := lastSubstitution (at level 62, left associativity).

  Definition downSubstitution {n} (A : formula (S n)) (t : term n)
    : formula n := A // (idVec, t).
  Local Infix "/-" := downSubstitution (at level 62, left associativity).

  Definition formulaUp {n} (A : formula n) : formula (S n) := A // idVecUp.

  Local Notation up := formulaUp.

  (*************)
  (* SEMANTICS *)
  (*************)

  Class Model (Truth : forall {n}, formula n -> Prop) := {
    Consistency : ~Truth (@FF 0);

    RuleMP {n} (A B : formula n) : Truth (A → B) -> Truth A -> Truth B;

    RuleGen {n} (A : formula (S n)) : Truth A -> Truth ∀A;

    RuleUp {n} (A : formula n) : Truth A -> Truth (up A);

    AxImp1 {n} (A B : formula n) : Truth (A → B → A);

    AxImp2 {n} (A B C : formula n) : Truth ((A → B → C) → (A → B) → A → C);

    AxAndI {n} (A B : formula n) : Truth (A → B → A ∧ B);

    AxAndE1 {n} (A B : formula n) : Truth (A ∧ B → A);

    AxAndE2 {n} (A B : formula n) : Truth (A ∧ B → B);

    AxOrI1 {n} (A B : formula n) : Truth (A → A ∨ B);

    AxOrI2 {n} (A B : formula n) : Truth (B → A ∨ B);

    AxOrE {n} (A B C : formula n) : Truth (A ∨ B → (A → C) → (B → C) → C);

    AxExFalso {n} (A : formula n) : Truth (FF → A);

    AxExI {n} (A : formula (S n)) (t : term n) : Truth (A /- t → ∃A);

    AxExE {n} (A : formula (S n)) (B : formula n) :
      Truth (∀(A → up B) → ∃A → B);

    AxFaI {n} (A : formula n) (B : formula (S n)) :
      Truth (∀(up A → B) → A → ∀B);

    AxFaE {n} (A : formula (S n)) (t : term n) : Truth (∀A → A /- t);

    AxEqRefl : Truth (x11 ≐ x11);

    AxEqSymm : Truth (x12 ≐ x22 → x22 ≐ x12);

    AxEqTrans : Truth (x13 ≐ x23 → x23 ≐ x33 → x13 ≐ x33);

    AxEqS : Truth (x12 ≐ x22 → S' x12 ≐ S' x22);

    AxEqPlus : Truth (x14 ≐ x24 → x34 ≐ x44 → x14 ﬩ x34 ≐ x24 ﬩ x44);

    AxEqMult : Truth (x14 ≐ x24 → x34 ≐ x44 → x14 ⋅ x34 ≐ x24 ⋅ x44);

    AxPA1 : Truth (S' x11 ≠ x11);

    AxPA2 : Truth (S' x12 ≐ S' x22 → x12 ≐ x22);

    AxPA3 : Truth (x11 ﬩ O' ≐ x11);

    AxPA4 : Truth (x12 ﬩ S' x22 ≐ S' (x12 ﬩ x22));

    AxPA5 : Truth (x11 ⋅ O' ≐ O');

    AxPA6 : Truth (x12 ⋅ S' x22 ≐ x12⋅x22 ﬩ x12);

    AxPA7 {n} (A : formula (S n)) :
      Truth (A /- O' → ∀(A → A/+(S' (var FIN.last))) → ∀A)
  }.

  Definition Provable {n} (A : formula n) :=
    forall Truth (M : Model Truth), Truth n A.

  (******************)
  (* STANDARD MODEL *)
  (******************)

  Fixpoint standardValuation {n} (t : term n) : VEC.t nat n -> nat :=
  match t with
  | O'     => fun _ => 0
  | var x  => fun f => VEC.nth f x
  | S' t   => fun f => S (standardValuation t f)
  | u ﬩ v  => fun f => standardValuation u f + standardValuation v f
  | u ⋅ v  => fun f => standardValuation u f * standardValuation v f
  end.

  Definition vecStandardValuation {n m} (f : VEC.t (term m) n) (g : VEC.t nat m)
    : VEC.t nat n := VEC.map (fun t => standardValuation t g) f.

  Definition AtomicStandardTruthPred {n} (A : atom n) : VEC.t nat n -> Prop :=
  match A with
  | FF    => fun _ => False
  | u ≐ v => fun f => (standardValuation u f) = (standardValuation v f)
  end.

  Fixpoint StandardTruthPred {n} (A : formula n) : VEC.t nat n -> Prop :=
  match A with
  | fAtom A => AtomicStandardTruthPred A
  | A ∧ B   => fun f => StandardTruthPred A f /\ StandardTruthPred B f
  | A ∨ B   => fun f => StandardTruthPred A f \/ StandardTruthPred B f
  | A → B   => fun f => StandardTruthPred A f -> StandardTruthPred B f
  | ∃A      => fun f => exists x : nat, StandardTruthPred A (f, x)
  | ∀A      => fun f => forall x : nat, StandardTruthPred A (f, x)
  end.

  Lemma idVecValuationLemma {n} (f : VEC.t nat n) :
    vecStandardValuation idVec f = f.
  Proof.
    apply VEC.pointwiseEquality. intro x.
    setoid_rewrite VEC.mapCompose. apply FIN_VEC.nthMap.
  Qed.

  Lemma idVecUpValuationLemma {n} (f : VEC.t nat n) (x : nat) :
    vecStandardValuation idVecUp (f;; x) = f.
  Proof.
    apply VEC.pointwiseEquality. intro y.
    setoid_rewrite VEC.mapCompose. setoid_rewrite FIN_VEC.nthMap'.
    reflexivity.
  Qed.

  Lemma termUpValuationLemma {n} (t : term n) (f : VEC.t nat n) (x : nat) :
    standardValuation (termUp t) (f;; x) = standardValuation t f.
  Proof.
    induction t as [a | y | t IH | u IHu v IHv | u IHu v IHv]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH. reflexivity.
    - rewrite IHu, IHv. reflexivity.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  Lemma termVecUpValuationLemma {n m} (f : VEC.t (term m) n)
                                (g : VEC.t nat m) (x : nat) :
    vecStandardValuation (termVecUp f) (g;; x) =
    vecStandardValuation f g.
  Proof.
    setoid_rewrite VEC.mapCompose.
    apply VEC.mapRespectful.
    intro t. apply termUpValuationLemma.
  Qed.

  Lemma termVecUpValuationLemma' {n m} (f : VEC.t (term m) n)
                                 (g : VEC.t nat m) (x : nat) :
    vecStandardValuation (termVecUp' f) (g;; x) =
    (vecStandardValuation f g;; x).
  Proof.
    assert
      (vecStandardValuation (termVecUp' f) (g;; x) =
       (vecStandardValuation (termVecUp f) (g;; x), x))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite termVecUpValuationLemma.
    reflexivity.
  Qed.

  Lemma termSubstitionLemma {n m} (t : term n) (f : VEC.t (term m) n)
                            (g : VEC.t nat m) :
    standardValuation (termSubst t f) g =
    standardValuation t (vecStandardValuation f g).
  Proof.
    induction t as [a | x | t IH | u IHu v IHv | u IHu v IHv]; simpl.
    - reflexivity.
    - setoid_rewrite VEC.mapNth. reflexivity.
    - rewrite IH. reflexivity.
    - rewrite IHu, IHv. reflexivity.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  Lemma atomSubstitutionLemma {n m} (A : atom n) (f : VEC.t (term m) n)
                              (g : VEC.t nat m) :
    AtomicStandardTruthPred (atomSubst A f) g <->
    AtomicStandardTruthPred A (vecStandardValuation f g).
  Proof.
    destruct A as [ | u v]; simpl.
    - tauto.
    - setoid_rewrite termSubstitionLemma. tauto.
  Qed.

  Lemma substitutionLemma {n m} (A : formula n) (f : VEC.t (term m) n)
                          (g : VEC.t nat m) :
    StandardTruthPred (A // f) g <->
    StandardTruthPred A (vecStandardValuation f g).
  Proof.
    generalize dependent m.
    induction A as
      [n A | n A IHA B IHB | n A IHA B IHB | n A IHA B IHB | n A IH | n A IH];
    intros m f g; simpl.
    - apply atomSubstitutionLemma.
    - rewrite IHA, IHB. tauto.
    - rewrite IHA, IHB. tauto.
    - rewrite IHA, IHB. tauto.
    - setoid_rewrite IH. setoid_rewrite termVecUpValuationLemma'. tauto.
    - setoid_rewrite IH. setoid_rewrite termVecUpValuationLemma'. tauto.
  Qed.

  Lemma lastSubstitutionLemma {n} (A : formula (S n)) (t : term (S n))
                              (f : VEC.t nat n) (x : nat) :
    StandardTruthPred (A /+ t) (f, x) <->
    StandardTruthPred A (f, standardValuation t (f, x)).
  Proof.
    setoid_rewrite substitutionLemma.
    assert
      (vecStandardValuation (idVecUp;; t) (f;; x) =
       (vecStandardValuation idVecUp (f;; x));; standardValuation t (f;; x))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite idVecUpValuationLemma.
    tauto.
  Qed.

  Lemma downSubstitutionLemma {n} (A : formula (S n)) (t : term n)
                              (f : VEC.t nat n) :
    StandardTruthPred (A /- t) f <->
    StandardTruthPred A (f, standardValuation t f).
  Proof.
    setoid_rewrite substitutionLemma.
    assert
      (vecStandardValuation (idVec;; t) f =
       (vecStandardValuation idVec f;; standardValuation t f))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite idVecValuationLemma.
    tauto.
  Qed.

  Lemma upLemma {n} (A : formula n) (f : VEC.t nat n) (x : nat) :
    StandardTruthPred (up A) (f, x) <-> StandardTruthPred A f.
  Proof.
    unfold up. rewrite substitutionLemma, idVecUpValuationLemma. tauto.
  Qed.

  Definition StandardTruth {n} (A : formula n) : Prop :=
    forall f : VEC.t nat n, StandardTruthPred A f.

  Instance standardModel : Model (@StandardTruth).
  Proof.
    split;
    try (intro f; simpl; auto; try congruence; try firstorder; try omega; fail).
    - intro H. exact (H ()).
    - intros n A H [f x]. apply upLemma. apply H.
    - intros n A t f. simpl. rewrite downSubstitutionLemma. eauto.
    - intros n A B f. simpl. setoid_rewrite upLemma. firstorder.
    - intros n A B f. simpl. setoid_rewrite upLemma. eauto.
    - intros n A t f. simpl. rewrite downSubstitutionLemma. eauto.
    - intros n A f. simpl. rewrite downSubstitutionLemma. simpl. intros H IH x.
      induction x as [ | x IHx].
      + exact H.
      + specialize (IH x IHx). rewrite lastSubstitutionLemma in IH. exact IH.
  Qed.

  Module NOTATIONS.

    Delimit Scope HA with HA.

    Infix "﬩" := plus' (at level 64) : HA.
    Infix "⋅" := mult' (at level 63) : HA.
    Infix "≐" := atomEq (at level 65) : HA.
    Notation "¬ A" := (¬A) (at level 66, right associativity) : HA.
    Infix "≠" := (fun u v => u ≠ v) (at level 65) : HA.
    Infix "∧" := fAnd (at level 67, left associativity) : HA.
    Infix "∨" := fOr (at level 68, left associativity) : HA.
    Infix "→" := fImp (at level 69, right associativity) : HA.
    Notation "∃ A" := ∃A (at level 5) : HA.
    Notation "∀ A" := ∀A (at level 5) : HA.
    Infix "//" := formulaSubstitution (at level 62, left associativity) : HA.
    Infix "/+" := lastSubstitution (at level 62, left associativity) : HA.
    Infix "/-" := downSubstitution (at level 62, left associativity) : HA.
    Notation up := (fun A => up A).

  End NOTATIONS.

End HA.

Module HA_COERCIONS.
  Import HA.
  Coercion fAtom : atom >-> formula.
End HA_COERCIONS.
