(**
* Heyting arithmetic
*)

Require Import Coq.Setoids.Setoid.

Require Import fin.
Require Import vec.

Import FIN.NOTATIONS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.

Module HA.

  (**
  ** Syntax
  *)

  (**
  *** Terms
  *)

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

  Definition x01 : term 1 := var (FIN.ofNat 0 0).
  Definition x02 : term 2 := var (FIN.ofNat 0 1).
  Definition x12 : term 2 := var (FIN.ofNat 1 0).
  Definition x03 : term 3 := var (FIN.ofNat 0 2).
  Definition x13 : term 3 := var (FIN.ofNat 1 1).
  Definition x23 : term 3 := var (FIN.ofNat 2 0).
  Definition x04 : term 4 := var (FIN.ofNat 0 3).
  Definition x14 : term 4 := var (FIN.ofNat 1 2).
  Definition x24 : term 4 := var (FIN.ofNat 2 1).
  Definition x34 : term 4 := var (FIN.ofNat 3 0).

  (**
  *** Atomic formulas
  *)

  Inductive atom (n : nat) :=
  | FF     : atom n
  | atomEq : term n -> term n -> atom n.
  Arguments FF {_}.
  Arguments atomEq {_} _ _.
  Local Infix "≐" := atomEq (at level 65).

  (**
  *** Formulas
  *)

  Inductive formula n :=
  | fAtom : atom n -> formula n
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

  (**
  *** Term promotion
  *)

  Fixpoint termUp {n : nat} (t : term n) : term (S n) :=
  match t with
  | O'    => O'
  | var x => var ++x
  | S' t  => S' (termUp t)
  | u ﬩ v => (termUp u) ﬩ (termUp v)
  | u ⋅ v => (termUp u) ⋅ (termUp v)
  end.

  Definition termVecUp {n m} (f : VEC.t (term m) n) : VEC.t (term (S m)) n :=
    VEC.map termUp f.

  (**
  *** Identity term vectors
  *)

  Definition idVec {n} : VEC.t (term n) n := VEC.finMap var.

  Definition idVecUp {n} : VEC.t (term (S n)) n := VEC.finMap' (k := 1) var.

  (**
  ** Substitution
  *)

  (**
  *** Substitution in terms
  *)

  Fixpoint termSubst {n m} (t : term n) (f : VEC.t (term m) n) : term m :=
  match t with
  | O'    => O'
  | var x => VEC.nth f x
  | S' t  => S' (termSubst t f)
  | u ﬩ v => termSubst u f ﬩ termSubst v f
  | u ⋅ v => termSubst u f ⋅ termSubst v f
  end.

  (**
  *** Substitution in atoms
  *)

  Definition atomSubst {n m} (A : atom n) (f : VEC.t (term m) n) : atom m :=
  match A with
  | FF    => FF
  | u ≐ v => termSubst u f ≐ termSubst v f
  end.

  (**
  *** Substitution in formulas
  *)

  Fixpoint formulaSubst {n m} (A : formula n) (f : VEC.t (term m) n)
    : formula m :=
  match A with
  | fAtom A => atomSubst A f
  | A ∧ B   => formulaSubst A f ∧ formulaSubst B f
  | A ∨ B   => formulaSubst A f ∨ formulaSubst B f
  | A → B   => formulaSubst A f → formulaSubst B f
  | ∃A      => ∃(formulaSubst A ((termVecUp f), var FIN.last))
  | ∀A      => ∀(formulaSubst A ((termVecUp f), var FIN.last))
  end.
  Local Infix "//" := formulaSubst (at level 62, left associativity).

  (**
  *** Substitution in the last variable
  *)

  Definition lastSubst {n} (A : formula (S n)) (t : term (S n)) : formula (S n)
    := A // (idVecUp, t).
  Local Infix "/+" := lastSubst (at level 62, left associativity).

  Definition downSubst {n} (A : formula (S n)) (t : term n) : formula n :=
    A // (idVec, t).
  Local Infix "/-" := downSubst (at level 62, left associativity).

  (**
  *** Formula promotion
  *)

  Definition formulaUp {n} (A : formula n) : formula (S n) := A // idVecUp.
  Local Notation up := formulaUp.

  (**
  ** Semantics
  *)

  Class Interpretation (Truth : forall {n}, formula n -> Prop) := {
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
    AxExI {n} (A : formula (S n)) (t : term n) : Truth (A/-t → ∃A);
    AxExE {n} (A : formula (S n)) (B : formula n) :
      Truth (∀(A → up B) → ∃A → B);
    AxFaI {n} (A : formula n) (B : formula (S n)) :
      Truth (∀(up A → B) → A → ∀B);
    AxFaE {n} (A : formula (S n)) (t : term n) : Truth (∀A → A/-t);
    AxEqRefl : Truth (x01 ≐ x01);
    AxEqSymm : Truth (x02 ≐ x12 → x12 ≐ x02);
    AxEqTrans : Truth (x03 ≐ x13 → x13 ≐ x23 → x03 ≐ x23);
    AxEqS : Truth (x02 ≐ x12 → S' x02 ≐ S' x12);
    AxEqPlus : Truth (x04 ≐ x14 → x24 ≐ x34 → x04 ﬩ x24 ≐ x14 ﬩ x34);
    AxEqMult : Truth (x04 ≐ x14 → x24 ≐ x34 → x04 ⋅ x24 ≐ x14 ⋅ x34);
    AxPA1 : Truth (S' x01 ≠ x01);
    AxPA2 : Truth (S' x02 ≐ S' x12 → x02 ≐ x12);
    AxPA3 : Truth (x01 ﬩ O' ≐ x01);
    AxPA4 : Truth (x02 ﬩ S' x12 ≐ S' (x02 ﬩ x12));
    AxPA5 : Truth (x01 ⋅ O' ≐ O');
    AxPA6 : Truth (x02 ⋅ S' x12 ≐ x02⋅x12 ﬩ x02);
    AxPA7 {n} (A : formula (S n)) :
      Truth (A/-O' → ∀(A → A/+(S' (var FIN.last))) → ∀A)
  }.

  (**
  ** Standard interpretation
  *)

  (**
  *** Standard term valuation
  *)

  Fixpoint standardVal {n} (t : term n) : VEC.t nat n -> nat :=
  match t with
  | O'     => fun _ => 0
  | var x  => fun f => VEC.nth f x
  | S' t   => fun f => S (standardVal t f)
  | u ﬩ v  => fun f => standardVal u f + standardVal v f
  | u ⋅ v  => fun f => standardVal u f * standardVal v f
  end.

  Definition standardVecVal {n m} (f : VEC.t (term m) n) (g : VEC.t nat m) :
    VEC.t nat n := VEC.map (fun t => standardVal t g) f.

  (**
  *** Standard atomic truth
  *)

  Definition AtomicStandardTruthPred {n} (A : atom n) : VEC.t nat n -> Prop :=
  match A with
  | FF    => fun _ => False
  | u ≐ v => fun f => (standardVal u f) = (standardVal v f)
  end.

  (**
  *** Standard truth
  *)

  Fixpoint StandardTruthPred {n} (A : formula n) : VEC.t nat n -> Prop :=
  match A with
  | fAtom A => AtomicStandardTruthPred A
  | A ∧ B   => fun f => StandardTruthPred A f /\ StandardTruthPred B f
  | A ∨ B   => fun f => StandardTruthPred A f \/ StandardTruthPred B f
  | A → B   => fun f => StandardTruthPred A f -> StandardTruthPred B f
  | ∃A      => fun f => exists x : nat, StandardTruthPred A (f, x)
  | ∀A      => fun f => forall x : nat, StandardTruthPred A (f, x)
  end.

  Definition StandardTruth {n} (A : formula n) : Prop :=
    forall f : VEC.t nat n, StandardTruthPred A f.

  Lemma standardVecValIdVecEq {n} (f : VEC.t nat n) :
    standardVecVal idVec f = f.
  Proof.
    unfold idVec, standardVecVal. rewrite VEC.finMapComposeEq. simpl.
    apply VEC.pointwiseEquality, VEC.nthFinMapEq.
  Qed.

  Lemma standardVecValIdVecUpEq {n} (f : VEC.t nat n) (x : nat) :
    standardVecVal idVecUp (f, x) = f.
  Proof.
    unfold idVecUp, standardVecVal. rewrite VEC.finMapComposeEq'. simpl.
    apply VEC.pointwiseEquality, VEC.nthFinMapEq.
  Qed.

  Lemma standardValTermUpEq {n} (t : term n) (f : VEC.t nat n) (x : nat) :
    standardVal (termUp t) (f, x) = standardVal t f.
  Proof.
    induction t as [a | y | t IH | u IHu v IHv | u IHu v IHv]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH. reflexivity.
    - rewrite IHu, IHv. reflexivity.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  Lemma standardVecValTermVecUpEq {n m} (f : VEC.t (term m) n)
                                  (g : VEC.t nat m) (x : nat) :
    standardVecVal (termVecUp f) (g, x) = standardVecVal f g.
  Proof.
    setoid_rewrite VEC.mapComposeEq.
    apply VEC.mapRespectful.
    intro t. apply standardValTermUpEq.
  Qed.

  Lemma standardVecValTermVecUpEq' {n m} (f : VEC.t (term m) n)
                                   (g : VEC.t nat m) (x : nat) :
    standardVecVal (termVecUp f;; var FIN.last) (g;; x) =
    (standardVecVal f g;; x).
  Proof.
    assert
      (standardVecVal (termVecUp f;; var FIN.last) (g;; x) =
       (standardVecVal (termVecUp f) (g;; x), x))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite standardVecValTermVecUpEq.
    reflexivity.
  Qed.

  Lemma standardValTermSubstEq {n m} (t : term n) (f : VEC.t (term m) n)
                               (g : VEC.t nat m) :
    standardVal (termSubst t f) g = standardVal t (standardVecVal f g).
  Proof.
    induction t as [a | x | t IH | u IHu v IHv | u IHu v IHv]; simpl.
    - reflexivity.
    - unfold standardVecVal. rewrite VEC.nthMapEq. reflexivity.
    - rewrite IH. reflexivity.
    - rewrite IHu, IHv. reflexivity.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  Lemma atomicTruthSubstEq {n m} (A : atom n) (f : VEC.t (term m) n)
                           (g : VEC.t nat m) :
    AtomicStandardTruthPred (atomSubst A f) g <->
    AtomicStandardTruthPred A (standardVecVal f g).
  Proof.
    destruct A as [ | u v]; simpl.
    - tauto.
    - setoid_rewrite standardValTermSubstEq. tauto.
  Qed.

  Lemma standardTruthSubstEq {n m} (A : formula n) (f : VEC.t (term m) n)
                             (g : VEC.t nat m) :
    StandardTruthPred (A // f) g <-> StandardTruthPred A (standardVecVal f g).
  Proof.
    generalize dependent m.
    induction A as
      [n A | n A IHA B IHB | n A IHA B IHB | n A IHA B IHB | n A IH | n A IH];
      intros m f g; simpl.
    - apply atomicTruthSubstEq.
    - rewrite IHA, IHB. tauto.
    - rewrite IHA, IHB. tauto.
    - rewrite IHA, IHB. tauto.
    - setoid_rewrite IH. setoid_rewrite standardVecValTermVecUpEq'. tauto.
    - setoid_rewrite IH. setoid_rewrite standardVecValTermVecUpEq'. tauto.
  Qed.

  Lemma standardTruthLastSubstEq {n} (A : formula (S n)) (t : term (S n))
                                 (f : VEC.t nat n) (x : nat) :
    StandardTruthPred (A /+ t) (f, x) <->
    StandardTruthPred A (f, standardVal t (f, x)).
  Proof.
    setoid_rewrite standardTruthSubstEq.
    assert
      (standardVecVal (idVecUp;; t) (f;; x) =
       (standardVecVal idVecUp (f;; x));; standardVal t (f;; x))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite standardVecValIdVecUpEq.
    tauto.
  Qed.

  Lemma standardTruthDownSubstEq {n} (A : formula (S n)) (t : term n)
                                 (f : VEC.t nat n) :
    StandardTruthPred (A /- t) f <-> StandardTruthPred A (f, standardVal t f).
  Proof.
    setoid_rewrite standardTruthSubstEq.
    assert
      (standardVecVal (idVec;; t) f = (standardVecVal idVec f, standardVal t f))
    as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite standardVecValIdVecEq.
    tauto.
  Qed.

  Lemma standardTruthUpEq {n} (A : formula n) (f : VEC.t nat n) (x : nat) :
    StandardTruthPred (up A) (f, x) <-> StandardTruthPred A f.
  Proof.
    unfold up. rewrite standardTruthSubstEq, standardVecValIdVecUpEq. tauto.
  Qed.

  Instance standardModel : Interpretation (@StandardTruth).
  Proof.
    split; unfold StandardTruth; simpl.
    - intro H. exact (H ()).
    - firstorder.
    - firstorder.
    - intros n A H [f x]. apply standardTruthUpEq. apply H.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - setoid_rewrite standardTruthDownSubstEq. eauto.
    - setoid_rewrite standardTruthUpEq. firstorder.
    - setoid_rewrite standardTruthUpEq. firstorder.
    - setoid_rewrite standardTruthDownSubstEq. auto.
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
      rewrite standardTruthDownSubstEq in H.
      setoid_rewrite standardTruthLastSubstEq in IH.
      induction x as [ | x IHx].
      + exact H.
      + exact (IH x IHx).
  Qed.

  (**
  ** Notations
  *)

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
    Infix "//" := (fun A f => A//f) (at level 62, left associativity) : HA.
    Infix "/+" := (fun A t => A/+t) (at level 62, left associativity) : HA.
    Infix "/-" := (fun A t => A/-t) (at level 62, left associativity) : HA.
    Notation up := (fun A => up A).
  End NOTATIONS.

End HA.

(**
** Coercions
*)

Module HA_COERCIONS.
  Coercion HA.fAtom : HA.atom >-> HA.formula.
End HA_COERCIONS.
