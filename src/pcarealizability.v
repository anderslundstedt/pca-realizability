Require Import Coq.Classes.Morphisms.

Require Import heytingarithmetic.
Require Import myvec.
Require Import pas.
Require Import pca.

Import FIN.NOTATIONS.
Import HA.NOTATIONS.
Import HA_COERCIONS.
Import PAS.NOTATIONS.
Import PAS_COERCIONS.
Import PCA.NOTATIONS.
Import PCA_COERCIONS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.
Local Open Scope HA.
Local Open Scope PAS.
Local Open Scope PCA.

Local Notation Pca := PCA.Pca.
Local Notation k := PCA.k.
Local Notation s := PCA.s.
Local Notation x11 := PAS.x11.
Local Notation x12 := PAS.x12.
Local Notation x22 := PAS.x22.
Local Notation x13 := PAS.x13.
Local Notation x23 := PAS.x23.
Local Notation x33 := PAS.x33.

Module PCA_REL.

  Local Notation "## f" :=
    (VEC.map (fun x => #x) f) (at level 6, right associativity).

  Definition RealizabilityPred {_ : Pca} (n : nat) :=
    VEC.t nat n -> PAS.term 0 -> Prop.

  Definition AtomicRealizability {_ : Pca} {n} (P : HA.atom n) :
    RealizabilityPred n := fun f t => HA.StandardTruthPred P f /\ t!.

  Fixpoint Realizability `{_ : Pca} {n} (P : HA.formula n)
    : RealizabilityPred n :=
  match P with
  | HA.fAtom P => AtomicRealizability P
  | P ∧ Q      =>
      fun f t => Realizability P f (π1*t) /\ Realizability Q f (π2*t)
  | P ∨ Q      =>
      fun f t => (π1*t ≃ #0 /\ Realizability P f (π2*t)) \/
                 (π1*t ≃ #1 /\ Realizability Q f (π2*t))
  | P → Q      =>
      fun f u => u! /\ forall v, Realizability P f v -> Realizability Q f (u*v)
  | ∃P         =>
      fun f t => exists n : nat, π1*t ≃ #n /\ Realizability P (f, n) (π2*t)
  | ∀P         => fun f t => forall x : nat, Realizability P (f, x) (t*#x)
  end.

  Lemma realizabilityRespectful {pca : Pca} {n} (A : HA.formula n)
                                (f : VEC.t nat n) (u v : PAS.term 0) :
    u ≃ v -> Realizability A f u -> Realizability A f v.
  Proof.
    generalize dependent u.
    generalize dependent v.
    induction A as
      [n A | n A IHA B IHB | n A IHA B IHB | n A IHA B IHB | n A IH | n A IH  ];
    intros u v Huv; simpl.
    - unfold AtomicRealizability. rewrite Huv. tauto.
    - intros [HA HB]. split.
      + apply (IHA f (π1*u) (π1*v)).
        * rewrite Huv. reflexivity.
        * exact HA.
      + apply (IHB f (π2*u) (π2*v)).
        * rewrite Huv. reflexivity.
        * exact HB.
    - intros [[H H'] | [H H']].
      + left. split.
        * rewrite <- Huv. exact H.
        * apply (IHA f (π2*u) (π2*v)); [ | exact H']. rewrite Huv. reflexivity.
      + right. split.
        * rewrite <- Huv. exact H.
        * apply (IHB f (π2*u) (π2*v)); [ | exact H']. rewrite Huv. reflexivity.
    - intros [Hv H]. split; [rewrite <- Huv; exact Hv | ].
      intros w Hw. specialize (H w Hw). apply IHB with (u := v*w).
      + rewrite Huv. reflexivity.
      + exact H.
    - intros [x [Hx H]]. exists x. split; [rewrite <- Huv; exact Hx | ].
      apply IH with (u := π2*v).
      + rewrite Huv. reflexivity.
      + exact H.
    - intros H x. apply IH with (u := v*#x).
      + rewrite Huv. reflexivity.
      + apply H.
  Qed.

  Instance realizabilityProper {pca : Pca} {n} (A : HA.formula n)
                               (f : VEC.t nat n) :
    Proper (PAS.ClosedTermEq ==> iff) (Realizability A f).
  Proof.
    intros u v Huv.
    split; intro H; [ | symmetry in Huv]; eauto using realizabilityRespectful.
  Qed.

  Lemma realizersDenote {pca : Pca} {n} {A : HA.formula n} {f : VEC.t nat n}
                        {t : PAS.term 0} :
    Realizability A f t -> t!.
  Proof.
    generalize dependent t.
    induction A as
      [n A | n A IHA B _ | n A IHA B IHB | n A _ B _ | n A IH | n A IH];
    simpl; intro t.
    - unfold AtomicRealizability. tauto.
    - intros [H _]. eauto using PAS.subTermDenotes.
    - intros [ [H H'] | [H H'] ]; eauto using PAS.subTermDenotes.
    - tauto.
    - intros [x [H H'] ]. eauto using PAS.subTermDenotes.
    - intros H. specialize (H 0). eauto using PAS.subTermDenotes.
  Qed.

  Lemma substitutionLemma {pca : Pca} {n m} (A : HA.formula n)
                          (f : VEC.t (HA.term m) n) (g : VEC.t nat m)
                          (t : PAS.term 0) :
    Realizability (A // f) g t <->
    Realizability  A (HA.vecStandardValuation f g) t.
  Proof.
    generalize dependent m. generalize dependent t.
    induction A as
      [n A | n A IHA B IHB | n A IHA B IHB | n A IHA B IHB | n A IH | n A IH];
    intros m f g; simpl.
    - unfold AtomicRealizability.
      setoid_rewrite HA.atomSubstitutionLemma.
      tauto.
    - setoid_rewrite IHA. setoid_rewrite IHB. tauto.
    - setoid_rewrite IHA. setoid_rewrite IHB. tauto.
    - setoid_rewrite IHA. setoid_rewrite IHB. tauto.
    - setoid_rewrite IH. setoid_rewrite HA.termVecUpValuationLemma'. tauto.
    - setoid_rewrite IH. setoid_rewrite HA.termVecUpValuationLemma'. tauto.
  Qed.

  Lemma lastSubstitutionLemma {pca : Pca} {n} (A : HA.formula (S n))
                              (t : HA.term (S n)) (f : VEC.t nat n) (x : nat)
                              (u : PAS.term 0) :
    Realizability (A /+ t) (f, x) u <->
    Realizability A (f, HA.standardValuation t (f, x)) u.
  Proof.
    setoid_rewrite substitutionLemma.
    assert
      (HA.vecStandardValuation (HA.idVecUp;; t) (f;; x) =
       (HA.vecStandardValuation HA.idVecUp (f;; x));;
        HA.standardValuation t (f;; x))
    as H by reflexivity.
    rewrite H. clear H.
    setoid_rewrite HA.idVecUpValuationLemma.
    tauto.
  Qed.

  Lemma downSubstitutionLemma {pca : Pca} {n} (A : HA.formula (S n))
                              (t : HA.term n) (f : VEC.t nat n)
                              (u : PAS.term 0) :
    Realizability (A /- t) f u <->
    Realizability A (f, HA.standardValuation t f) u.
  Proof.
    setoid_rewrite substitutionLemma.
    assert
      (HA.vecStandardValuation (HA.idVec;; t) f =
       (HA.vecStandardValuation HA.idVec f);; HA.standardValuation t f)
    as H by reflexivity.
    rewrite H. clear H.
    setoid_rewrite HA.idVecValuationLemma.
    tauto.
  Qed.

  Lemma upLemma {pca : Pca} {n} (A : HA.formula n) (f : VEC.t nat n) (x : nat)
                (t : PAS.term 0) :
    Realizability (up A) (f, x) t <-> Realizability A f t.
  Proof.
    unfold HA.formulaUp. rewrite substitutionLemma, HA.idVecUpValuationLemma.
    tauto.
  Qed.

  Definition IsRealizable {_ : Pca} {n} (P : HA.formula n) : Prop :=
    exists t : PAS.term 0, forall f : VEC.t nat n, Realizability P f (t**##f).

  Lemma combinatoryCompleteness1 {pca : Pca} {n} (t : PAS.term (S n))
                                 (f : VEC.t nat n) :
    λ t ** ##f!.
  Proof.
    apply PCA.combinatoryCompleteness1'.
    intro x. rewrite VEC.mapNth. apply PCA.natRepresentationCombinatorDenotes.
  Qed.

  Lemma combinatoryCompleteness2 {pca : Pca} {n} (t : PAS.term n)
                                 (f : VEC.t nat n) :
    λ t ** ##f ≃ t/##f.
  Proof.
    apply PCA.combinatoryCompleteness2'.
    intro x. rewrite VEC.mapNth. apply PCA.natRepresentationCombinatorDenotes.
  Qed.

  Lemma combinatoryCompleteness2' {pca : Pca} {n} (t : PAS.term (S n))
                                  (f : VEC.t nat n) (a : pca) :
    λ t ** ##f * &a ≃ t/(##f, &a).
  Proof.
    cutrewrite (λ t ** ##f * &a = λ t ** (##f;; &a)); [ | reflexivity].
    apply PCA.combinatoryCompleteness2'.
    destruct x as [x | x]; simpl.
    - rewrite VEC.mapNth. apply PCA.natRepresentationCombinatorDenotes.
    - exists a. reflexivity.
  Qed.

  Fixpoint termRepresentation {pca : Pca} {n} (t : HA.term n) : PAS.term 0 :=
  match t with
  | HA.O'       => λ (n := n) $ #0
  | HA.var x    => λ (PAS.termVar x)
  | HA.S' t     => λ (n := n) ($ σ * $(termRepresentation t) ** PAS.idVec 0)
  | u ﬩ v       =>
    let u' := $(termRepresentation u) ** PAS.idVec 0 in
    let v' := $(termRepresentation v) ** PAS.idVec 0 in
    λ (n := n) ($ α * u' * v')
  | u ⋅ v       =>
    let u' := $(termRepresentation u) ** PAS.idVec 0 in
    let v' := $(termRepresentation v) ** PAS.idVec 0 in
    λ (n := n) ($ μ * u' * v')
  end.
  Local Notation termRep := termRepresentation.

  Lemma termRepresentationCorrect {pca : Pca} {n} (t : HA.term n)
                                  (f : VEC.t nat n) :
    (termRep t)**##f ≃ #(HA.standardValuation t f).
  Proof.
    induction t as [ | x | t IHt | u IHu v IHv | u IHu v IHv];
    simpl; rewrite combinatoryCompleteness2; simpl.
    - setoid_rewrite PAS.closedTermSubstitutionLemma0. reflexivity.
    - rewrite VEC.mapNth. reflexivity.
    - setoid_rewrite PAS.idVecProductSubstitutionEq0'.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      rewrite IHt.
      rewrite PCA.successorCombinatorCorrect.
      reflexivity.
    - setoid_rewrite PAS.idVecProductSubstitutionEq0'.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      rewrite IHu, IHv.
      rewrite PCA.additionCombinatorCorrect.
      reflexivity.
    - setoid_rewrite PAS.idVecProductSubstitutionEq0'.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      rewrite IHu, IHv.
      rewrite PCA.multiplicationCombinatorCorrect.
      reflexivity.
  Qed.

  Instance realizabilityModel {pca : Pca} : HA.Model (@IsRealizable _).
  Proof.
    split.
    - intros [t H]. specialize (H ()). destruct H as [H _]. exact H.
    - intros n A B [u Hu] [v Hv].
      exists (λ (n := n) ($ u ** PAS.idVec 0 * $ v ** PAS.idVec 0)).
      intro f.
      specialize (Hu f). specialize (Hv f).
      rewrite combinatoryCompleteness2.
      simpl.
      setoid_rewrite PAS.idVecProductSubstitutionEq0'.
      destruct Hu as [_ Hu]. exact (Hu _ Hv).
    - intros n A [t H]. exists t. intro f. simpl. intro x. apply H.
    - intros n A [t H].
      exists (λ (n := (S n)) ($ t ** PAS.idVec 1)).
      intros [f x].
      rewrite combinatoryCompleteness2, upLemma.
      assert (##(f;; x) = (##f;; #x)) as H' by reflexivity.
      rewrite H'. clear H'.
      setoid_rewrite PAS.idVecProductSubstitutionEq1'.
      apply H.
    - intros n A B.
      exists (λ (n := n) &k).
      intro f.
      rewrite combinatoryCompleteness2. simpl.
      split; [exists k; reflexivity | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hua].
      setoid_rewrite Hua. rewrite Hua in Ha. clear dependent u.
      split; [apply PCA.kaDenotes | ].
      intros v Hb. destruct (realizersDenote Hb) as [b Hvb].
      rewrite Hvb in *. clear dependent v.
      setoid_rewrite PCA.kSpec. exact Ha.
    - intros n A B C.
      exists (λ (n := n) &s).
      intro f. rewrite combinatoryCompleteness2.
      split; [exists s; reflexivity | ].
      intros t Ha. destruct (realizersDenote Ha) as [a Ht]. rewrite Ht in *.
      clear dependent t.
      split; [ apply PCA.saDenotes | ].
      intros t Hb. destruct (realizersDenote Hb) as [b Ht]. rewrite Ht in *.
      clear dependent t.
      split; [ apply PCA.sSpec1 | ].
      intros t Hc. destruct (realizersDenote Hc) as [c Ht]. rewrite Ht in *.
      clear dependent t.
      setoid_rewrite PCA.sSpec2'.
      destruct Ha as [_ Ha], Hb as [_ Hb].
      specialize (Ha _ Hc). specialize (Hb _ Hc).
      destruct Ha as [_ Ha]. exact (Ha _ Hb).
    - intros n A B. exists (λ (n := n) $ π). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [ apply PCA.pairingCombinatorDenotes | ].
      intros t Ha. destruct (realizersDenote Ha) as [a Ht]. rewrite Ht in *.
      clear dependent t.
      split; [apply PCA.pairingCombinatorDenotes' | ].
      intros t Hb. destruct (realizersDenote Hb) as [b Ht]. rewrite Ht in *.
      clear dependent t.
      split.
      + rewrite PCA.leftProjectionCombinatorCorrect. exact Ha.
      + rewrite PCA.rightProjectionCombinatorCorrect. exact Hb.
    - intros n A B. exists (λ (n := n) $ π1). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [apply PCA.leftProjectionCombinatorDenotes | ]. simpl. tauto.
    - intros n A B. exists (λ (n := n) $ π2). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [apply PCA.rightProjectionCombinatorDenotes | ]. simpl. tauto.
    - intros n A B. exists (λ (n := n) ($ (π * #0))). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      destruct (PCA.natRepresentationCombinatorDenotes 0) as [x Hx].
      rewrite Hx.
      split; [apply PCA.pairingCombinatorDenotes' | ].
      intros t Ha. destruct (realizersDenote Ha) as [a Ht]. rewrite Ht in *.
      clear dependent t.
      left. split.
      + rewrite PCA.leftProjectionCombinatorCorrect, Hx. reflexivity.
      + rewrite PCA.rightProjectionCombinatorCorrect. exact Ha.
    - intros n A B. exists (λ (n := n) ($ (π * #1))). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      destruct (PCA.natRepresentationCombinatorDenotes 1) as [x Hx].
      rewrite Hx.
      split; [apply PCA.pairingCombinatorDenotes' | ].
      intros t Ha. destruct (realizersDenote Ha) as [a Ht]. rewrite Ht in *.
      clear dependent t.
      right. split.
      + rewrite PCA.leftProjectionCombinatorCorrect, Hx. reflexivity.
      + rewrite PCA.rightProjectionCombinatorCorrect. exact Ha.
    - intros n A B C.
      set (t := $ δ * x23 * x33 * ($ π1 * x13) * ($ π2 * x13)). simpl in t.
      exists (λ (n := n) $ (λ t)). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [apply PCA.representationsDenote | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      split. {
        apply PAS.subTermDenotes with (v := λ t * &a * &a); [auto | ].
        cutrewrite (λ t * &a * &a = λ t ** &&(();; a;; a)); [ | reflexivity].
        apply PCA.combinatoryCompleteness1.
      }
      intros u Hb. destruct (realizersDenote Hb) as [b Hu]. rewrite Hu in *.
      clear dependent u.
      split. {
        cutrewrite (λ t * &a * &b = λ t ** &&(();; a;; b)); [ | reflexivity].
        apply PCA.combinatoryCompleteness1.
      }
      intros u Hc. destruct (realizersDenote Hc) as [c Hu]. rewrite Hu in *.
      clear dependent u.
      rewrite PCA.combinatoryCompletenessInstance3. simpl.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      destruct Ha as [[H H'] | [H H']]; rewrite H.
      + setoid_rewrite PCA.caseCombinatorCorrect0.
        destruct Hb as [_ Hb]. exact (Hb _ H').
      + setoid_rewrite PCA.caseCombinatorCorrectS.
        destruct Hc as [_ Hc]. exact (Hc _ H').
    - intros n A. exists (λ (n := n) &k). intro f.
      rewrite combinatoryCompleteness2. simpl.
      split; [exists k; reflexivity | ]. intros v [H _]. contradiction.
    - intros n A t.
      exists (λ (n := S n) ($ π * $(termRep t) ** PAS.idVec 1 * PAS.lastVar)).
      intro f.
      split; [apply combinatoryCompleteness1 | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      rewrite downSubstitutionLemma in Ha.
      set (x := HA.standardValuation t f). exists x.
      rewrite combinatoryCompleteness2'. simpl.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      setoid_rewrite PAS.idVecProductSubstitutionEq1'.
      rewrite termRepresentationCorrect. fold x. fold x in Ha.
      destruct (PCA.natRepresentationCombinatorDenotes x) as [x' Hx].
      rewrite Hx.
      split.
      + apply PCA.leftProjectionCombinatorCorrect.
      + setoid_rewrite PCA.rightProjectionCombinatorCorrect. exact Ha.
    - intros n A B.
      set (t := λ (x12 * ($ π1 * x22) * ($ π2 * x22))).
      exists (λ (n := n) $ t). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [ apply PCA.representationsDenote | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      split. {
        cutrewrite (t * &a  = t ** &&(();; a)); [ | reflexivity].
        apply PCA.combinatoryCompleteness1.
      }
      intros u Hb. destruct (realizersDenote Hb) as [b Hu]. rewrite Hu in *.
      clear dependent u.
      unfold t. rewrite PCA.combinatoryCompletenessInstance2. simpl.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      destruct Hb as [x [Hx Hb]]. rewrite Hx in *.
      simpl in Ha. specialize (Ha x). destruct Ha as [_ Ha].
      specialize (Ha _ Hb). apply upLemma in Ha. exact Ha.
    - intros n A B.
      set (t := λ (x13*x33*x23)).
      exists (λ (n := n) $ t). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [apply PCA.representationsDenote | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      split. {
        apply PAS.subTermDenotes with (v := t*&a*&a); [auto | ].
        cutrewrite (t * &a * &a  = t ** &&(();; a;; a)); [ | reflexivity].
        apply PCA.combinatoryCompleteness1.
      }
      intros u Hb. destruct (realizersDenote Hb) as [b Hu]. rewrite Hu in *.
      clear dependent u.
      simpl. intro x.
      destruct (PCA.natRepresentationCombinatorDenotes x) as [x' Hx].
      rewrite Hx in *.
      unfold t. rewrite PCA.combinatoryCompletenessInstance3. simpl.
      simpl in Ha. specialize (Ha x). destruct Ha as [_ Ha].
      setoid_rewrite upLemma in Ha.
      rewrite <- Hx. exact (Ha _ Hb).
    - intros n A t.
      exists (λ (n := S n) (PAS.lastVar * $(termRep t) ** PAS.idVec 1)).
      split; [apply combinatoryCompleteness1 | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      rewrite downSubstitutionLemma, combinatoryCompleteness2'. simpl.
      setoid_rewrite PAS.idVecProductSubstitutionEq1'.
      rewrite termRepresentationCorrect.
      apply Ha.
    - exists (λ (n := 1) &k).
      intros [f x]. destruct f.
      rewrite combinatoryCompleteness2. simpl.
      split; [ | exists k; reflexivity].
      simpl. reflexivity.
    - exists (λ (n := 2) &k).
      intros [[f x] y]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      simpl. split; [ | apply PCA.kaDenotes].
      simpl in *. congruence.
    - exists (λ (n := 3) &k).
      intros [[[f x] y] z]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      split; [apply PCA.kaDenotes | ].
      intros u [Hb [b Hub]]. rewrite Hub. clear dependent u.
      simpl. split; [ | eauto using PCA.kSpec].
      simpl in *. congruence.
    - exists (λ (n := 2) &k).
      intros [[f x] y]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      simpl. split; [ | apply PCA.kaDenotes].
      simpl in *. congruence.
    - exists (λ (n := 4) &k).
      intros [[[[f x1] x2] x3] x4]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      split; [apply PCA.kaDenotes | ].
      intros u [Hb [b Hub]]. rewrite Hub. clear dependent u.
      simpl. split; [ | eauto using PCA.kSpec].
      simpl in *. congruence.
    - exists (λ (n := 4) &k).
      intros [[[[f x1] x2] x3] x4]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      split; [apply PCA.kaDenotes | ].
      intros u [Hb [b Hub]]. rewrite Hub. clear dependent u.
      simpl. split; [ | eauto using PCA.kSpec].
      simpl in *. congruence.
    - exists (λ (n := 1) &k).
      intros [f x]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha _]. simpl in Ha. exfalso. intuition.
    - exists (λ (n := 2) &k).
      intros [[f x] y]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [exists k; reflexivity | ].
      intros u [Ha [a Hua]]. rewrite Hua. clear dependent u.
      simpl. split; [ | apply PCA.kaDenotes].
      simpl in *. congruence.
    - exists (λ (n := 1) &k).
      intros [f x]. destruct f.
      rewrite combinatoryCompleteness2. simpl.
      split; [ | exists k; reflexivity].
      simpl. auto.
    - exists (λ (n := 2) &k).
      intros [[f x] y]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [ | exists k; reflexivity].
      simpl. auto.
    - exists (λ (n := 1) &k).
      intros [f x]. destruct f.
      rewrite combinatoryCompleteness2. simpl.
      split; [ | exists k; reflexivity].
      simpl. auto.
    - exists (λ (n := 2) &k).
      intros [[f x] y]. destruct f.
      rewrite combinatoryCompleteness2.
      split; [ | exists k; reflexivity].
      simpl. auto.
    - intros n A.
      set (t := λ ($ ρ * x13 * x23 * x33)).
      exists (λ (n := n) $ t). intro f.
      rewrite combinatoryCompleteness2.
      setoid_rewrite PAS.closedTermSubstitutionLemma0.
      split; [ apply PCA.representationsDenote | ].
      intros u Ha. destruct (realizersDenote Ha) as [a Hu]. rewrite Hu in *.
      clear dependent u.
      split. {
        apply PAS.subTermDenotes with (v := t*&a*&a); [auto | ].
        cutrewrite (t * &a * &a  = t ** &&(();; a;; a)); [ | reflexivity].
        apply PCA.combinatoryCompleteness1.
      }
      intros u Hb. destruct (realizersDenote Hb) as [b Hu]. rewrite Hu in *.
      clear dependent u.
      simpl. intro x.
      destruct (PCA.natRepresentationCombinatorDenotes x) as [x' Hx].
      rewrite Hx in *.
      unfold t. rewrite PCA.combinatoryCompletenessInstance3. simpl.
      setoid_rewrite PAS.closedTermSubstitutionLemma0. rewrite <- Hx.
      clear dependent x'.
      induction x as [ | x IHx].
      + setoid_rewrite PCA.primitiveRecursionCombinatorCorrect0.
        rewrite downSubstitutionLemma in Ha. exact Ha.
      + setoid_rewrite PCA.primitiveRecursionCombinatorCorrectS.
        destruct (realizersDenote IHx) as [c Hc]. rewrite Hc in *.
        simpl in Hb. specialize (Hb x). destruct Hb as [_ Hb].
        specialize (Hb _ IHx).
        setoid_rewrite lastSubstitutionLemma in Hb. exact Hb.
  Qed.

  Module NOTATIONS.

    Delimit Scope PCA_REL with PCA_REL.

    Notation "## f" := ##f (at level 6, right associativity) : PCA_REL.
    Notation termRep := termRep.

  End NOTATIONS.

End PCA_REL.
