(**
* Rewriting with K and S
*)

Local Ltac inj_subst H := injection H; intros; subst; clear H.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Require Import rewriting.

Import RW.NOTATIONS.

Module KS_RW.

  (**
  ** Definitions
  *)

  (**
  *** Terms
  *)

  Inductive term :=
  | K    : term
  | S    : term
  | appl : term -> term -> term.
  Local Infix "⋅" := appl (at level 40, left associativity).

  (**
  *** Non-deterministic reduction
  *)

  Local Reserved Infix ">" (at level 70).
  Inductive OneStepReduces : term -> term -> Prop :=
  | oneStepReducesK U V    : K⋅U⋅V > U
  | oneStepReducesS U V W  : S⋅U⋅V⋅W > U⋅W⋅(V⋅W)
  | oneStepReducesL U U' V : U > U' -> U⋅V > U'⋅V
  | oneStepReducesR U V V' : V > V' -> U⋅V > U⋅V'
  where "U > V" := (OneStepReduces U V).

  Definition Reduces := RTC OneStepReduces.
  Local Infix ">*" := Reduces (at level 70).

  (**
  *** Convertibility
  *)

  Definition Convertible (U V : term) : Prop := exists W, U >* W /\ V >* W.
  Local Infix "≈" := Convertible (at level 70).

  (**
  *** Deterministic eager reduction
  *)

  Fixpoint eagerReduct (T : term) : option term :=
  match T with
  | K
  | S   => None
  | U⋅V => match eagerReduct U, eagerReduct V with
           | Some U,      _ => Some (U⋅V)
           |   None, Some V => Some (U⋅V)
           |   None,   None => match T with
                               | K⋅U⋅V   => Some U
                               | S⋅U⋅V⋅W => Some (U⋅W⋅(V⋅W))
                               | _       => None
                               end
           end
  end.

  Definition EagerlyOneStepReduces (U V : term) : Prop :=
    eagerReduct U = Some V.
  Local Infix ">>" := EagerlyOneStepReduces (at level 70).

  Definition EagerlyReduces : term -> term -> Prop :=
    RTC (fun U V : term => U >> V).
  Infix ">>*" := EagerlyReduces (at level 70).

  (**
  *** Normal terms and normal forms
  *)

  Notation Normal := (RW.Normal OneStepReduces).

  Local Notation NF := (NF OneStepReduces).

  Definition StrictlyNormal (T : term) := eagerReduct T = None.
  Local Notation SN := StrictlyNormal.

  Definition StrictNormalForm (U V : term) : Prop := U >>* V /\ SN V.
  Local Notation SNF := StrictNormalForm.

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Delimit Scope KS_RW with KS_RW.

    Infix "⋅" := appl : KS_RW.
    Infix ">" := (fun U V => U > V) (at level 70) : KS_RW.
    Infix ">*" := (fun U V => U >* V) (at level 70) : KS_RW.
    Infix ">>" := (fun U V => U >> V) (at level 70) : KS_RW.
    Infix ">>*" := (fun U V => U >>* V) (at level 70) : KS_RW.
    Infix "≈" := (fun U V => U ≈ V) (at level 70) : KS_RW.
    Notation Normal := Normal.
    Notation NF := NF.
    Notation SNF := SNF.

  End NOTATIONS.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    (**
    *** Convertibility is an equivalence relation
    *)

    Declare Instance convertibleEquivalence : Equivalence Convertible.

    (**
    *** Application respects convertibility
    *)

    Declare Instance applRespectsConvertibility :
      Proper (Convertible ==> Convertible ==> Convertible) appl.

    (**
    *** Normal forms respects convertibility
    *)

    Declare Instance normalFormsRespectConvertibility :
      Proper (Convertible ==> eq ==> iff) NF.

    (**
    *** Induction principle for eager reduction
    *)

    Axiom eagerReductionInduction :
      forall P : term -> term -> Prop,
      (forall U U' V : term, P U U' -> P (U⋅V) (U'⋅V)) ->
      (forall U V V' : term, SN U -> P V V' -> P (U⋅V) (U⋅V')) ->
      (forall U V : term, SN U -> SN V -> P (K⋅U⋅V) U) ->
      (forall U V W : term, SN U -> SN V -> SN W -> P (S⋅U⋅V⋅W) (U⋅W⋅(V⋅W))) ->
      forall U V : term, U >> V -> P U V.

    (**
    *** Induction principle for normal terms
    *)

    Axiom normalTermInduction :
      forall P : term -> Prop,
      P K ->
      P S ->
      (forall T : term, Normal T -> P T -> P (K⋅T)) ->
      (forall T : term, Normal T -> P T -> P (S⋅T)) ->
      (forall U V : term, Normal U -> Normal V -> P U -> P V -> P (S⋅U⋅V)) ->
      forall T : term, Normal T -> P T.

    Axiom strictlyNormalTermInduction :
      forall P : term -> Prop,
      P K ->
      P S ->
      (forall T : term, SN T -> P T -> P (K⋅T)) ->
      (forall T : term, SN T -> P T -> P (S⋅T)) ->
      (forall U V : term, SN U -> SN V -> P U -> P V -> P (S⋅U⋅V)) ->
      forall T : term, SN T -> P T.

    (**
    *** Relations between reduction relations
    *)

    Axiom eagerlyOneStepReduces_oneStepReduces :
      forall U V : term, U >> V -> U > V.

    Axiom eagerlyReduces_reduces : forall U V : term, U >>* V -> U >* V.

    (**
    *** Properties of reduction
    *)

    Axiom reductionL : forall U U' V : term, U >* U' -> U⋅V >* U'⋅V.

    Axiom reductionR : forall U V V' : term,  V >* V' -> U⋅V >* U⋅V'.

    Axiom reductionPar :
      forall U V U' V' : term,  U >* U' -> V >* V' -> U⋅V >* U'⋅V'.

    (**
    *** Properties of eager reduction
    *)

    Axiom eagerOneStepReductionFunctional : RW.Functional EagerlyOneStepReduces.

    Axiom eagerReductionL : forall U U' V : term, U >>* U' -> U⋅V >>* U'⋅V.

    Axiom eagerReductionR :
      forall U V V' : term, SN U -> V >>* V' -> U⋅V >>* U⋅V'.

    Axiom eagerReductionPar :
      forall U U' V V' : term, SN U' -> U >>* U' -> V >>* V' -> U⋅V >>* U'⋅V'.

    (**
    *** Reduction relations are confluent
    *)

    Axiom reductionConfluent : RW.Confluence OneStepReduces.

    Axiom eagerReductionConfluent : RW.Confluence EagerlyOneStepReduces.

    (**
    *** Definition of strict normal terms is correct
    *)

    Axiom strictlyNormalCorrect :
      forall T : term, SN T <-> RW.Normal EagerlyOneStepReduces T.

    Axiom strictNormalFormsCorrect :
      forall U V : term, SNF U V <-> RW.NormalForm EagerlyOneStepReduces U V.

    (**
    *** Properties of normal terms
    *)

    Axiom normalIffStrictlyNormal : forall T, Normal T <-> SN T.

    Axiom strictNormalForm_normalForm : forall U V : term, SNF U V -> NF U V.

    Axiom normalApplL : forall U V : term, Normal (U⋅V) -> Normal U.

    Axiom strictlyNormalApplL : forall U V : term, SN (U⋅V) -> SN U.

    Axiom normalApplR : forall U V : term, Normal (U⋅V) -> Normal V.

    Axiom strictlyNormalApplR : forall U V : term, SN (U⋅V) -> SN V.

    Axiom normalReduction : forall U V : term, Normal U -> U >* V -> U = V.

    Axiom strictlyNormalEagerReduction :
      forall U V : term, SN U -> U >>* V -> U = V.

    Axiom strictNormalFormApplL :
      forall U V W : term, SNF (U⋅V) W -> exists U' : term, SNF U U'.

    Axiom strictNormalFormApplR :
      forall U V W : term, SNF (U⋅V) W -> exists V' : term, SNF V V'.

    Axiom normalFormsUnique :
      forall U V V' : term,  NF U V -> NF U V' -> V = V'.

    Axiom strictNormalFormsUnique :
      forall U V W : term, SNF U V -> SNF U W -> V = W.

    (**
    *** Normal terms
    *)

    Axiom kNormal : Normal K.

    Axiom kStrictlyNormal : SN K.

    Axiom ktNormal : forall T : term, Normal T -> Normal (K⋅T).

    Axiom ktStrictlyNormal : forall T : term, SN T -> SN (K⋅T).

    Axiom sNormal : Normal S.

    Axiom sStrictlyNormal : SN S.

    Axiom stNormal : forall T : term, Normal T -> Normal (S⋅T).

    Axiom stStrictlyNormal : forall T : term, SN T -> SN (S⋅T).

    Axiom suvNormal :
      forall U V : term,  Normal U -> Normal V -> Normal (S⋅U⋅V).

    Axiom suvStrictlyNormal : forall U V : term, SN U -> SN V -> SN (S⋅U⋅V).

    Axiom kuvNotStrictlyNormal : forall U V : term, ~ SN (K⋅U⋅V).

    Axiom suvwNotStrictlyNormal : forall U V W : term, ~ SN (S⋅U⋅V⋅W).

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Theorem strictlyNormalApplL (U V : term) : SN (U⋅V) -> SN U.
    Proof.
      intro H.
      remember (eagerReduct U) as rU eqn:HU. symmetry in HU.
      unfold SN in H. simpl in H.
      destruct rU as [U' | ]; rewrite HU in H.
      - discriminate H.
      - exact HU.
    Qed.

    Theorem strictlyNormalApplR (U V : term) : SN (U⋅V) -> SN V.
    Proof.
      intro H.
      remember (eagerReduct U) as rU eqn:HU.
      remember (eagerReduct V) as rV eqn:HV.
      symmetry in HU, HV. unfold SN in H. simpl in H.
      destruct rU as [U' | ]; rewrite HU in H.
      - discriminate H.
      - destruct rV as [V' | ].
        + rewrite HV in H. discriminate H.
        + exact HV.
    Qed.

    Theorem eagerReductionInduction (P : term -> term -> Prop) :
      (forall U U' V : term, P U U' -> P (U⋅V) (U'⋅V)) ->
      (forall U V V' : term, SN U -> P V V' -> P (U⋅V) (U⋅V')) ->
      (forall U V : term, SN U -> SN V -> P (K⋅U⋅V) U) ->
      (forall U V W : term, SN U -> SN V -> SN W -> P (S⋅U⋅V⋅W) (U⋅W⋅(V⋅W))) ->
      forall U V : term, U >> V -> P U V.
    Proof.
      intros HL HR HK HS T.
      induction T as [ | | U IHU V IHV]; [discriminate | discriminate | ].
      remember (eagerReduct U) as rU eqn:HU. symmetry in HU.
      destruct rU as [U' | ].
      - intros W H.
        unfold EagerlyOneStepReduces in H. simpl in H. rewrite HU in H.
        injection H. intro H'. subst.
        apply HL. apply IHU. exact HU.
      - remember (eagerReduct V) as rV eqn:HV. symmetry in HV.
        destruct rV as [V' | ].
        + intros W H.
          unfold EagerlyOneStepReduces in H. simpl in H. rewrite HU, HV in H.
          injection H. intro H'. subst. apply HR.
          * exact HU.
          * apply IHV. exact HV.
        + intros W H.
          unfold EagerlyOneStepReduces in H. simpl in H. rewrite HU, HV in H.
          refine
            (match U as U' return (U' = U -> _) with
             | K       => _
             | S       => _
             | K⋅U'    => _
             | S⋅_     => _
             | K⋅_⋅_   => _
             | S⋅U'⋅V' => _
             | _⋅_⋅_⋅_ => _
             end _).
          * intro H'. subst. inversion H.
          * intro H'. subst. inversion H.
          * intro H'. subst. injection H. intro H'. subst.
            apply strictlyNormalApplR in HU. apply HK; assumption.
          * intro H'. subst. inversion H.
          * intro H'. subst. inversion H.
          * intro H'. subst. injection H. intro H'. subst.
            pose proof (strictlyNormalApplR _ _ HU) as HV'.
            apply strictlyNormalApplL, strictlyNormalApplR in HU.
            apply HS; assumption.
          * intro H'. subst. inversion H.
          * reflexivity.
    Qed.

    Theorem eagerOneStepReductionFunctional :
      RW.Functional EagerlyOneStepReduces.
    Proof.
      unfold EagerlyOneStepReduces.
      intros U V W HUV HUW. rewrite HUV in HUW. injection HUW. tauto.
    Qed.

    Theorem eagerReductionConfluent : RW.Confluence EagerlyOneStepReduces.
    Proof.
      apply RW.THMS.functionalRelation_confluence.
      apply eagerOneStepReductionFunctional.
    Qed.

    Theorem eagerlyOneStepReduces_oneStepReduces (U V : term) : U >> V -> U > V.
    Proof.
      intro HUV.
      induction HUV as [U U' V IH | U V V' _ IH | U V _ _ | U V W _ _ _ ]
        using eagerReductionInduction.
      - apply oneStepReducesL. exact IH.
      - apply oneStepReducesR. exact IH.
      - apply oneStepReducesK.
      - apply oneStepReducesS.
    Qed.

    Theorem eagerlyReduces_reduces (U V : term) : U >>* V -> U >* V.
    Proof.
      intro H. induction H as [U V | T | U V W _ IHL _ IHR].
      - apply rt_step. apply eagerlyOneStepReduces_oneStepReduces. exact H.
      - apply rt_refl.
      - apply rt_trans with (y := V); assumption.
    Qed.

    Theorem strictlyNormalCorrect (T : term) :
      SN T <-> RW.Normal EagerlyOneStepReduces T.
    Proof.
      unfold RW.Normal, EagerlyOneStepReduces, SN.
      split.
      - intros H [T' H']. rewrite H' in H. discriminate H.
      - intros H. destruct (eagerReduct T) as [T' | T'].
        + exfalso. eauto.
        + reflexivity.
    Qed.

    Theorem strictNormalFormsCorrect (U V : term) :
      SNF U V <-> RW.NormalForm EagerlyOneStepReduces U V.
    Proof.
      split.
      - intros [H HV]. split; [exact H | ]. clear U H. intros [W H].
        unfold SN in HV. unfold EagerlyOneStepReduces in H.
        rewrite HV in H. discriminate H.
      - intros [H HV]. split; [exact H | ]. clear U H.
        unfold SN.
        set (W' := eagerReduct V). remember W' as W eqn:HW.
        destruct W as [W | ]; subst.
        + exfalso. apply HV. unfold EagerlyOneStepReduces. eauto.
        + reflexivity.
    Qed.

    Theorem strictNormalFormsUnique (U V W : term) :
      SNF U V -> SNF U W -> V = W.
    Proof.
      intros H H'.
      apply strictNormalFormsCorrect in H.
      apply strictNormalFormsCorrect in H'.
      eapply (RW.THMS.confluence_normalFormsUnique _ eagerReductionConfluent);
      eauto.
    Qed.

    Theorem normalApplL (U V : term) : Normal (U⋅V) -> Normal U.
    Proof. intros H [T HT]. eauto using OneStepReduces. Qed.

    Theorem normalApplR (U V : term) : Normal (U⋅V) -> Normal V.
    Proof. intros H [T HT]. eauto using OneStepReduces. Qed.

    Theorem normalReduction (U V : term) : Normal U -> U >* V -> U = V.
    Proof.
      intros H H'.
      induction H' as [U V H' | U H' | U V W _ IHL _ IHR].
      - exfalso. eauto.
      - reflexivity.
      - specialize (IHL H). subst. exact (IHR H).
    Qed.

    Theorem strictlyNormalEagerReduction (U V : term) :
      SN U -> U >>* V -> U = V.
    Proof.
      rewrite strictlyNormalCorrect. apply RW.THMS.normalReductionTrivial.
    Qed.

    Theorem kuvNotStrictlyNormal (U V : term) : ~ SN (K⋅U⋅V).
    Proof.
      intro H.
      remember (eagerReduct U) as rU eqn:HU.
      remember (eagerReduct V) as rV eqn:HV.
      symmetry in HU, HV. unfold SN in H. simpl in H.
      destruct rU as [U' | ]; rewrite HU in H.
      - discriminate H.
      - destruct rV as [V' | ]; rewrite HV in H; discriminate H.
    Qed.

    Theorem suvwNotStrictlyNormal (U V W : term) : ~ SN (S⋅U⋅V⋅W).
    Proof.
      intro H.
      remember (eagerReduct U) as rU eqn:HU.
      remember (eagerReduct V) as rV eqn:HV.
      remember (eagerReduct W) as rW eqn:HW.
      symmetry in HU, HV, HW. unfold SN in H. simpl in H.
      destruct rU as [U' | ]; rewrite HU in H.
      - discriminate H.
      - destruct rV as [V' | ]; rewrite HV in H.
        + discriminate H.
        + destruct rW as [W' | ]; rewrite HW in H; discriminate.
    Qed.

    Theorem normalIffStrictlyNormal (T : term) : Normal T <-> SN T.
    Proof.
      split.
      - intro H. remember (eagerReduct T) as r eqn:Hr. symmetry in Hr.
        destruct r as [T' | ].
        + exfalso. apply H. exists T'.
          apply eagerlyOneStepReduces_oneStepReduces. exact Hr.
        + exact Hr.
      - intros HT [T' H]. induction H as [ | | U U' V _ IH | U V V' _ IH].
        + apply (kuvNotStrictlyNormal _ _ HT).
        + apply (suvwNotStrictlyNormal _ _ _ HT).
        + apply IH. eapply strictlyNormalApplL. eauto.
        + apply IH. eapply strictlyNormalApplR. eauto.
    Qed.

    Theorem strictNormalFormApplL (U V W : term) :
      SNF (U⋅V) W -> exists U' : term, SNF U U'.
    Proof.
      intros [H HW]. remember (U⋅V) as T eqn:HT.
      revert U V HT.
      setoid_rewrite clos_rt_rt1n_iff in H.
      induction H as [T | T' T W HUVT HTW IH]; intros U V HT; subst.
      - exists U. split.
        + apply rt_refl.
        + eapply strictlyNormalApplL. eauto.
      - setoid_rewrite <- clos_rt_rt1n_iff in HTW. specialize (IH HW).
        remember (eagerReduct U) as U' eqn:HU.
        unfold EagerlyOneStepReduces in HUVT.
        destruct U' as [U' | ].
        + simpl in HUVT. rewrite <- HU in HUVT.
          injection HUVT. intro H. subst.
          specialize (IH U' V).
          destruct IH as [U'' [IH HU'']]; [reflexivity | ].
          exists U''. split; [ | exact HU'']. apply rt_trans with (y := U').
          * apply rt_step. symmetry. exact HU.
          * exact IH.
        + symmetry in HU. exists U. split.
          * apply rt_refl.
          * exact HU.
    Qed.

    Theorem strictNormalFormApplR (U V W : term) :
      SNF (U⋅V) W -> exists V' : term, SNF V V'.
    Proof.
      intros [H HW]. remember (U⋅V) as T eqn:HT.
      revert U V HT.
      setoid_rewrite clos_rt_rt1n_iff in H.
      induction H as [T | T' T W HUVT HTW IH]; intros U V HT; subst.
      - exists V. split.
        + apply rt_refl.
        + eapply strictlyNormalApplR. eauto.
      - setoid_rewrite <- clos_rt_rt1n_iff in HTW. specialize (IH HW).
        remember (eagerReduct U) as U' eqn:HU.
        remember (eagerReduct V) as V' eqn:HV.
        unfold EagerlyOneStepReduces in HUVT.
        destruct U' as [U' | ]; [ | destruct V' as [V' | ]].
        + simpl in HUVT. rewrite <- HU in HUVT.
          injection HUVT. intro H. subst.
          eapply IH. eauto.
        + simpl in HUVT. rewrite <- HU, <- HV in HUVT.
          injection HUVT. intro H. subst.
          specialize (IH U V').
          destruct IH as [V'' [IH HV'']]; [reflexivity | ].
          exists V''. split; [ | exact HV'']. apply rt_trans with (y := V').
          * apply rt_step. symmetry. exact HV.
          * exact IH.
        + symmetry in HV. exists V. split.
          * apply rt_refl.
          * exact HV.
    Qed.

    Theorem strictNormalForm_normalForm (U V : term) : SNF U V -> NF U V.
    Proof.
      firstorder using normalIffStrictlyNormal, eagerlyReduces_reduces.
    Qed.

    Theorem normalTermInduction (P : term -> Prop) :
      P K ->
      P S ->
      (forall T : term, Normal T -> P T -> P (K⋅T)) ->
      (forall T : term, Normal T -> P T -> P (S⋅T)) ->
      (forall U V : term, Normal U -> Normal V -> P U -> P V -> P (S⋅U⋅V)) ->
      forall T : term, Normal T -> P T.
    Proof.
      assert (forall T U V W, ~ Normal (T⋅U⋅V⋅W)) as lemma. {
        clear. intro T.
        induction T as [ | | U IHU V _].
        - intros U V W H. apply H. exists (U⋅W). constructor. constructor.
        - intros U V W H. apply H. eexists. constructor.
        - intros W U' V' H. apply (IHU V W U'). eapply normalApplL. eauto.
      }
      intros HK HS HKU HSU HSUV T.
      refine
        ((fix IH T :=
         match T as T' return (T = T' -> Normal T ->  P T) with
         | K       => _
         | S       => _
         | K⋅T     => _
         | S⋅T     => _
         | K⋅U⋅V   => _
         | S⋅U⋅V   => _
         | _⋅_⋅_⋅_ => _
         end _) T).
      - intros H _. subst. apply HK.
      - intros H _. subst. apply HS.
      - intros H' H. subst.
        pose proof (normalApplR _ _ H) as HV.
        apply (HKU _ HV). apply (IH _ HV).
      - intros H' H. subst.
        pose proof (normalApplR _ _ H) as HV.
        apply (HSU _ HV). apply (IH _ HV).
      - intros H' H. subst. exfalso. apply H. exists U. constructor.
      - intros H' H. subst.
        pose proof (normalApplL _ _ H) as HU. apply normalApplR in HU.
        pose proof (normalApplR _ _ H) as HV.
        apply (HSUV _ _ HU HV).
        + apply (IH _ HU).
        + apply (IH _ HV).
      - intros H' H. subst. exfalso. eapply lemma. eauto.
      - reflexivity.
    Qed.

    Theorem strictlyNormalTermInduction (P : term -> Prop) :
      P K ->
      P S ->
      (forall T : term, SN T -> P T -> P (K⋅T)) ->
      (forall T : term, SN T -> P T -> P (S⋅T)) ->
      (forall U V : term, SN U -> SN V -> P U -> P V -> P (S⋅U⋅V)) ->
      forall T : term, SN T -> P T.
    Proof.
      setoid_rewrite <- normalIffStrictlyNormal. apply normalTermInduction.
    Qed.

    Theorem eagerReductionL (U U' V : term) : U >>* U' -> U⋅V >>* U'⋅V.
    Proof.
      intros H. induction H as [U U' H | U | U T U' _ IHL _ IHR].
      - apply rt_step.
        unfold EagerlyOneStepReduces. simpl. rewrite H.
        reflexivity.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    Theorem eagerReductionR (U V V' : term) : SN U -> V >>* V' -> U⋅V >>* U⋅V'.
    Proof.
      intros HU H. induction H as [V V' H | V | V T V' _ IHL _ IHR].
      - apply rt_step.
        unfold EagerlyOneStepReduces. simpl. rewrite HU, H.
        reflexivity.
      - apply rt_refl.
      - eapply rt_trans; eauto.
    Qed.

    Theorem eagerReductionPar (U U' V V' : term) :
      SN U' -> U >>* U' -> V >>* V' -> U⋅V >>* U'⋅V'.
    Proof.
      intros HU' HU HV. apply rt_trans with (y := U'⋅V).
      - apply eagerReductionL. exact HU.
      - apply eagerReductionR; assumption.
    Qed.

    Theorem reductionL (U U' V : term) : U >* U' -> U⋅V >* U'⋅V.
    Proof.
      intro H. induction H as [U U' | U | U W U' HL IHL HR IHR].
      - apply rt_step. constructor. assumption.
      - apply rt_refl.
      - apply rt_trans with (y := W⋅V); assumption.
    Qed.

    Theorem reductionR (U V V' : term) :  V >* V' -> U⋅V >* U⋅V'.
    Proof.
      intro H. induction H as [V V' | V | V W V' HL IHL HR IHR].
      - apply rt_step. constructor. assumption.
      - apply rt_refl.
      - apply rt_trans with (y := U⋅W); assumption.
    Qed.

    Theorem reductionPar (U V U' V' : term) :
      U >* U' -> V >* V' -> U⋅V >* U'⋅V'.
    Proof.
      intros HU HV.
      apply rt_trans with (y := U'⋅V);
      [apply reductionL | apply reductionR]; assumption.
    Qed.

    Theorem kStrictlyNormal : SN K.
    Proof. reflexivity. Qed.

    Theorem kNormal : Normal K.
    Proof. apply normalIffStrictlyNormal, kStrictlyNormal. Qed.

    Theorem ktStrictlyNormal (T : term) : SN T -> SN (K⋅T).
    Proof. unfold StrictlyNormal. simpl. intro H. rewrite H. reflexivity. Qed.

    Theorem ktNormal (T : term) : Normal T -> Normal (K⋅T).
    Proof. setoid_rewrite normalIffStrictlyNormal. apply ktStrictlyNormal. Qed.

    Theorem sStrictlyNormal : SN S.
    Proof. reflexivity. Qed.

    Theorem sNormal : Normal S.
    Proof. apply normalIffStrictlyNormal, sStrictlyNormal. Qed.

    Theorem stStrictlyNormal (T : term) : SN T -> SN (S⋅T).
    Proof. unfold StrictlyNormal. simpl. intro H. rewrite H. reflexivity. Qed.

    Theorem stNormal (T : term) : Normal T -> Normal (S⋅T).
    Proof. setoid_rewrite normalIffStrictlyNormal. apply stStrictlyNormal. Qed.

    Theorem suvStrictlyNormal (U V : term) : SN U -> SN V -> SN (S⋅U⋅V).
    Proof.
      unfold SN. simpl. intros H H'. rewrite H, H'. reflexivity.
    Qed.

    Theorem suvNormal (U V : term) : Normal U -> Normal V -> Normal (S⋅U⋅V).
    Proof. setoid_rewrite normalIffStrictlyNormal. apply suvStrictlyNormal. Qed.

    Local Reserved Infix ">=" (at level 70).
    Inductive OneStepReflParReduces : term -> term -> Prop :=
    | oneStepReflParReducesK    U V       : K⋅U⋅V >= U
    | oneStepReflParReducesS    U V W     : S⋅U⋅V⋅W >= U⋅W⋅(V⋅W)
    | oneStepReflParReducesRefl U         : U >= U
    | oneStepReflParReducesPar  U U' V V' : U >= U' -> V >= V' -> U⋅V >= U'⋅V'
    where "U >= V" := (OneStepReflParReduces U V).

    Definition ReflParReduces := RTC OneStepReflParReduces.
    Local Infix ">=*" := ReflParReduces (at level 70).

    Lemma inclusion1 (U V : term) : U > V -> U >= V.
    Proof. intro H. induction H; auto using OneStepReflParReduces. Qed.

    Lemma inclusion2 (U V : term) : U >= V -> U >* V.
    Proof.
      intro H. induction H as [V T | U V W | V | U U' V V' HL IHL HR IHR].
      - apply rt_step. constructor.
      - apply rt_step. constructor.
      - apply rt_refl.
      - apply rt_trans with (y := U'⋅V);
        [apply reductionL | apply reductionR]; assumption.
    Qed.

    Lemma redEqReflParRed (U V : term) : U >* V <-> U >=* V.
    Proof.
      split.
      - apply RW.THMS.rtcIncreasing. apply inclusion1.
      - intros H.
        induction H as [U V H | U | U W V _ IHL _ IHR].
        + apply inclusion2. assumption.
        + apply rt_refl.
        + apply rt_trans with (y := W); assumption.
    Qed.

    Lemma dpOneStepReflParReduces : DP OneStepReflParReduces.
    Proof.
      (* redundant cases *)
      assert (forall T U V, K⋅T >= U -> exists W, T >= W /\ U⋅V >= W) as case1.
      {
        intros T U V H. inversion_clear H.
        - eauto using OneStepReflParReduces.
        - inversion_clear H0. eauto using OneStepReflParReduces.
      }
      assert
        (forall U V W U' V',
         S⋅U⋅V >= U' -> W >= V' -> exists W', U⋅W⋅(V⋅W) >= W' /\ U'⋅V' >= W')
      as case2. {
        intros U V W U' V' HL HR. remember (S⋅U⋅V) as SUv eqn:HSUV.
        destruct HL as [U'' V'' | U'' V'' W'' | T | U'' U''' V'' V''' HL' HR'].
        - inversion HSUV.
        - discriminate HSUV.
        - subst. eauto 6 using OneStepReflParReduces.
        - inj_subst HSUV. inversion_clear HL'.
          + eauto 6 using OneStepReflParReduces.
          + inversion_clear H. eauto 6 using OneStepReflParReduces.
      }
      (* the proof *)
      intros T U V H. generalize dependent V.
      induction H as [U V | U V W | T | U U' V V' HL IHL HR IHR].
      - remember (K⋅U⋅V) as T eqn:HT.
        intros W H.
        destruct H as [U' V' | U' V' W' | T | U'' U' V'' V' H' H'' ].
        + inj_subst HT. eauto using OneStepReflParReduces.
        + inversion HT.
        + subst. eauto using OneStepReflParReduces.
        + inj_subst HT. apply (case1 _ _ _ H').
      - remember (S⋅U⋅V⋅W) as T eqn:HT.
        intros T' H.
        destruct H as [U' V' | U' V' W' | T | U'' U' V'' V' H' H''].
        + inversion HT.
        + inj_subst HT. eauto using OneStepReflParReduces.
        + subst. eauto using OneStepReflParReduces.
        + inj_subst HT. apply (case2 _ _ _ _  _ H' H'').
      - eauto using OneStepReflParReduces.
      - remember (U⋅V) as T eqn:HT.
        intros T' H.
        destruct H as [U'' V'' | U'' V'' W'' | T | U''' U'' V''' V'' HL' HR'].
        + inj_subst HT. pose proof (case1 _ _ V' HL). firstorder.
        + inj_subst HT. pose proof (case2 _ _ _ _ _ HL HR). firstorder.
        + subst. eauto using OneStepReflParReduces.
        + inj_subst HT.
          destruct
            (IHL _ HL') as [U''' [H H']],
            (IHR _ HR') as [V''' [H'' H''']].
          eauto using OneStepReflParReduces.
    Qed.

    Theorem reductionConfluent : RW.Confluence OneStepReduces.
    Proof.
      cut (DP ReflParReduces).
      + intros H U V V' H' H''.
        apply redEqReflParRed in H'.
        apply redEqReflParRed in H''.
        destruct (H _ _ _ H' H'') as [W [H''' H4]].
        apply redEqReflParRed in H'''.
        apply redEqReflParRed in H4.
        eauto.
      + apply RW.THMS.dp_confluence. apply dpOneStepReflParReduces.
    Qed.

    Theorem normalFormsUnique (U V V' : term) : NF U V -> NF U V' -> V = V'.
    Proof.
      intros H H'.
      eapply (RW.THMS.confluence_normalFormsUnique _ reductionConfluent); eauto.
    Qed.

    Instance convertibleEquivalence : Equivalence Convertible.
    Proof.
      split.
        - intro T. exists T. split; apply rt_refl.
        - firstorder.
        - intros U V w [U' [HUV HVU] [V' [HVW HWV]]].
          destruct (reductionConfluent _ _ _ HVU HVW) as [W' [HU'W' HV'W']].
          exists W'. split; eapply rt_trans; eauto.
    Qed.

    Instance normalFormsRespectConvertibility :
      Proper (Convertible ==> eq ==> iff) NF.
    Proof.
      assert (forall U V W, U ≈ V -> NF U W -> NF V W) as H. {
        intros U V W [T [HUT HVT]] [HUW HW].
        destruct (reductionConfluent _ _ _ HUT HUW) as [W' [HTW' HWW']].
        apply (normalReduction _ _ HW) in HWW'. subst. split.
        - eapply rt_trans; eauto.
        - exact HW.
      }
      intros U V HUV W' W HW. subst.
      split; [ | symmetry in HUV]; apply H; exact HUV.
    Qed.

    Instance applRespectsConvertibility :
      Proper (Convertible ==> Convertible ==> Convertible) appl.
    Proof.
      intros U U' [U'' [HU HU']] V V' [V'' [HV HV']]. exists (U''⋅V'').
      split; apply reductionPar; assumption.
    Qed.

  End THMS.

End KS_RW.
