(**
* Partial combinatory algebra based on normal KS-terms
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.

Require Import fin.
Require Import ksrewriting.
Require Import pas.
Require Import pca.
Require Import rewriting.

Import KS_RW.
Import KS_RW.NOTATIONS.
Import KS_RW.THMS.
Import PAS.NOTATIONS.
Import PCA.NOTATIONS.

Local Open Scope PAS.
Local Open Scope KS_RW.

Module NORMAL_TERM_PCA.

  (**
  ** Definitions
  *)

  Definition normalTerm := {t : term | StrictlyNormal t}.

  Definition K : normalTerm := exist _ _ kStrictlyNormal.
  Definition S : normalTerm := exist _ _ sStrictlyNormal.

  Definition normalTermToTerm (T : normalTerm) : term := proj1_sig T.
  Local Coercion normalTermToTerm : normalTerm >-> term.

  Definition NormalTermEq (U V : normalTerm) := (U : term) = (V : term).

  Instance normalTermEqEquivalence : Equivalence NormalTermEq.
  Proof. unfold NormalTermEq. split; congruence. Qed.

  Instance normalTermSetoid : Setoid normalTerm := {equiv := NormalTermEq}.

  Definition Appl (U V W : normalTerm) : Prop := U⋅V >>* W.

  Fixpoint closedPasTermToTerm `{_ : PAS.Pas normalTerm} (t : PAS.term 0)
    : term :=
  match t with
  | &a        => let (a, _) := a in a
  | PAS.var x => False_rect _ (FIN.THMS.t0Empty x)
  | u*v       => closedPasTermToTerm u ⋅ closedPasTermToTerm v
  end.
  Local Notation "§ t" := (closedPasTermToTerm t) (at level 6).

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Delimit Scope NT_PCA with NT_PCA.

    Notation "§ t" := (§t) (at level 6) : NT_PCA.

  End NOTATIONS.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    Declare Instance pas : PAS.Pas normalTermSetoid Appl.

    Declare Instance pca : PCA.Pca pas K S.

    Axiom nonTriviality : PCA.NonTrivial pca.

    Axiom closedPasTermDenotation :
      forall (u : PAS.term 0) (T : normalTerm), u ≃ &T <-> §u >>* T.

    Axiom eagerlyReduces_closedPasTermEq :
      forall u v : PAS.term 0, §u >>* §v -> u ≃ v.

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Instance pas : PAS.Pas normalTermSetoid Appl.
    Proof.
      split.
      - unfold Appl. congruence.
      - unfold Appl.
        intros [U HU] [V HV] [W HW] [W' HW'] H H'. simpl in *.
        unfold NormalTermEq. simpl.
        eapply strictNormalFormsUnique; unfold SNF; eauto.
    Qed.

    Theorem closedPasTermDenotation (u : PAS.term 0) (T : normalTerm) :
      u ≃ &T <-> §u >>* T.
    Proof.
      revert T. induction u as [U | x | u IHu v IHv]; intro T.
      - assert (&U ≃ &T <-> U == T) as H. {
          split; intro H.
          - apply PAS.THMS.constInjective. exact H.
          - rewrite H. reflexivity.
        }
        rewrite H. clear H. simpl. destruct U as [U HU], T as [T HT].
        unfold NormalTermEq. simpl. split; intro H.
        + rewrite H. apply rt_refl.
        + apply strictlyNormalEagerReduction; assumption.
      - contradiction.
      - split; intro H.
        + apply PAS.THMS.correctness1 in H. destruct H as [U [V [Hu [Hv H]]]].
          unfold Appl in H. simpl.
          specialize (IHu U). destruct IHu as [IHu _]. specialize (IHu Hu).
          specialize (IHv V). destruct IHv as [IHv _]. specialize (IHv Hv).
          clear Hu Hv. apply rt_trans with (y := U⋅V).
          * destruct U as [U HU], V as [V HV]. simpl in *.
            apply eagerReductionPar; assumption.
          * exact H.
        + assert (SNF (§u⋅§v) T) as H'. {
            split.
            - exact H.
            - destruct T as [T HT]. exact HT.
          }
          destruct
            (strictNormalFormApplL _ _ _ H') as [U [Hu HU]],
            (strictNormalFormApplR _ _ _ H') as [V [Hv HV]].
          clear H'.
          set (U' := exist _ _ HU : normalTerm).
          set (V' := exist _ _ HV : normalTerm).
          specialize (IHu U'). destruct IHu as [_ IHu]. rewrite (IHu Hu).
          specialize (IHv V'). destruct IHv as [_ IHv]. rewrite (IHv Hv).
          rewrite PAS.THMS.correctness1'. unfold Appl. simpl. clear IHu IHv U' V'.
          pose proof (eagerReductionPar _ _ _ _ HU Hu Hv) as H'.
          destruct
            (RW.THMS.functionalDoubleReduction
              EagerlyOneStepReduces eagerOneStepReductionFunctional _ _ _ H H')
          as [H'' | H''];
          [ | exact H''].
          destruct T as [T HT]. simpl in *.
          apply (strictlyNormalEagerReduction _ _ HT) in H''. subst.
          apply rt_refl.
    Qed.

    Theorem eagerlyReduces_closedPasTermEq (u v : PAS.term 0) :
      §u >>* §v -> u ≃ v.
    Proof.
      intro H. rewrite PAS.THMS.correctness2. setoid_rewrite closedPasTermDenotation.
      intros [T HT]. simpl. split; intro H'.
      - destruct (eagerReductionConfluent _ _ _ H H') as [T' [H'' HT']].
        apply (strictlyNormalEagerReduction _ _ HT) in HT'.
        subst. exact H''.
      - eapply rt_trans; eauto.
    Qed.

    Instance pca : PCA.Pca pas K S.
    Proof.
      split.
      - setoid_rewrite closedPasTermDenotation. intros [U HU] [V HV]. simpl.
        apply rt_step.
        unfold EagerlyOneStepReduces. simpl. rewrite HU, HV.
        reflexivity.
      - unfold PAS.Denotes. setoid_rewrite closedPasTermDenotation.
        intros [U HU] [V HV]. simpl.
        set (SUV := exist _ _ (suvStrictlyNormal _ _ HU HV) : normalTerm).
        exists SUV. apply rt_refl.
      - intros [U HU] [V HV] [W HW].
        apply eagerlyReduces_closedPasTermEq. simpl.
        apply rt_step.
        unfold EagerlyOneStepReduces. simpl. rewrite HU, HV, HW.
        reflexivity.
    Qed.

    Theorem nonTriviality : PCA.NonTrivial pca.
    Proof. exists K, S. intros H. discriminate H. Qed.

  End THMS.

End NORMAL_TERM_PCA.

(**
** Coercions
*)

Coercion NORMAL_TERM_PCA.normalTermToTerm :
  NORMAL_TERM_PCA.normalTerm >-> KS_RW.term.
