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

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    Declare Instance pas : PAS.Pas normalTermSetoid Appl.

    Declare Instance pca : PCA.Pca pas K S.

    Axiom nonTriviality : PCA.NonTrivial pca.

    Axiom normalTermDenotation : forall (T : normalTerm), §T ≃ &T.

    Axiom termDenotation :
      forall (U : term) (V : normalTerm), §U ≃ &V <-> U >>* V.

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

    Fixpoint termToClosedPasTerm (T : term) : PAS.term 0 :=
    match T with
    | KS_RW.K   => &K
    | KS_RW.S   => &S
    | U⋅V       => termToClosedPasTerm U * termToClosedPasTerm V
    end.
    Local Notation "$ t" := (termToClosedPasTerm t) (at level 6).

    Lemma termDenotation' (U : term) (V : normalTerm) :
      $(U) ≃ &V <-> U >>* V.
    Proof.
      revert V. induction U as [ | | U IHU V IHV]; intro T.
      - simpl.
        assert (&K ≃ &T <-> K == T) as H. {
          split; intro H.
          - apply PAS.THMS.constInjective. exact H.
          - rewrite H. reflexivity.
        }
        rewrite H. clear H. simpl. unfold NormalTermEq. split; intro H.
        + rewrite <- H. simpl. apply rt_refl.
        + destruct T as [T HT]. simpl in *.
          apply strictlyNormalEagerReduction.
          * apply kStrictlyNormal.
          * exact H.
      - simpl.
        assert (&S ≃ &T <-> S == T) as H. {
          split; intro H.
          - apply PAS.THMS.constInjective. exact H.
          - rewrite H. reflexivity.
        }
        rewrite H. clear H. simpl. unfold NormalTermEq. split; intro H.
        + rewrite <- H. simpl. apply rt_refl.
        + destruct T as [T HT]. simpl in *.
          apply strictlyNormalEagerReduction.
          * apply sStrictlyNormal.
          * exact H.
      - split; intro H.
        + simpl in H. apply PAS.THMS.correctness1 in H.
          destruct H as [U' [V' [HU [HV H]]]].
          unfold Appl in H.
          specialize (IHU U'). destruct IHU as [IHU _]. specialize (IHU HU).
          specialize (IHV V'). destruct IHV as [IHV _]. specialize (IHV HV).
          clear HU HV. apply rt_trans with (y := U'⋅V').
          * destruct U' as [U' HU'], V' as [V' HV']. simpl in *.
            apply eagerReductionPar; assumption.
          * exact H.
        + simpl.
          assert (SNF (U⋅V) T) as H'. {
            split.
            - exact H.
            - destruct T as [T HT]. exact HT.
          }
          destruct
            (strictNormalFormApplL _ _ _ H') as [U' [HU HU']],
            (strictNormalFormApplR _ _ _ H') as [V' [HV HV']].
          clear H'.
          set (U'' := exist _ _ HU' : normalTerm).
          set (V'' := exist _ _ HV' : normalTerm).
          specialize (IHU U''). destruct IHU as [_ IHU]. rewrite (IHU HU).
          specialize (IHV V''). destruct IHV as [_ IHV]. rewrite (IHV HV).
          rewrite PAS.THMS.correctness1'. unfold Appl. simpl.
          clear IHU IHV U'' V''.
          pose proof (eagerReductionPar _ _ _ _ HU' HU HV) as H'.
          destruct
            (RW.THMS.functionalDoubleReduction
              EagerlyOneStepReduces eagerOneStepReductionFunctional _ _ _ H H')
          as [H'' | H''];
          [ | exact H''].
          destruct T as [T HT]. simpl in *.
          apply (strictlyNormalEagerReduction _ _ HT) in H''. subst.
          apply rt_refl.
    Qed.

    Lemma normalTermDenotation' (T : normalTerm) : $(T) ≃ &T.
    Proof. setoid_rewrite termDenotation'. apply rt_refl. Qed.

    Lemma eagerlyReduces_closedPasTermEq (U V : term) :
      U >>* V -> $(U) ≃ $(V).
    Proof.
      intro H. rewrite PAS.THMS.correctness2.
      setoid_rewrite termDenotation'.
      intros [T HT]. simpl. split; intro H'.
      - destruct (eagerReductionConfluent _ _ _ H H') as [T' [H'' HT']].
        apply (strictlyNormalEagerReduction _ _ HT) in HT'.
        subst. exact H''.
      - eapply rt_trans; eauto.
    Qed.

    Instance pca : PCA.Pca pas K S.
    Proof.
      split.
      - intros U V.
        setoid_rewrite <- normalTermDenotation'.
        cutrewrite ($(K)*$(U)*$(V) = $(K⋅U⋅V)); [ | reflexivity].
        apply eagerlyReduces_closedPasTermEq.
        destruct U as [U HU], V as [V HV]. simpl.
        apply rt_step. unfold EagerlyOneStepReduces. simpl. rewrite HU, HV.
        reflexivity.
      - intros U V.
        setoid_rewrite <- normalTermDenotation'.
        cutrewrite ($(S)*$(U)*$(V) = $(S⋅U⋅V)); [ | reflexivity].
        unfold PAS.Denotes. setoid_rewrite termDenotation'.
        destruct U as [U HU], V as [V HV]. simpl.
        set (SUV := exist _ _ (suvStrictlyNormal _ _ HU HV) : normalTerm).
        exists SUV. apply rt_refl.
      - intros U V W.
        setoid_rewrite <- normalTermDenotation'.
        cutrewrite ($(S)*$(U)*$(V)*$(W) = $(S⋅U⋅V⋅W)); [ | reflexivity].
        cutrewrite ($(U)*$(W)*($(V)*$(W)) = $(U⋅W⋅(V⋅W))); [ | reflexivity].
        apply eagerlyReduces_closedPasTermEq.
        destruct U as [U HU], V as [V HV], W as [W HW]. simpl.
        apply rt_step.
        unfold EagerlyOneStepReduces. simpl. rewrite HU, HV, HW.
        reflexivity.
    Qed.

    Theorem nonTriviality : PCA.NonTrivial pca.
    Proof. exists K, S. intros H. discriminate H. Qed.

    Lemma equalMaps (T : term) : §T = $(T).
    Proof.
      induction T as [ | | U IHU V IHV].
      - reflexivity.
      - reflexivity.
      - simpl. rewrite IHU, IHV. reflexivity.
    Qed.

    Theorem normalTermDenotation (T : normalTerm) : §T ≃ &T.
    Proof. rewrite equalMaps. apply normalTermDenotation'. Qed.

    Theorem termDenotation (U : term) (V : normalTerm) : §U ≃ &V <-> U >>* V.
    Proof. rewrite equalMaps. apply termDenotation'. Qed.

  End THMS.

End NORMAL_TERM_PCA.

(**
** Coercions
*)

Coercion NORMAL_TERM_PCA.normalTermToTerm :
  NORMAL_TERM_PCA.normalTerm >-> KS_RW.term.
