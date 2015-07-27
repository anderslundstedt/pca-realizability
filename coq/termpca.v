(**
* Partial combinatory algebra based on KS-terms
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Relations.Relation_Operators.

Require Import fin.
Require Import ksrewriting.
Require Import pas.
Require Import pca.

Import KS_RW.
Import KS_RW.NOTATIONS.
Import KS_RW.THMS.
Import PAS.NOTATIONS.

Local Open Scope PAS.
Local Open Scope KS_RW.

Module TERM_PCA.

  (**
  ** Definitions
  *)

  Instance termSetoid : Setoid term := {equiv := Convertible}.

  Definition Appl : term -> term -> term -> Prop :=
    fun U V W => U⋅V == W.

  Fixpoint closedPasTermToTerm `{_ : PAS.Pas term} (t : PAS.term 0) : term :=
  match t with
  | &a        => a
  | PAS.var x => False_rect _ (FIN.THMS.t0Empty x)
  | u*v       => closedPasTermToTerm u ⋅ closedPasTermToTerm v
  end.
  Local Notation "§ t" := (closedPasTermToTerm t) (at level 6).

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Delimit Scope TERM_PCA with TERM_PCA.

    Notation "§ t" := (§t) (at level 6) : TERM_PCA.

  End NOTATIONS.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    Declare Instance pas : PAS.Pas termSetoid Appl.

    Axiom totality : PAS.Total pas.

    Declare Instance pca : PCA.Pca pas K S.

    Axiom nonTriviality : PCA.NonTrivial pca.

    Declare Instance applRespectsEquiv :
      Proper (equiv ==> equiv ==> equiv) appl.

    Declare Instance closedPasTermToTermRespectsEquiv :
      Proper (PAS.ClosedTermEq ==> equiv) closedPasTermToTerm.

    Axiom closedPasTermToTermEq : forall t : PAS.term 0, t ≃ &§t.

    Axiom closedPasTermToTermInjective : forall u v : PAS.term 0,
      §u == §v -> u ≃ v.

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Instance applRespectsEquiv : Proper (equiv ==> equiv ==> equiv) appl :=
      applRespectsConvertibility.

    Instance pas : PAS.Pas termSetoid Appl.
    Proof.
      split; unfold Appl.
      - intros u u' v v' w w' Hu Hv Hw Huv.
        rewrite <- Hu, <- Hv, <- Hw. exact Huv.
      - intros u v w w' H H'. rewrite <- H, H'. reflexivity.
    Qed.

    Theorem totality : PAS.Total pas.
    Proof. intros u v. exists (u⋅v). simpl. unfold Appl. reflexivity. Qed.

    Theorem closedPasTermToTermEq (t : PAS.term 0) : t ≃ &§t.
    Proof.
      induction t as [t | x | u IHu v IHv].
      - reflexivity.
      - contradiction.
      - simpl. rewrite IHu, IHv at 1. rewrite PAS.THMS.correctness1'.
        unfold Appl. reflexivity.
    Qed.

    Instance closedPasTermToTermRespectsEquiv :
      Proper (PAS.ClosedTermEq ==> equiv) closedPasTermToTerm.
    Proof.
      intros u v H.
      setoid_rewrite closedPasTermToTermEq in H.
      apply PAS.THMS.constInjective in H. rewrite H. reflexivity.
    Qed.

    Theorem closedPasTermToTermInjective (u v : PAS.term 0) : §u == §v -> u ≃ v.
    Proof.
      setoid_rewrite closedPasTermToTermEq. simpl.
      intro H. rewrite H. reflexivity.
    Qed.

    Instance pca : PCA.Pca pas K S.
    Proof.
      split.
      - intros a b. apply closedPasTermToTermInjective. simpl. exists a. split.
        + apply rt_step. apply oneStepReducesK.
        + apply rt_refl.
      - intros a b. exists (S⋅a⋅b). apply closedPasTermToTermInjective. simpl.
        exists (S⋅a⋅b). split; apply rt_refl.
      - intros a b c. apply closedPasTermToTermInjective. simpl.
        exists (a⋅c⋅(b⋅c)). split.
        + apply rt_step. apply oneStepReducesS.
        + apply rt_refl.
    Qed.

    Theorem nonTriviality : PCA.NonTrivial pca.
    Proof.
      exists K, S. intros [t [HK HS]].
      apply (normalReduction _ _ kNormal) in HK.
      apply (normalReduction _ _ sNormal) in HS.
      subst. discriminate HS.
    Qed.

  End THMS.

End TERM_PCA.
