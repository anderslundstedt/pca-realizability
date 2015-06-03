(**
* A term partial combinatory algebra
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relation_Operators.

Require Import fin.
Require Import pas.
Require Import pca.
Require Import relationresults.

Import PAS.NOTATIONS.
Import PAS_COERCIONS.
Import PCA.NOTATIONS.
Import PCA_COERCIONS.
Import REL_RES.NOTATIONS.

Local Open Scope REL_RES.

Ltac inj_subst H := injection H; intros; subst; clear H.

Module TERM_PCA.

  (**
  ** Terms
  *)

  Inductive term : Type :=
  | K    : term
  | S    : term
  | appl : term -> term -> term.
  Local Infix "⋅" := appl (at level 40, left associativity).

  (**
  ** One step reduction relation
  *)

  Local Reserved Infix ">" (at level 70).
  Inductive OneStepRed : relation term :=
  | oneStepRedK u v    : K⋅u⋅v > u
  | oneStepRedS u v w  : S⋅u⋅v⋅w > u⋅w⋅(v⋅w)
  | oneStepRedL u u' v : u > u' -> u⋅v > u'⋅v
  | oneStepRedR u v v' : v > v' -> u⋅v > u⋅v'
  where "u > v" := (OneStepRed u v).

  (**
  ** Reduction relation
  *)

  Definition Red := OneStepRed+.
  Local Infix ">*" := Red (at level 70).

  (**
  ** One step reflexive parallel reduction relation
  *)

  Local Reserved Infix ">>" (at level 70).
  Inductive OneStepReflParRed : relation term :=
  | oneStepReflParRedK    u v       : K⋅u⋅v >> u
  | oneStepReflParRedS    u v w     : S⋅u⋅v⋅w >> u⋅w⋅(v⋅w)
  | oneStepReflParRedRefl u         : u >> u
  | oneStepReflParRedPar  u u' v v' : u >> u' -> v >> v' -> u⋅v >> u'⋅v'
  where "u >> v" := (OneStepReflParRed u v).

  (**
  ** Reflexive parallel reduction relation
  *)

  Definition ReflParRed := OneStepReflParRed+.
  Local Infix ">>*" := ReflParRed (at level 70).

  (**
  ** Relations between reduction relations
  *)

  Lemma inclusion1 : inclusion _ OneStepRed OneStepReflParRed.
  Proof. intros u v H. induction H; auto using OneStepReflParRed. Qed.

  Lemma redL (u v u' : term) : u >* u' -> u⋅v >* u'⋅v.
  Proof.
    intro H. induction H as [u u' | u | u w u' HL IHL HR IHR].
    - apply rt_step. constructor. assumption.
    - apply rt_refl.
    - apply rt_trans with (y := w⋅v); assumption.
  Qed.

  Lemma redR (u v v' : term) : v >* v' -> u⋅v >* u⋅v'.
  Proof.
    intro H. induction H as [v v' | v | v w v' HL IHL HR IHR].
    - apply rt_step. constructor. assumption.
    - apply rt_refl.
    - apply rt_trans with (y := u⋅w); assumption.
  Qed.

  Lemma redPar (u v u' v' : term) : u >* u' -> v >* v' -> u⋅v >* u'⋅v'.
  Proof.
    intros Hu Hv.
    apply rt_trans with (y := u'⋅v); [apply redL | apply redR]; assumption.
  Qed.

  Lemma inclusion2 : inclusion _ OneStepReflParRed Red.
  Proof.
    intros u v H. induction H as [v t | u v w | v | u u' v v' HL IHL HR IHR].
    - apply rt_step. constructor.
    - apply rt_step. constructor.
    - apply rt_refl.
    - apply rt_trans with (y := u'⋅v); [apply redL | apply redR]; assumption.
  Qed.

  Lemma redEqReflParRed : same_relation _ Red ReflParRed.
  Proof.
    split.
    - apply REL_RES.clos_refl_transIncreasing. apply inclusion1.
    - intros u v H.
      induction H as [u v H | u | u w v _ IHL _ IHR].
      + apply inclusion2. assumption.
      + apply rt_refl.
      + apply rt_trans with (y := w); assumption.
  Qed.

  (**
  ** The reduction relation is confluent
  *)

  Lemma oneStepReflParRedDp : REL_RES.Dp _ OneStepReflParRed.
  Proof.
    (* redundant cases *)
    assert (forall t u v, K⋅t >> u -> exists w, t >> w /\ u⋅v >> w) as case1. {
      intros t u v H. inversion_clear H.
      - eauto using OneStepReflParRed.
      - inversion_clear H0. eauto using OneStepReflParRed.
    }
    assert
      (forall u v w u' v',
       S⋅u⋅v >> u' -> w >> v' -> exists w', u⋅w⋅(v⋅w) >> w' /\ u'⋅v' >> w')
    as case2. {
      intros u v w u' v' HL HR. remember (S⋅u⋅v) as Suv eqn:HSuv.
      destruct HL as [u'' v'' | u'' v'' w'' | t | u'' u''' v'' v''' HL' HR'].
      - inversion HSuv.
      - discriminate HSuv.
      - subst. eauto 6 using OneStepReflParRed.
      - inj_subst HSuv. inversion_clear HL'.
        + eauto 6 using OneStepReflParRed.
        + inversion_clear H. eauto 6 using OneStepReflParRed.
    }
    (* the proof *)
    intros t u v H. generalize dependent v.
    induction H as [u v | u v w | t | u u' v v' HL IHL HR IHR].
    - remember (K⋅u⋅v) as t eqn:Ht.
      intros w H. destruct H as [u' v' | u' v' w' | t | u'' u' v'' v' H' H'' ].
      + inj_subst Ht. eauto using OneStepReflParRed.
      + inversion Ht.
      + subst. eauto using OneStepReflParRed.
      + inj_subst Ht. apply (case1 _ _ _ H').
    - remember (S⋅u⋅v⋅w) as t eqn:Ht.
      intros t' H.
      destruct H as [u' v' | u' v' w' | t | u'' u' v'' v' H' H''].
      + inversion Ht.
      + inj_subst Ht. eauto using OneStepReflParRed.
      + subst. eauto using OneStepReflParRed.
      + inj_subst Ht. apply (case2 _ _ _ _  _ H' H'').
    - eauto using OneStepReflParRed.
    - remember (u⋅v) as t eqn:Ht.
      intros t' H.
      destruct H as [u'' v'' | u'' v'' w'' | t | u''' u'' v''' v'' HL' HR'].
      + inj_subst Ht. pose proof (case1 _ _ v' HL). firstorder.
      + inj_subst Ht. pose proof (case2 _ _ _ _ _ HL HR). firstorder.
      + subst. eauto using OneStepReflParRed.
      + inj_subst Ht.
        destruct (IHL _ HL') as [u''' [H H']], (IHR _ HR') as [v''' [H'' H''']].
        eauto using OneStepReflParRed.
  Qed.

  Theorem redConfluent : REL_RES.Dp _ Red.
  Proof.
    cut (REL_RES.Dp _ ReflParRed).
    + intros H u v v' H' H''.
      apply redEqReflParRed in H'.
      apply redEqReflParRed in H''.
      destruct (H _ _ _ H' H'') as [w [H''' H4]].
      apply redEqReflParRed in H'''.
      apply redEqReflParRed in H4.
      eauto.
    + apply REL_RES.dp_confluence. apply oneStepReflParRedDp.
  Qed.

  (**
  ** Normal terms and normal forms
  *)

  Definition Normal (u : term) := ~exists v, u > v.

  Lemma normApplL (u v : term) : Normal (u⋅v) -> Normal u.
  Proof. intros H [t Ht]. eauto using OneStepRed. Qed.

  Lemma normApplR (u v : term) : Normal (u⋅v) -> Normal v.
  Proof. intros H [t Ht]. eauto using OneStepRed. Qed.

  Lemma kNormal : Normal K.
  Proof. intros [u H]. inversion H. Qed.

  Lemma ktNormal (t : term) : Normal t -> Normal (K⋅t).
  Proof.
    intros H [v H']. inversion_clear H'.
    - inversion_clear H0.
    - apply H. eauto.
  Qed.

  Lemma sNormal : Normal S.
  Proof. intros [u H]. inversion H. Qed.

  Lemma stNormal (t : term) : Normal t -> Normal (S⋅t).
  Proof.
    intros H [u H']. inversion_clear H'.
    - inversion_clear H0.
    - apply H. eauto.
  Qed.

  Lemma suvNormal (u v : term) : Normal u -> Normal v -> Normal (S⋅u⋅v).
  Proof.
    intros Hu Hv [w H]. inversion_clear H.
    - destruct (stNormal u Hu); eauto.
    - apply Hv. eauto.
  Qed.

  Definition NormalForm (u v : term) := u >* v /\ Normal v.
  Local Notation NF := NormalForm.

  Lemma normalRed (u v : term) : Normal u -> u >* v -> u = v.
  Proof.
    intros H H'.
    induction H' as [u v H' | u H' | u v w _ IHL _ IHR].
    - exfalso. eauto.
    - reflexivity.
    - specialize (IHL H). subst. exact (IHR H).
  Qed.

  Theorem normalFormsUnique (u v v' : term) : NF u v -> NF u v' -> v = v'.
  Proof.
    intros [Huv Hv] [Huv' Hv'].
    destruct (redConfluent u v v' Huv Huv') as [w [Hvw Hv'w]].
    apply normalRed in Hvw; [ | exact Hv].
    apply normalRed in Hv'w; [ | exact Hv'].
    congruence.
  Qed.

  (**
  ** Strict one step reduction
  *)

  Local Reserved Infix ">>>" (at level 70).
  Inductive StrictOneStepRed : term -> term -> Prop :=
  | strictOneStepRedAppl u v w  : Normal u -> Normal v -> u⋅v > w -> u⋅v >>> w
  | strictOneStepRedL    u u' v : u >>> u' -> u⋅v >>> u'⋅v
  | strictOneStepRedR    u v v' : v >>> v' -> u⋅v >>> u⋅v'
  where "u >>> v" := (StrictOneStepRed u v).

  Lemma strictOneStepRed_oneStepRed (u v : term) : u >>> v -> u > v.
  Proof. intro H. induction H; auto using OneStepRed. Qed.

  (**
  ** Strict reduction
  *)

  Definition StrictRed := StrictOneStepRed+.
  Local Infix ">>>*" := StrictRed (at level 70).

  Lemma strictRed_red (u v : term) : u >>>* v -> u >* v.
  Proof.
    intro H. induction H as [u v | t | u v w _ IHL _ IHR].
    - apply rt_step. apply strictOneStepRed_oneStepRed. exact H.
    - apply rt_refl.
    - apply rt_trans with (y := v); assumption.
  Qed.

  Lemma strictRedL (u u' v : term) : u >>>* u' -> u⋅v >>>* u'⋅v.
  Proof.
    intro H. generalize dependent v.
    induction H as [u u' H | u | u u' u'' _ IHL _ IHR]; intro v.
    - apply rt_step. apply strictOneStepRedL. assumption.
    - apply rt_refl.
    - specialize (IHL v). specialize (IHR v).
      apply rt_trans with (y := u'⋅v); assumption.
  Qed.

  Lemma strictRedR (u v v' : term) : v >>>* v' -> u⋅v >>>* u⋅v'.
  Proof.
    intro H. generalize dependent u.
    induction H as [v v' H | v | v v' v'' _ IHL _ IHR]; intro u.
    - apply rt_step. apply strictOneStepRedR. assumption.
    - apply rt_refl.
    - specialize (IHL u). specialize (IHR u).
      apply rt_trans with (y := u⋅v'); assumption.
  Qed.

  Lemma strictRedPar (u u' v v' : term) :
    u >>>* u' -> v >>>* v' -> u⋅v >>>* u'⋅v'.
  Proof.
    intros Hu Hv.
    apply rt_trans with (y := u'⋅v);
    [apply strictRedL | apply strictRedR]; assumption.
  Qed.

  (**
  ** Strict normal forms
  *)

  Definition StrictNormalForm (u v : term) := u >>>* v /\ Normal v.
  Local Notation SNF := StrictNormalForm.

  Lemma strictNormalForm_normalForm (u v : term) : SNF u v -> NF u v.
  Proof. firstorder using strictRed_red. Qed.

  Lemma strictNormalFormsUnique (u v w : term) : SNF u v -> SNF u w -> v = w.
  Proof. eauto using strictNormalForm_normalForm, normalFormsUnique. Qed.

  (**
  ** Normal terms form a partial applicative structure
  *)

  Definition normalTerm := {t : term | Normal t}.

  Definition normalTermsToTerms (t : normalTerm) : term := proj1_sig t.
  Local Coercion normalTermsToTerms : normalTerm >-> term.

  Definition NormalTermEq (u v : normalTerm) := (u : term) = (v : term).

  Instance normalTermEqEquivalence : Equivalence NormalTermEq.
  Proof. unfold NormalTermEq. split; congruence. Qed.

  Definition NormalTermAppl (u v w : normalTerm) : Prop := SNF (u⋅v) w.

  Instance termPas : PAS.Pas := {
    carrier := normalTerm;
    CarrierEq := NormalTermEq;
    carrierEqEquivalence := normalTermEqEquivalence;
    Appl := NormalTermAppl
  }.
  Proof.
    - unfold NormalTermAppl, NormalTermEq. congruence.
    - unfold NormalTermAppl, NormalTermEq. eauto using strictNormalFormsUnique.
  Defined.

  Local Open Scope PAS.

  Lemma normalApplRed (u v w w' : term) :
    Normal u -> Normal v -> u⋅v > w -> u⋅v > w' -> w = w'.
  Proof.
    intros Hu Hv H H'.
    remember (u⋅v) as uv eqn:Huv.
    destruct H as [x | x y z H | x u' y H | x y v' H];
    injection Huv; intros; subst; clear Huv.
    - inversion_clear H'.
      + reflexivity.
      + exfalso. eauto.
      + exfalso. eauto.
    - inversion_clear H'.
      + reflexivity.
      + exfalso. eauto.
      + exfalso. eauto.
    - exfalso. eauto.
    - exfalso. eauto.
  Qed.

  (**
  ** Strict one step reflexive reduction
  *)

  Definition StrictOneStepReflRed :=
    REL_RES.ReflexiveClosure _ StrictOneStepRed.
  Local Infix ">>=" := (StrictOneStepReflRed) (at level 70, no associativity).

  Lemma strictOneStepReflRedL (u u' v : term) : u >>= u' -> u⋅v >>= u'⋅v.
  Proof.
    intro H. destruct H as [H | H].
    - left. apply strictOneStepRedL. assumption.
    - right. congruence.
  Qed.

  Lemma strictOneStepReflRedR (u v v' : term) : v >>= v' -> u⋅v >>= u⋅v'.
  Proof.
    intros H. destruct H as [H | H].
    - left. apply strictOneStepRedR. assumption.
    - right. congruence.
  Qed.

  Lemma strictOneStepReflRedDp : REL_RES.Dp _ StrictOneStepReflRed.
  Proof.
    intros t u v H H'. destruct H as [H | H]; destruct H' as [H' | H'].
    - generalize dependent v.
      induction H as [u v w Hu Hv H | u u' v H IH | u v v' H IH].
      + intros w' H'. remember (u⋅v) as t eqn:Ht.
        destruct H' as [u' v' w' _ _ H' | u'' u' v' H' | u' v'' v' H'];
        inj_subst Ht.
        * rewrite (normalApplRed _ _ _ _ Hu Hv H H').
          unfold StrictOneStepReflRed, REL_RES.ReflexiveClosure. eauto.
        * exfalso. apply Hu. exists u'.
          apply strictOneStepRed_oneStepRed. assumption.
        * exfalso. apply Hv. exists v'.
          apply strictOneStepRed_oneStepRed. assumption.
      + intros w H'. remember (u⋅v) as t eqn:Ht.
        destruct H' as [u'' v'' w Hu _ H' | u''' u'' v''' H' | u'' v'' v' H'];
        inj_subst Ht.
        * exfalso. apply Hu. exists u'.
          apply strictOneStepRed_oneStepRed. assumption.
        * destruct (IH _ H') as [w [H'' H''']].
          eauto using strictOneStepReflRedL.
        * exists (u'⋅v').
          split; [apply strictOneStepReflRedR | apply strictOneStepReflRedL];
          left; assumption.
      + intros w H'. remember (u⋅v) as t eqn:Ht.
        destruct H' as [u'' v'' w _ Hv H' | u'' u' v''' H' | u' v''' v'' H'];
        inj_subst Ht.
        * exfalso. apply Hv. exists v'.
          apply strictOneStepRed_oneStepRed. assumption.
        * exists (u'⋅v').
          split; [apply strictOneStepReflRedL | apply strictOneStepReflRedR];
          left; assumption.
        * destruct (IH _ H') as [w [H'' H''']].
          eauto using strictOneStepReflRedR.
    - subst. exists u. split; [right | left]; auto.
    - subst. exists v. split; [left | right]; auto.
    - exists t. subst. split; right; auto.
  Qed.

  (**
  ** Strict reduction confluent
  *)

  Lemma strictRedConfluent : REL_RES.Dp _ StrictRed.
  Proof. apply REL_RES.dpReflClos_confluence. apply strictOneStepReflRedDp. Qed.

  (**
  ** Strict one step left-or-right reduction
  *)

  Reserved Notation "u >>>lr v" (at level 70, no associativity).
  Inductive StrictOneStepRedLeftRight : term -> term -> Prop :=
  | strictOneStepRedLeftRightL u u' v : u >>> u' -> u⋅v >>>lr u'⋅v
  | strictOneStepRedLeftRightR u v v' : v >>> v' -> u⋅v >>>lr u⋅v'
  where "u >>>lr v" := (StrictOneStepRedLeftRight u v).

  (**
  ** Strict left-or-right reduction
  *)

  Definition StrictRedLeftRight := StrictOneStepRedLeftRight+.
  Infix ">>>lr*" := StrictRedLeftRight (at level 70, no associativity).

  Lemma strictRedLeftRightL (u v u' v' : term) : u⋅v >>>lr* u'⋅v' -> u >>>* u'.
  Proof.
    intro H. apply REL_RES.nChain_clos_refl_trans in H.
    destruct H as [m H].
    generalize dependent v'. generalize dependent u'.
    generalize dependent v. generalize dependent u.
    induction m as [ | m IH]; intros.
    - inversion_clear H. apply rt_refl.
    - inversion_clear H. inversion H1; subst.
      + specialize (IH u v u0 v' H0). apply rt_trans with (y := u0); auto.
        apply rt_step. assumption.
      + eapply IH; eauto.
  Qed.

  Lemma strictRedLeftRightR (u v u' v' : term) : u⋅v >>>lr* u'⋅v' -> v >>>* v'.
  Proof.
    intro H. apply REL_RES.nChain_clos_refl_trans in H.
    destruct H as [m H].
    generalize dependent v'. generalize dependent u'.
    generalize dependent v. generalize dependent u.
    induction m as [ | m IH]; intros.
    - inversion_clear H. apply rt_refl.
    - inversion_clear H. inversion H1; subst.
      + eapply IH; eauto.
      + specialize (IH u v u' v0 H0). apply rt_trans with (y := v0); auto.
        apply rt_step. assumption.
  Qed.

  (**
  Closed PAS terms as terms
  *)

  Fixpoint closedPasTermToTerm (t : @PAS.term termPas 0) : term :=
  match t with
  | &a        => let (a, _) := a in a
  | PAS.var x => False_rect _ (FIN.t0Empty x)
  | u*v       => closedPasTermToTerm u ⋅ closedPasTermToTerm v
  end.
  Local Notation "§ t" := (closedPasTermToTerm t) (at level 6).

  Lemma closedPasTermEq (u v : @PAS.term termPas 0) : §u >>>* §v -> u ≃ v.
  Proof.
    assert (forall u v w, u⋅v >>>lr* w -> exists u' v', w = u'⋅v') as lemma. {
      clear.
      intros u v w H. apply REL_RES.nChain_clos_refl_trans in H.
      destruct H as [m H].
      generalize dependent w. generalize dependent v. generalize dependent u.
      induction m as [ | m IH]; intros.
      - inversion_clear H. eauto.
      - inversion_clear H. specialize (IH u v b H0).
        destruct IH as [u' [v' H]]. subst. destruct H1; eauto.
    }
    assert
      (forall u v w,
       u⋅v >>>* w ->
       u⋅v >>>lr* w \/
       exists n n', Normal n /\ Normal n' /\ u >>>* n /\ v >>>* n'
                    /\ n⋅n' >>>* w)
    as lemma'. {
      clear u v.
      intros u v w H. apply REL_RES.nChain_clos_refl_trans in H.
      destruct H as [m H].
      generalize dependent w. generalize dependent v. generalize dependent u.
      induction m as [ | m IH]; intros.
      - inversion_clear H. left. apply rt_refl.
      - inversion_clear H. specialize (IH u v b H0).
        destruct IH as [IH | IH].
        + inversion H1; subst.
          * right. exists u0, v0. repeat split; auto.
            { apply (strictRedLeftRightL _ _ _ _ IH). }
            { apply (strictRedLeftRightR _ _ _ _ IH). }
            { apply rt_step. assumption. }
          * left. eapply rt_trans; eauto. apply rt_step.
            apply strictOneStepRedLeftRightL. assumption.
          * left. eapply rt_trans; eauto. apply rt_step.
            apply strictOneStepRedLeftRightR. assumption.
        + right. destruct IH as [n [n' IH]]. exists n, n'.
          repeat split; try tauto. apply rt_trans with (y := b); [tauto | ].
          apply rt_step. assumption.
    }
    assert
      (forall u v n, u⋅v >>>* n -> Normal n ->
                     exists n' n'', SNF u n' /\ SNF v n'' /\ n'⋅n'' >>>* n)
    as lemma''. {
      clear u v.
      intros u v n H Hn. apply lemma' in H.
      destruct H as [H | [n' [n'' [Hn' [Hn'' [H [H' H'']]]]]]].
      - destruct (lemma u v n H) as [n' [n'' H']]. subst.
        exists n', n''. split; [ | split].
        + split; [ | apply (normApplL _ _ Hn)].
          apply (strictRedLeftRightL _ _ _ _ H).
        + split; [ | apply (normApplR _ _ Hn)].
          apply (strictRedLeftRightR _ _ _ _ H).
        + apply rt_refl.
      - exists n', n''. repeat split; auto.
    }
    clear lemma lemma'.
    assert (forall u (v : normalTerm), §u >>>* v -> u ≃ &v) as lemma. {
      clear u v.
      induction u as [u | x | u IHu v IHv].
      - intros v H. simpl in H. apply strictRed_red in H.
        cut (u == v); [intro H'; rewrite H'; reflexivity | ].
        destruct u as [u Hu]. apply normalRed; assumption.
      - destruct x.
      - intros w H.
        destruct (lemma'' _ _ _ H (proj2_sig w))
          as [a [b [[H' Ha] [[H'' Hb] H''']]]].
        fold closedPasTermToTerm in H', H''.
        set (a' := exist _ _ Ha : normalTerm). setoid_rewrite (IHu a' H').
        set (b' := exist _ _ Hb : normalTerm). setoid_rewrite (IHv b' H'').
        setoid_rewrite PAS.correctness1'.
        destruct w as [w Hw]. split; assumption.
    }
    assert (forall u (v : normalTerm), u ≃ &v <-> SNF §u v) as lemma'. {
      clear u v.
      intro u. induction u as [u | x | u IHu v IHv].
      - intro n. split; intro H.
        + apply PAS.constInjective in H.
          destruct u as [u Hu], n as [n Hn]. simpl in *.
          unfold NormalTermEq in H. simpl in H. subst.
          split; [apply rt_refl | exact Hn].
        + cut (u == n); [intro Hun; rewrite Hun; reflexivity | ].
          destruct H as [H _], u as [u Hu], n as [n Hn]. simpl in *.
          unfold NormalTermEq. simpl.
          apply normalRed; [exact Hu | ]. apply strictRed_red. exact H.
      - inversion x.
      - intro n. simpl. rewrite PAS.correctness1. split.
        + intros [a [b [Hu [Hv H]]]].
          specialize (IHu a).
          specialize (IHv b).
          destruct IHu as [IHu _]. specialize (IHu Hu). destruct IHu as [IHu _].
          destruct IHv as [IHv _]. specialize (IHv Hv). destruct IHv as [IHv _].
          unfold PAS.Appl in H. simpl in H. unfold NormalTermAppl in H.
          destruct n as [n Hn]. destruct a as [a Ha]. destruct b as [b Hb].
          simpl in *. split; [ | exact Hn].
          destruct H as [H _].
          apply rt_trans with (y := a⋅b); [ | exact H].
          apply strictRedPar; assumption.
        + intros [H Hn]. apply (lemma (u*v)) in H.
          setoid_rewrite PAS.correctness1 in H. exact H.
    }
    intro H. apply PAS.correctness2. intro v'.
    setoid_rewrite lemma'. clear lemma lemma' lemma''.
    split; intro H'; destruct H' as [H' _], v' as [v' Hv']; simpl in *.
    - split; [ | exact Hv'].
      destruct (strictRedConfluent §u §v v' H H') as [w [H'' H''']].
      assert (v' = w) as H4. {
        apply strictRed_red in H'''. apply normalRed in H'''; assumption.
      }
      subst. assumption.
    - split; [ | exact Hv']. apply rt_trans with (y := §v); assumption.
  Qed.

  (**
  ** Normal terms form a partial combinatory algebra
  *)

  Definition k : normalTerm := exist _ _ kNormal.
  Definition s : normalTerm := exist _ _ sNormal.

  Instance termPca : PCA.Pca := {
    pas := termPas;
    k := k;
    s := s
  }.
  Proof.
    - intros [u Hu] [v Hv]. apply closedPasTermEq.
      apply rt_step. simpl. apply strictOneStepRedAppl.
      + apply ktNormal. exact Hu.
      + exact Hv.
      + apply oneStepRedK.
    - intros [u Hu] [v Hv].
      set (suv := exist _ _ (suvNormal _ _ Hu Hv) : normalTerm).
      exists suv. apply closedPasTermEq. apply rt_refl.
    - intros [u Hu] [v Hv] [w Hw].
      apply closedPasTermEq. simpl.
      apply rt_step. apply strictOneStepRedAppl.
      + apply suvNormal; assumption.
      + exact Hw.
      + apply oneStepRedS.
  Defined.

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Delimit Scope TERM_PCA with TERM_PCA.

    Infix "⋅" :=
      (fun u v => u ⋅ v) (at level 40, left associativity) : TERM_PCA.
    Infix ">" := (fun u v => u > v) (at level 70) : TERM_PCA.
    Infix ">*" := (fun u v => u >* v) (at level 70) : TERM_PCA.
    Infix ">>>" := (fun u v => u >>> v) (at level 70) : TERM_PCA.
    Infix ">>>*" := (fun u v => u >>>* v) (at level 70) : TERM_PCA.
    Notation "§ t" := (§t) (at level 6) : TERM_PCA.

  End NOTATIONS.

End TERM_PCA.

(**
** Coercions
*)

Module TERM_PCA_COERCIONS.
  Import TERM_PCA.
  Coercion normalTermsToTerms : normalTerm >-> term.
End TERM_PCA_COERCIONS.
