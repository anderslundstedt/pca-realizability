Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relation_Operators.

Require Import myvec.
Require Import pas.
Require Import pca.
Require Import relationresults.

Import PAS.NOTATIONS.
Import PAS_COERCIONS.
Import PCA.NOTATIONS.
Import PCA_COERCIONS.
Import REL_RES.NOTATIONS.

Local Open Scope REL_RES.

Module TERM_PCA.

  Inductive term : Type :=
    K    : term
  | S    : term
  | conc : term -> term -> term.
  Local Infix "⋅" := conc (at level 40, left associativity).

  (* one step reduction relation *)
  Inductive OneStepRed : relation term :=
    oneStepRedK u v    : OneStepRed (K⋅u⋅v) u
  | oneStepRedS u v w  : OneStepRed (S⋅u⋅v⋅w) (u⋅w⋅(v⋅w))
  | oneStepRedL u u' v : OneStepRed u u' -> OneStepRed (u⋅v) (u'⋅v)
  | oneStepRedR u v v' : OneStepRed v v' -> OneStepRed (u⋅v) (u⋅v').
  Local Infix ">" := OneStepRed (at level 70).

  (* reduction relation *)
  Definition Red := OneStepRed+.
  Local Infix ">*" := Red (at level 70).

  (* one step reflexive parallel reduction relation *)
  Inductive OneStepReflParRed : relation term :=
    oneStepReflParRedK    u v       : OneStepReflParRed (K⋅u⋅v) u
  | oneStepReflParRedS    u v w     : OneStepReflParRed (S⋅u⋅v⋅w) (u⋅w⋅(v⋅w))
  | oneStepReflParRedRefl u         : OneStepReflParRed u u
  | oneStepReflParRedPar  u u' v v' :
      OneStepReflParRed u u' -> OneStepReflParRed v v' ->
      OneStepReflParRed (u⋅v) (u'⋅v').
  Local Infix ">>" := OneStepReflParRed (at level 70).

  (* reflexive parallel reduction relation *)
  Definition ReflParRed := OneStepReflParRed+.
  Local Infix ">>*" := ReflParRed (at level 70).

  (* relations between reduction relations *)

  Lemma inclusion1 : inclusion _ OneStepRed OneStepReflParRed.
  Proof. intros u v H. induction H; auto using OneStepReflParRed. Qed.

  Lemma redL : forall u v u', u >* u' -> u⋅v >* u'⋅v.
  Proof.
    intros u v u' H.
    induction H as [u u' | u | u w u' HL IHL HR IHR].
    - apply rt_step. constructor. assumption.
    - apply rt_refl.
    - apply rt_trans with (y := w⋅v); assumption.
  Qed.

  Lemma redR : forall u v v', v >* v' -> u⋅v >* u⋅v'.
  Proof.
    intros u v u' H. induction H as [v v' | v | v w v' HL IHL HR IHR].
    - apply rt_step. constructor. assumption.
    - apply rt_refl.
    - apply rt_trans with (y := u⋅w); assumption.
  Qed.

  Lemma redPar : forall u v u' v', u >* u' -> v >* v' -> u⋅v >* u'⋅v'.
  Proof.
    intros u v u' v' Hu Hv.
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

  Lemma oneStepReflParRedDp : REL_RES.Dp _ OneStepReflParRed.
  Proof with (eauto using OneStepReflParRed).
    Ltac inj_subst H := injection H; intros; subst; clear H.
    intros u v v' H. generalize dependent v'.
    induction H as [v t | x y z | u | x x' y y' HL IHL HR IHR].
    - remember (K⋅v⋅t) as u eqn:Hu.
      intros v' H. destruct H.
      + inj_subst Hu...
      + inversion Hu.
      + (* TODO (redundant case) *) admit.
      + (* TODO (redundant case) *) admit.
    - remember (S⋅x⋅y⋅z) as u eqn:Hu.
      intros v' H'. destruct H'.
      + (* TODO (redundant case) *) admit.
      + inj_subst Hu...
      + (* TODO (redundant case) *) admit.
      + (* TODO (redundant case) *) admit.
    - idtac...
    - remember (x⋅y) as u eqn:Hu.
      intros v' H. destruct H as [v' t | a b c | | x''' x'' y''' y'' HL' HR'].
      + inj_subst Hu.
        assert (exists v'', x' = K⋅v'' /\ v' >> v'') as [v'' [H H']].
        { inversion_clear HL... inversion_clear H... }
        subst...
      + inj_subst Hu.
        assert (exists a' b', x' = S⋅a'⋅b' /\ a >> a' /\ b >> b')
          as [a' [b' [H [H' H'']]]].
        { inversion_clear HL... inversion_clear H... inversion_clear H1... }
        subst. exists (a'⋅y'⋅(b'⋅y'))...
      + (* TODO (redundant case) *) admit.
      + inj_subst Hu.
        destruct (IHL x'' HL') as [x''' [H H']].
        destruct (IHR y'' HR') as [y''' [H'' H''']]...
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

  Definition Normal (u : term) := ~exists v, u > v.

  Definition NormalForm (u v : term) := u >* v /\ Normal v.
  Local Notation NF := NormalForm.

  Lemma normalRed : forall u v, Normal u -> u >* v -> u = v.
  Proof.
    intros n t H H'.
    induction H' as [u v H' | u H' | u v w _ IHL _ IHR].
    - exfalso. eauto.
    - reflexivity.
    - specialize (IHL H). subst. exact (IHR H).
  Qed.

  Theorem normalFormsUnique : forall u v v' : term, NF u v -> NF u v' -> v = v'.
  Proof.
    intros u v v' [Huv Hv] [Huv' Hv'].
    destruct (redConfluent u v v' Huv Huv') as [w [Hvw Hv'w]].
    apply normalRed in Hvw; [ | exact Hv].
    apply normalRed in Hv'w; [ | exact Hv'].
    congruence.
  Qed.

  Definition normalTerm := {t : term | Normal t}.

  Local Coercion normalTermsToTerms (t : normalTerm) : term :=
    let (t, _) := t in t.

  Definition NormalTermEq (u v : normalTerm) := (u : term) = (v : term).

  Instance normalTermEqEquivalence : Equivalence NormalTermEq.
  Proof. unfold NormalTermEq. split; congruence. Qed.

  Inductive StrictOneStepRed : term -> term -> Prop :=
    strictOneStepRedConc u v w  :
      Normal u -> Normal v -> u⋅v > w -> StrictOneStepRed (u⋅v) w
  | strictOneStepRedL    u u' v :
      StrictOneStepRed u u' -> StrictOneStepRed (u⋅v) (u'⋅v)
  | strictOneStepRedR    u v v' :
      StrictOneStepRed v v' -> StrictOneStepRed (u⋅v) (u⋅v').
  Local Infix ">>>" := StrictOneStepRed (at level 70).

  Definition StrictRed := StrictOneStepRed+.
  Local Infix ">>>*" := StrictRed (at level 70).

  Definition StrictNormalForm (u v : term) := u >>>* v /\ Normal v.
  Local Notation SNF := StrictNormalForm.

  Lemma strictOneStepRed_oneStepRed (u v : term) : u >>> v -> u > v.
  Proof. intro H. induction H; auto using OneStepRed. Qed.

  Lemma strictRed_red (u v : term) : u >>>* v -> u >* v.
  Proof.
    intro H. induction H as [u v | t | u v w _ IHL _ IHR].
    - apply rt_step. apply strictOneStepRed_oneStepRed. exact H.
    - apply rt_refl.
    - apply rt_trans with (y := v); assumption.
  Qed.

  Lemma strictNormalForm_normalForm (u v : term) : SNF u v -> NF u v.
  Proof. firstorder using strictRed_red. Qed.

  Lemma strictNormalFormsUnique (u v w : term) : SNF u v -> SNF u w -> v = w.
  Proof. eauto using strictNormalForm_normalForm, normalFormsUnique. Qed.

  Definition NormalTermAppl (u v w : normalTerm) : Prop := SNF (u⋅v) w.

  Lemma normalTermApplRespectful (u u' v v' w w' : normalTerm) :
    NormalTermEq u u' -> NormalTermEq v v' -> NormalTermEq w w' ->
    NormalTermAppl u v w -> NormalTermAppl u' v' w'.
  Proof. unfold NormalTermEq, NormalTermAppl. congruence. Qed.

  Instance normalTermApplProper :
    Proper
      (NormalTermEq ==> NormalTermEq ==> NormalTermEq ==> iff) NormalTermAppl.
  Proof.
    intros u u' Hu v v' Hv w w' Hw.
    split;
      [ | symmetry in Hu, Hv, Hw]; apply normalTermApplRespectful; assumption.
  Qed.

  Theorem normalTermApplFunctional (u v w w' : normalTerm) :
    NormalTermAppl u v w -> NormalTermAppl u v w' -> NormalTermEq w w'.
  Proof.
    unfold NormalTermAppl, NormalTermEq. eauto using strictNormalFormsUnique.
  Qed.

  Instance termPas : PAS.Pas := {
    carrier := normalTerm;
    CarrierEq := NormalTermEq;
    carrierEqEquivalence := normalTermEqEquivalence;
    Appl := NormalTermAppl;
    applRespectful := normalTermApplRespectful;
    applFunctional := normalTermApplFunctional
  }.

  Local Open Scope PAS.

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

  Lemma normalConc (u v w w' : term) :
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
    intros u v v' H H'. destruct H as [H | H]; destruct H' as [H' | H'].
    - generalize dependent v'.
      induction H as [u v w Hu Hv H | u_l u'_l u_r H IH | u_l u_r u'_r H IH].
      + intros w' H'. remember (u⋅v) as uv eqn:Huv.
        destruct H' as [u' v' w' Hu' Hv' H' | x v' y H' | ];
        injection Huv; intros; subst; clear Huv.
        * rewrite (normalConc u v w w' Hu Hv H H').
          exists w'. split; right; reflexivity.
        * exfalso. apply Hu. exists v'.
          apply strictOneStepRed_oneStepRed. assumption.
        * exfalso. apply Hv. exists v'.
          apply strictOneStepRed_oneStepRed. assumption.
      + intros v' H'. remember (u_l⋅u_r) as a eqn:Ha.
        destruct H' as [ | x u''_l y H' IH' | x y u'_r H'];
        injection Ha; intros; subst; clear Ha.
        * (* TODO: redundant case *) admit.
        * destruct (IH u''_l H') as [w_l [H'' H''']]. exists (w_l⋅u_r).
          split; apply strictOneStepReflRedL; assumption.
        * exists (u'_l⋅u'_r).
          split; [apply strictOneStepReflRedR | apply strictOneStepReflRedL];
          left; assumption.
      + intros v' H'. remember (u_l⋅u_r) as a eqn:Ha.
        destruct H' as [ | | x y u''_r H'];
        injection Ha; intros; subst; clear Ha.
        * (* TODO: redundant case *) admit.
        * (* TODO: redundant case *) admit.
        * destruct (IH u''_r H') as [w_r [H'' H''']]. exists (u_l⋅w_r).
          split; apply strictOneStepReflRedR; assumption.
    - subst. exists v. split; [right | left]; auto.
    - subst. exists v'. split; [left | right]; auto.
    - exists u. subst. split; right; auto.
  Qed.

  Lemma strictRedConfluence : REL_RES.Dp _ StrictRed.
  Proof. apply REL_RES.dpReflClos_confluence. apply strictOneStepReflRedDp. Qed.

  Lemma strictRedL : forall u u' v, u >>>* u' -> u⋅v >>>* u'⋅v.
  Proof.
    intros u u' v H. generalize dependent v.
    induction H as [u u' H | u | u u' u'' _ IHL _ IHR]; intro v.
    - apply rt_step. apply strictOneStepRedL. assumption.
    - apply rt_refl.
    - specialize (IHL v). specialize (IHR v).
      apply rt_trans with (y := u'⋅v); assumption.
  Qed.

  Lemma strictRedR : forall u v v', v >>>* v' -> u⋅v >>>* u⋅v'.
  Proof.
    intros u v v' H. generalize dependent u.
    induction H as [v v' H | v | v v' v'' _ IHL _ IHR]; intro u.
    - apply rt_step. apply strictOneStepRedR. assumption.
    - apply rt_refl.
    - specialize (IHL u). specialize (IHR u).
      apply rt_trans with (y := u⋅v'); assumption.
  Qed.

  Lemma strictRedPar : forall u u' v v', u >>>* u' -> v >>>* v' -> u⋅v >>>* u'⋅v'.
  Proof.
    intros u u' v v' Hu Hv.
    apply rt_trans with (y := u'⋅v);
    [apply strictRedL | apply strictRedR]; assumption.
  Qed.

  Lemma normConcL : forall n n', Normal (n⋅n') -> Normal n.
  Proof.
    intros n n' H [t Ht]. eauto using OneStepRed.
  Qed.

  Lemma normConcR : forall n n', Normal (n⋅n') -> Normal n'.
  Proof.
    intros n n' H [t Ht]. eauto using OneStepRed.
  Qed.

  Reserved Notation "u >>>lr v" (at level 70, no associativity).
  Inductive StrictOneStepRedLeftRight : term -> term -> Prop :=
    strictOneStepRedLeftRightL u u' v : u >>> u' -> u⋅v >>>lr u'⋅v
  | strictOneStepRedLeftRightR u v v' : v >>> v' -> u⋅v >>>lr u⋅v'
  where "u >>>lr v" := (StrictOneStepRedLeftRight u v).

  Definition StrictRedLeftRight := StrictOneStepRedLeftRight+.
  Infix ">>>lr*" := StrictRedLeftRight (at level 70, no associativity).

  Lemma strictRedLeftRightL : forall u v u' v', u⋅v >>>lr* u'⋅v' -> u >>>* u'.
  Proof.
    intros u v u' v' H. apply REL_RES.nChain_clos_refl_trans in H.
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

  Lemma StrictRedLeftRightR : forall u v u' v', u⋅v >>>lr* u'⋅v' -> v >>>* v'.
  Proof.
    intros u v u' v' H. apply REL_RES.nChain_clos_refl_trans in H.
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

  Lemma lemma : forall u v w, u⋅v >>>lr* w -> exists u' v', w = u'⋅v'.
  Proof.
    intros u v w H. apply REL_RES.nChain_clos_refl_trans in H.
    destruct H as [m H].
    generalize dependent w. generalize dependent v. generalize dependent u.
    induction m as [ | m IH]; intros.
    - inversion_clear H. eauto.
    - inversion_clear H. specialize (IH u v b H0).
      destruct IH as [u' [v' H]]. subst. destruct H1; eauto.
  Qed.

  Lemma lemma' : forall u v w, u⋅v >>>* w ->
    u⋅v >>>lr* w
    \/ exists n n', Normal n /\ Normal n' /\ u >>>* n /\ v >>>* n' /\ n⋅n' >>>* w.
  Proof.
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
          { apply (StrictRedLeftRightR _ _ _ _ IH). }
          { apply rt_step. assumption. }
        * left. eapply rt_trans; eauto. apply rt_step.
          apply strictOneStepRedLeftRightL. assumption.
        * left. eapply rt_trans; eauto. apply rt_step.
          apply strictOneStepRedLeftRightR. assumption.
      + right. destruct IH as [n [n' IH]]. exists n, n'.
        repeat split; try tauto. apply rt_trans with (y := b); [tauto | ].
        apply rt_step. assumption.
  Qed.

  Lemma lemma'' : forall u v n, u⋅v >>>* n -> Normal n -> exists n' n'',
    SNF u n' /\ SNF v n'' /\ n'⋅n'' >>>* n.
  Proof.
    intros u v n H Hn. apply lemma' in H.
    destruct H as [H | [n' [n'' [Hn' [Hn'' [H [H' H'']]]]]]].
    - destruct (lemma u v n H) as [n' [n'' H']]. subst.
      exists n', n''. split; [ | split].
      + split; [ | apply (normConcL _ _ Hn)]. apply (strictRedLeftRightL _ _ _ _ H).
      + split; [ | apply (normConcR _ _ Hn)]. apply (StrictRedLeftRightR _ _ _ _ H).
      + apply rt_refl.
    - exists n', n''. repeat split; auto.
  Qed.

  Fixpoint closedPasTermToTerm (t : @PAS.term termPas 0) : term := match t with
  | &a            => let (a, _) := a in a
  | PAS.termVar x => False_rect _ (FIN.t0Empty x)
  | u*v           => closedPasTermToTerm u ⋅ closedPasTermToTerm v
  end.

  Local Notation "$ t" := (closedPasTermToTerm t) (at level 6).

  Lemma concatenationLemma (u : @PAS.term termPas 0) (v : normalTerm) :
    $ u >>>* v -> u ≃ &v.
  Proof.
    generalize dependent v.
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
  Qed.

  Lemma concatenationLemma' :
    forall (u : @PAS.term termPas 0) (v : normalTerm), (u ≃ &v) <-> SNF $ u v.
  Proof.
    intro u. induction u as [u | x | u IHu v IHv].
    - intro n. split; intro H.
      + apply PAS.termConstInjective in H.
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
      + intros [H Hn]. apply (concatenationLemma (u*v)) in H.
        setoid_rewrite PAS.correctness1 in H. exact H.
  Qed.

  Lemma concatenationLemma'' (u v : @PAS.term termPas 0) :
    $ u >>>* $ v -> u ≃ v.
  Proof.
    intro H. apply PAS.correctness2. intro v'.
    setoid_rewrite concatenationLemma'.
    split; intro H'; destruct H' as [H' _], v' as [v' Hv']; simpl in *.
    - split; [ | exact Hv'].
      destruct (strictRedConfluence $ u $ v v' H H') as [w [H'' H''']].
      assert (v' = w) as H4. {
        apply strictRed_red in H'''. apply normalRed in H'''; assumption.
      }
      subst. assumption.
    - split; [ | exact Hv']. apply rt_trans with (y := $ v); assumption.
  Qed.

  Definition k : normalTerm := exist _ _ kNormal.
  Definition s : normalTerm := exist _ _ sNormal.

  Instance termPca : PCA.Pca := {
    pas := termPas;
    k := k;
    s := s
  }.
  Proof.
    - discriminate.
    - intros [u Hu] [v Hv]. apply concatenationLemma''.
      apply rt_step. simpl. apply strictOneStepRedConc.
      + apply ktNormal. exact Hu.
      + exact Hv.
      + apply oneStepRedK.
    - intros [u Hu] [v Hv].
      set (suv := exist _ _ (suvNormal _ _ Hu Hv) : normalTerm).
      exists suv. apply concatenationLemma''. apply rt_refl.
    - intros [u Hu] [v Hv] [w Hw].
      apply concatenationLemma''. simpl.
      apply rt_step. apply strictOneStepRedConc.
      + apply suvNormal; assumption.
      + exact Hw.
      + apply oneStepRedS.
  Qed.

  Module NOTATIONS.

    Delimit Scope TERM_PCA with TERM_PCA.

    Infix "⋅" :=
      (fun u v => u ⋅ v) (at level 40, left associativity) : TERM_PCA.
    Infix ">" := (fun u v => u > v) (at level 70) : TERM_PCA.
    Infix ">*" := (fun u v => u >* v) (at level 70) : TERM_PCA.
    Infix ">>" := (fun u v => u >> v) (at level 70) : TERM_PCA.
    Infix ">>*" := (fun u v => u >>* v) (at level 70) : TERM_PCA.
    Infix ">>=" := (fun u v => u >>= v) (at level 70) : TERM_PCA.
    Infix ">>>" := (fun u v => u >>> v) (at level 70) : TERM_PCA.
    Infix ">>>*" := (fun u v => u >>>* v) (at level 70) : TERM_PCA.
    Infix ">>>lr" := (fun u v => u >>>lr v) (at level 70) : TERM_PCA.
    Infix ">>lr*" := (fun u v => u >>>lr* v) (at level 70) : TERM_PCA.
    Notation "$ t" := ($ t) (at level 6) : TERM_PCA.

  End NOTATIONS.

End TERM_PCA.

Module TERM_PCA_COERCIONS.
  Import TERM_PCA.
  Coercion normalTermsToTerms : normalTerm >-> term.
End TERM_PCA_COERCIONS.
