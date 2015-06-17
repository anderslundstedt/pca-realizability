(**
* Some results on relation operators
Taken from
``Polishing up the Tait--Martin-Lof proof of the Church--Rosser theorem''
(Robert Pollack 1995).
*)

Require Import Relations.
Require Import Relation_Operators.

Module REL_RES.

  Local Notation "R +" := (clos_refl_trans _ R) (at level 5).

  Section RelationResults.

    Variable A : Type.
    Local Notation Rel := (relation A).

    (**
    ** Definitions
    *)

    (**
    *** Reflexive closure
    *)

    Definition ReflexiveClosure (R : Rel) a b := R a b \/ a = b.

    (**
    *** Generalized diamond property
    *)

    Definition Gdp (R S : Rel) : Prop :=
      forall a b b', R a b -> S a b' -> exists c : A, S b c /\ R b' c.

    (**
    *** Diamond property
    *)

    Definition Dp (R : Rel) : Prop := Gdp R R.

    (**
    *** Confluence
    *)

    Definition Confluence (R : relation A) := Dp R+.

    (**
    *** Strip property
    *)

    Definition strip (f : Rel -> Rel) :=
      forall R S : Rel, Gdp R S -> Gdp R (f S).

    (**
    *** Strips property
    *)

    Definition strips (f : relation A -> relation A) :=
      forall R S : Rel, Gdp R S -> Gdp (f R) (f S).

    (**
    *** Relation chains
    The [R]-chain of length [n] relates two elements [a0] and [an]
    if there is [a_1,...,a(n-1)] such that
    [a0Ra1R...Ra(n-1)Ran].
    *)

    Inductive nChain (R : Rel) : nat -> A -> A -> Prop :=
    | nChain0 a       : nChain R 0 a a
    | nChainS n a b c : nChain R n a b -> R b c -> nChain R (S n) a c.

    (**
    ** Results
    *)

    (**
    *** Commutativity of generalized diamond property
    *)

    Lemma gdpCommutative (R S : Rel) : Gdp R S -> Gdp S R.
    Proof. intros H a b c H' H''. specialize (H a c b H'' H'). firstorder. Qed.

    (**
    *** Strip property implies strips property
    *)

    Lemma strip_strips (f : Rel -> Rel) : strip f -> strips f.
    Proof. unfold strips. auto using gdpCommutative. Qed.

    (**
    *** Transitive reflexive closure is extensive
    *)

    Lemma clos_refl_transExtensive (R : Rel) : inclusion _ R R+.
    Proof. unfold inclusion. auto using rt_step. Qed.

    (**
    *** Transitive reflexive closure is increasing
    *)

    Lemma clos_refl_transIncreasing (R S : Rel) :
      inclusion _ R S -> inclusion _ R+ S+.
    Proof.
      intros H a b H'.
      induction H';
        [auto using rt_step | apply clos_rt_is_preorder | eauto using rt_trans].
    Qed.

    (**
    *** Transitive reflexive closure has the strip property
    *)

    Lemma clos_refl_transStrip : strip (clos_refl_trans A).
    Proof.
      intros R S H.
      apply gdpCommutative.
      apply gdpCommutative in H.
      intros a b c H'. generalize dependent c.
      induction H' as [a b H' | a | a b' b HL IHL HR IHR].
      - intros c H''.
        destruct (H a b c H' H'') as [d [H''' H4]]. eauto using rt_step.
      - eauto using rt_refl.
      - intros c H'.
        destruct (IHL c H') as [b'' [H'' H''']].
        destruct (IHR b'' H'') as [d [H4 H5]]. eauto using rt_trans.
    Qed.

    (**
    *** Diamond property implies confluence
    *)

    Theorem dp_confluence (R : Rel) : Dp R -> Confluence R.
    Proof. apply strip_strips. apply clos_refl_transStrip. Qed.

    (**
    *** Diamond property of reflexive closure implies confluence
    *)

    Theorem dpReflClos_confluence (R : Rel) :
      Dp (ReflexiveClosure R) -> Confluence R.
    Proof.
      set (R' := ReflexiveClosure R).
      assert (forall u v, R'+ u v <-> R+ u v) as H. {
        intros u v. split; intro H.
        - induction H.
          + inversion_clear H.
            * apply rt_step; assumption.
            * subst. apply rt_refl.
          + apply rt_refl.
          + eauto using rt_trans.
        - induction H.
          + apply rt_step. left. assumption.
          + apply rt_refl.
          + eauto using rt_trans.
      }
      intros H' u v v' H'' H'''. apply H in H''. apply H in H'''.
      destruct (dp_confluence _  H' u v v' H'' H''') as [w [Hvw Hv'w]].
      apply H in Hvw. apply H in Hv'w. eauto.
    Qed.

    (**
    *** Equivalence between reflexive transitive closure and chains
    *)

    Theorem nChain_clos_refl_trans R a b : R+ a b <-> exists n, nChain R n a b.
    Proof.
      split; intro H.
      - induction H as [a b H | a | a b c HL [n IHL] HR [m IHR]].
        + exists 1. apply nChainS with (b := a); [constructor | assumption].
        + exists 0. constructor.
        + clear HR. generalize dependent c. induction m as [ | m IH]; intros.
          * exists n. inversion IHR. subst. exact IHL.
          * inversion IHR. subst. clear IHR.
            specialize (IH b0 H0). destruct IH as [n' IH]. exists (S n').
            apply nChainS with (b := b0); assumption.
      - destruct H as [n H]. generalize dependent b.
        induction n as [ | n IH]; intros b H.
        + inversion_clear H. apply rt_refl.
        + inversion_clear H. specialize (IH b0 H0).
          apply rt_trans with (y := b0).
          * exact IH.
          * apply rt_step. exact H1.
    Qed.

  End RelationResults.

  (**
  ** Notations
  *)

  Module NOTATIONS.
    Delimit Scope REL_RES with REL_RES.
    Notation "R +" := R+ (at level 5) : REL_RES.
  End NOTATIONS.

End REL_RES.
