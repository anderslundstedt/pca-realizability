(**
* Some results relating to rewriting systems
The proof that the diamond property for
the reflexive closure implies closure follows
``Polishing up the Tait--Martin-Lof proof of the Church--Rosser theorem''
(Robert Pollack 1995).
*)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.

Module RW.

  (**
  ** Definitions
  *)

  (**
  *** Reflexive closure
  *)

  Definition ReflexiveClosure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
    fun a b => R a b \/ a = b.
  Local Notation RC := ReflexiveClosure.

  (**
  *** Reflexive transitive closure
  *)

  Local Notation RTC := (clos_refl_trans _).

  (**
  *** Generalized diamond property
  *)

  Definition GeneralizedDiamondProperty {A} (R S : A -> A -> Prop) : Prop :=
    forall a b c : A, R a b -> S a c -> exists d : A, S b d /\ R c d.
  Local Notation GDP := GeneralizedDiamondProperty.

  (**
  *** Diamond property
  *)

  Definition DiamondProperty {A} (R : A -> A -> Prop) : Prop := GDP R R.
  Local Notation DP := DiamondProperty.

  (**
  *** Confluence
  *)

  Definition Confluence {A} (R : A -> A -> Prop) := DP (RTC R).

  (**
  *** Functional relation
  *)

  Definition Functional {A} (R : A -> A -> Prop) : Prop :=
    forall a b c : A, R a b -> R a c -> b = c.

  (**
  *** Normal elements and normal forms
  *)

  Definition Normal {A} (R : A -> A -> Prop) (a : A) : Prop :=
    ~ exists b : A, R a b.

  Definition NormalForm {A} (R : A -> A -> Prop) (a b : A) : Prop :=
    RTC R a b /\ Normal R b.
  Local Notation NF := NormalForm.

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Notation RC := RC.
    Notation RTC := RTC.
    Notation GDP := GDP.
    Notation DP := DP.
    Notation NF := NF.

  End NOTATIONS.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    Axiom rtcExtensive :
      forall {A} (R : A -> A -> Prop) (a b : A), R a b -> RTC R a b.

    Axiom rtcIncreasing :
      forall {A} (R S : A -> A -> Prop),
      (forall a b : A, R a b -> S a b) ->
      (forall a b : A, RTC R a b -> RTC S a b).

    (**
    *** Diamond property implies confluence
    *)

    Axiom dp_confluence : forall {A} (R : A -> A -> Prop), DP R -> Confluence R.

    (**
    *** Diamond property of reflexive closure implies confluence
    *)

    Axiom dpReflClos_confluence :
      forall {A} (R : A -> A -> Prop), DP (RC R) -> Confluence R.

    (**
    *** Functional relations are confluent
    *)

    Axiom functionalRelation_confluence :
      forall {A} (R : A -> A -> Prop), Functional R -> Confluence R.

    (**
    *** Normal reduction is trivial
    *)

    Axiom normalReductionTrivial :
      forall {A} (R : A -> A -> Prop) (a b : A),
      Normal R a -> RTC R a b -> a = b.

    (**
    *** Normal forms are unique for confluent relations
    *)

    Axiom confluence_normalFormsUnique :
      forall {A} (R : A -> A -> Prop),
      Confluence R -> forall a b c : A, NF R a b -> NF R a c -> b = c.

    Axiom functionalDoubleReduction :
      forall {A} (R : A -> A -> Prop),
      Functional R ->
      forall a b c : A, RTC R a b -> RTC R a c -> RTC R b c \/ RTC R c b.

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Theorem rtcExtensive {A} (R : A -> A -> Prop) (a b : A) : R a b -> RTC R a b.
    Proof. auto using rt_step. Qed.

    Theorem rtcIncreasing {A} (R S : A -> A -> Prop) :
      (forall a b : A, R a b -> S a b) ->
      (forall a b : A, RTC R a b -> RTC S a b).
    Proof.
      intros H a b H'.
      induction H';
      [auto using rt_step | apply clos_rt_is_preorder | eauto using rt_trans].
    Qed.

    Lemma gdpCommutative {A} (R S : A -> A -> Prop) : GDP R S -> GDP S R.
    Proof. intros H a b c HR HS. specialize (H a c b HS HR). firstorder. Qed.

    Definition StripProperty {A} (f : (A -> A -> Prop) -> (A -> A -> Prop)) :=
      forall R S : (A -> A -> Prop), GDP R S -> GDP R (f S).
    Local Notation Strip := StripProperty.

    Definition StripsProperty {A} (f : (A -> A -> Prop) -> (A -> A -> Prop)) :=
      forall R S : (A -> A -> Prop), GDP R S -> GDP (f R) (f S).
    Local Notation Strips := StripsProperty.

    Lemma strip_strips {A} (f : (A -> A -> Prop) -> (A -> A -> Prop)) :
      Strip f -> Strips f.
    Proof. unfold Strips. auto using gdpCommutative. Qed.

    Lemma rtcStrip {A} : Strip (clos_refl_trans A).
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

    Theorem dp_confluence {A} (R : A -> A -> Prop) : DP R -> Confluence R.
    Proof. apply strip_strips. apply rtcStrip. Qed.

    Theorem dpReflClos_confluence {A} (R : A -> A -> Prop) :
      DP (RC R) -> Confluence R.
    Proof.
      set (R' := RC R).
      assert (forall u v, (RTC R') u v <-> (RTC R) u v) as H. {
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

    Theorem functionalDoubleReduction {A} (R : A -> A -> Prop) :
      Functional R ->
      forall a b c : A, RTC R a b -> RTC R a c -> RTC R b c \/ RTC R c b.
    Proof.
      setoid_rewrite clos_rt_rt1n_iff.
      intros HR a b c Hab Hac.
      induction Hab as [a | a a' b Haa' Ha'b IH]; [tauto | ].
      destruct Hac as [ | a'' c Haa'' Ha''c].
      - right. apply rt1n_trans with (y := a').
        + exact Haa'.
        + exact Ha'b.
      - specialize (HR _ _ _ Haa' Haa''). subst. apply IH. exact Ha''c.
    Qed.

    Theorem functionalRelation_confluence {A} (R : A -> A -> Prop) :
      Functional R -> Confluence R.
    Proof.
      intros H a b c Hab Hac.
      destruct (functionalDoubleReduction _ H _ _ _ Hab Hac); firstorder.
    Qed.

    Theorem normalReductionTrivial {A} (R : A -> A -> Prop) (a b : A) :
      Normal R a -> RTC R a b -> a = b.
    Proof.
      intros H H'.
      induction H' as [U V H' | U H' | U V W _ IHL _ IHR].
      - exfalso. eauto.
      - reflexivity.
      - specialize (IHL H). subst. exact (IHR H).
    Qed.

    Theorem confluence_normalFormsUnique {A} (R : A -> A -> Prop) :
      Confluence R -> forall a b c : A, NF R a b -> NF R a c -> b = c.
    Proof.
      intros H a b c [Hab Hb] [Hac Hc].
      destruct (H _ _ _ Hab Hac) as [d [Hbd Hcd]].
      apply (normalReductionTrivial _ _ _ Hb) in Hbd.
      apply (normalReductionTrivial _ _ _ Hc) in Hcd.
      congruence.
    Qed.

  End THMS.

End RW.
