(**
* Partial applicative structures
*)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.

Require Import fin.
Require Import vec.

Import FIN.NOTATIONS.
Import VEC.NOTATIONS.

Local Open Scope VEC.

Module PAS.

  (**
  ** Definition
  For generality,
  the carrier is a setoid and
  application is a ternary relation that is
  functional with respect to the setoid equality.
  *)

  Local Reserved Infix "==" (at level 70).
  Class Pas := {
    carrier : Type;
    CarrierEq :
      carrier -> carrier -> Prop where "a == b" := (CarrierEq a b) : Pas;
    carrierEqEquivalence :> Equivalence CarrierEq;
    Appl : carrier -> carrier -> carrier -> Prop;
    applRespectful (a a' b b' c c' : carrier) :
      a == a' -> b == b' -> c == c' -> Appl a b c -> Appl a' b' c';
    applFunctional (a b c d : carrier) :  Appl a b c -> Appl a b d -> c == d
  }.
  Local Coercion carrier : Pas >-> Sortclass.
  Local Infix "==" := CarrierEq.

  Instance applProper {pas : Pas} :
    Proper (CarrierEq ==> CarrierEq ==> CarrierEq ==> iff) Appl.
  Proof.
    intros a a' Ha b b' Hb c c' Hc.
    split; [ | symmetry in Ha, Hb, Hc]; eauto using applRespectful.
  Qed.

  (**
  ** Terms
  *)

  Inductive term {pas : Pas} (n : nat) :=
  | const : pas -> term n
  | var   : FIN.t n -> term n
  | appl  : term n -> term n -> term n.
  Arguments const {_} {_} _.
  Arguments var {_} {_} _.
  Arguments appl {_} {_} _ _.
  Local Notation "& t" := (const t) (at level 6).
  Local Infix "*" := appl (at level 40, left associativity).

  Definition lastVar {_ : Pas} {n} : term (S n) := var FIN.last.

  Definition x01 {_ : Pas} : term 1 := var (FIN.ofNat 0 0).
  Definition x02 {_ : Pas} : term 2 := var (FIN.ofNat 0 1).
  Definition x12 {_ : Pas} : term 2 := var (FIN.ofNat 1 0).
  Definition x03 {_ : Pas} : term 3 := var (FIN.ofNat 0 2).
  Definition x13 {_ : Pas} : term 3 := var (FIN.ofNat 1 1).
  Definition x23 {_ : Pas} : term 3 := var (FIN.ofNat 2 0).
  Definition x04 {_ : Pas} : term 4 := var (FIN.ofNat 0 3).
  Definition x14 {_ : Pas} : term 4 := var (FIN.ofNat 1 2).
  Definition x24 {_ : Pas} : term 4 := var (FIN.ofNat 2 1).
  Definition x34 {_ : Pas} : term 4 := var (FIN.ofNat 3 0).
  Definition x05 {_ : Pas} : term 5 := var (FIN.ofNat 0 4).
  Definition x15 {_ : Pas} : term 5 := var (FIN.ofNat 1 3).
  Definition x25 {_ : Pas} : term 5 := var (FIN.ofNat 2 2).
  Definition x35 {_ : Pas} : term 5 := var (FIN.ofNat 3 1).
  Definition x45 {_ : Pas} : term 5 := var (FIN.ofNat 4 0).

  Fixpoint closedTermToTerm `{_ : Pas} {n} (t : term 0) : term n :=
  match t with
  | &a    => &a
  | var x => False_rect _ (FIN.t0Empty x)
  | u*v   => closedTermToTerm u * closedTermToTerm v
  end.
  Local Notation "§ t" := (closedTermToTerm t) (at level 6).

  Lemma closedTermToClosedTermEq {_ : Pas} (t : term 0) : §t = t.
  Proof.
    induction t as [a | x | u IHu v IHv]; simpl.
    - reflexivity.
    - inversion x.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  (**
  ** Vectors of terms
  *)

  Definition pasVecToTermVec {pas : Pas} {m n : nat} (f : VEC.t pas n)
    : VEC.t (term m) n := VEC.map const f.
  Local Notation "&& P" := (pasVecToTermVec P) (at level 6).

  Definition idVec {_ : Pas} {n} k : VEC.t (term (k + n)) n := VEC.finMap' var.

  (**
  ** Substitution
  *)

  Fixpoint substitution `{_ : Pas} {m n : nat} (t : term n)
                        (f : VEC.t (term m) n) : term m :=
  match t with
  | &a    => &a
  | var x => VEC.nth f x
  | u*v   => substitution u f * substitution v f
  end.
  Local Infix "/" := substitution.

  Lemma substIdVecEq {pas : Pas} {n} (t : term n)
    : t / idVec 0 = t.
  Proof.
    induction t as [a | x | u IHu v IHv].
    - reflexivity.
    - unfold idVec, substitution. rewrite VEC.nthFinMapEq'. reflexivity.
    - simpl. setoid_rewrite IHu. setoid_rewrite IHv. reflexivity.
  Qed.

  Lemma closedTermSubstitutionEq {pas : Pas} {n m : nat} (t : term 0)
                                 (f : VEC.t (term m) n) :
    §t/f = §t.
  Proof.
    induction t as [a | x | u IHu v IHv]; simpl.
    - reflexivity.
    - inversion x.
    - rewrite IHu, IHv. reflexivity.
  Qed.

  Lemma closedTermSubstitutionEq0 {pas : Pas} {n : nat} (t : term 0)
                                  (f : VEC.t (term 0) n) :
    §t/f = t.
  Proof. rewrite closedTermSubstitutionEq. apply closedTermToClosedTermEq. Qed.

  Lemma emptySubstitutionEq {pas : Pas} {n} (t : term 0)
                               (f : VEC.t (term n) 0) :
    t/f = §t.
  Proof.
    rewrite <- closedTermToClosedTermEq at 1. apply closedTermSubstitutionEq.
  Qed.

  Definition termVecSubst {_ : Pas} {n m k} (f : VEC.t (term m) n)
                          (g : VEC.t (term k) m) : VEC.t (term k) n :=
    VEC.map (fun t => t/g) f.

  Lemma termVecSubstIdVecEq {n m k} {pas : Pas} (f : VEC.t (term m) n)
                            (g : VEC.t (term m) k) :
    termVecSubst (idVec k) (VEC.concat f g) = f.
  Proof.
    apply VEC.pointwiseEquality. intro x.
    unfold termVecSubst. rewrite VEC.nthMapEq.
    unfold idVec. rewrite VEC.nthFinMapEq'.
    simpl.
    induction k as [ | k IHk].
    - reflexivity.
    - destruct g as [g t]. simpl. apply IHk.
  Qed.

  (**
  ** Product of a term and a vector of terms
  *)

  Definition product {_ : Pas} {m n : nat} (t : term m) (f : VEC.t (term m) n)
    : term m := VEC.foldl appl t f.
  Local Infix "**" := product (at level 39, left associativity).

  Lemma doubleProductEq {pas : Pas} {n m k : nat} (t : term n)
                        (f : VEC.t (term n) m) (g : VEC.t (term n) k) :
    t ** f ** g = t ** (VEC.concat f g).
  Proof. unfold product. rewrite VEC.foldlConcatEq. reflexivity. Qed.

  Lemma productSubstitutionEq {pas : Pas} {n m k} (t : term m)
                              (f : VEC.t (term m) n) (g : VEC.t (term k) m) :
    (t ** f) / g = (t/g) ** (termVecSubst f g).
  Proof.
    induction n as [ | n IHn].
    - reflexivity.
    - destruct f as [f u].
      assert ((t ** (f;; u) /g = ((t ** f) / g) * (u / g))) as H by reflexivity.
      rewrite H, IHn. reflexivity.
  Qed.

  Lemma idVecProductSubstitutionEq {pas : Pas} {n m k} (t : term (k + n))
                                   (f : VEC.t (term m) n)
                                   (g : VEC.t (term m) k) :
    (t ** idVec k) / VEC.concat f g = (t / VEC.concat f g) ** f.
  Proof. rewrite productSubstitutionEq, termVecSubstIdVecEq. reflexivity. Qed.

  Lemma idVecProductSubstitutionEq0 {pas : Pas} {n m} (t : term n)
                                    (f : VEC.t (term m) n) :
    (t ** idVec 0) / f = (t/f) ** f.
  Proof. apply (idVecProductSubstitutionEq (t : term (0 + n)) f ()). Qed.

  Lemma idVecProductSubstitutionEq0' {pas : Pas} {n} (t : term 0)
                                     (f : VEC.t (term 0) n) :
    (§t ** idVec 0) / f = t ** f.
  Proof.
    rewrite
      (idVecProductSubstitutionEq0 (n := n) (m := 0)),
      closedTermSubstitutionEq, closedTermToClosedTermEq.
    reflexivity.
  Qed.

  Lemma idVecProductSubstitutionEq1 {pas : Pas} {n m} (u : term (S n))
                                    (f : VEC.t (term m) n) (v : term m) :
    (u ** idVec 1) / (f;; v) = (u / (f;; v)) ** f.
  Proof.
    assert ((f;; v) = VEC.concat f (();; v)) as H by reflexivity.
    setoid_rewrite H. clear H.
    apply (idVecProductSubstitutionEq (u : term (1 + n))).
  Qed.

  Lemma idVecProductSubstitutionEq1' {pas : Pas} {n} (u v : term 0)
                                     (f : VEC.t (term 0) n) :
    (§u ** idVec 1) / (f;; v) = u ** f.
  Proof.
    assert ((f;; v) = VEC.concat f (();; v)) as H by reflexivity.
    setoid_rewrite H. clear H.
    rewrite
      idVecProductSubstitutionEq, closedTermSubstitutionEq,
      closedTermToClosedTermEq.
    reflexivity.
  Qed.

  (**
  ** Equivalence of closed terms
  *)

  Fixpoint Denotation `{pas : Pas} (t : term 0) (c : pas) : Prop :=
  match t with
  | &a    => a == c
  | u*v   => exists a b, Denotation u a /\ Denotation v b /\ Appl a b c
  | var _ => False
  end.

  Lemma denotationsUnique {pas : Pas} (t : term 0) (a b : pas) :
    Denotation t a -> Denotation t b -> a == b.
  Proof.
    generalize a, b. clear.
    induction t as [a' | x | u IHu v IHv]; simpl.
    - intros a b Ha Hb. rewrite <- Ha, Hb. reflexivity.
    - contradiction.
    - intros c c' [a [b [Hua [Hvb Habc]]]] [a' [b' [Hua' [Hvb' Habc']]]].
      specialize (IHu a a' Hua Hua').
      specialize (IHv b b' Hvb Hvb').
      rewrite IHu, IHv in Habc. apply (applFunctional a' b'); assumption.
  Qed.

  Definition ClosedTermEq {_ : Pas} (u v : term 0) : Prop :=
    forall a, Denotation u a <-> Denotation v a.
  Local Infix "≃" := ClosedTermEq (at level 70).

  Instance closedTermEqEquivalence {pas : Pas} : Equivalence ClosedTermEq.
  Proof. firstorder. Qed.

  Lemma denotationRespectful {pas : Pas} (u v : term 0) (a b : pas)
    : u ≃ v -> a == b -> Denotation u a -> Denotation v b.
  Proof.
    intros Huv Hab Hua.
    specialize (Huv a). destruct Huv as [Huv _]. specialize (Huv Hua).
    clear dependent u.
    destruct v as [c | | u v]; simpl in *.
    - rewrite Huv, Hab. reflexivity.
    - contradiction.
    - destruct Huv as [a' [b' [Hua' [Hvb' H]]]]. setoid_rewrite <- Hab. eauto.
  Qed.

  Instance denotationProper {pas : Pas} :
    Proper (ClosedTermEq ==> CarrierEq ==> iff) Denotation.
  Proof.
    intros u v Huv a b Hab. split; intro H.
    - apply (denotationRespectful u v a b); assumption.
    - apply (denotationRespectful v u b a); [symmetry | symmetry | ]; assumption.
  Qed.

  Lemma denotationClosedTermEq {pas : Pas} (t : term 0) (a : pas) :
    t ≃ &a <-> Denotation t a.
  Proof.
    split; intro H.
    - apply H. simpl. reflexivity.
    - intro a'. split; intro H'.
      + apply (denotationsUnique t); assumption.
      + assert (a == a') as Ha. {
          apply (denotationsUnique &a); [simpl; reflexivity | exact H'].
        }
        rewrite <- Ha. exact H.
  Qed.

  (**
  *** Correctness properties
  *)

  Instance constProper {pas : Pas} :
    Proper (CarrierEq ==> ClosedTermEq) const.
  Proof. intros a b Hab c. simpl. rewrite Hab. tauto. Qed.

  Instance applProper' {pas : Pas} :
    Proper (ClosedTermEq ==> ClosedTermEq ==> ClosedTermEq) appl.
  Proof.
    intros u u' Hu v v' Hv c. simpl. setoid_rewrite Hu. setoid_rewrite Hv.
    tauto.
  Qed.

  Lemma constInjective {pas : Pas} (a b : pas) : &a ≃ &b -> a == b.
  Proof. intro H. specialize (H b). simpl in H. apply H. reflexivity. Qed.

  Lemma correctness1 {pas : Pas} (u v : term 0) (c : pas) :
    u*v ≃ &c <-> exists a b : pas, u ≃ &a /\ v ≃ &b /\ Appl a b c.
  Proof.
    split.
    - intro H. specialize (H c). destruct H as [_ H]. simpl in H.
      lapply H; [clear H; intros [a [b [Hua [Hvb Habc]]]] | reflexivity].
      exists a, b. split; [ | split].
      + apply denotationClosedTermEq. exact Hua.
      + apply denotationClosedTermEq. exact Hvb.
      + exact Habc.
    - intros [a [b [Hua [Hvb Habc]]]].
      apply denotationClosedTermEq. simpl.
      rewrite denotationClosedTermEq in Hua, Hvb.
      eauto.
  Qed.

  Lemma correctness1' {pas : Pas} (a b c : pas) : &a*&b ≃ &c <-> Appl a b c.
  Proof.
    rewrite correctness1. split.
    - intros [a' [b' [Ha [Hb H]]]].
      apply constInjective in Ha. apply constInjective in Hb.
      rewrite Ha, Hb. exact H.
    - intro H. exists a, b. firstorder.
  Qed.

  Lemma correctness2 {pas : Pas} (u v : term 0) :
    u ≃ v <-> forall a : pas, u ≃ &a <-> v ≃ &a.
  Proof.
    split; intro H.
    - setoid_rewrite H. tauto.
    - setoid_rewrite denotationClosedTermEq in H. exact H.
  Qed.

  Global Opaque Denotation ClosedTermEq.

  (**
  ** Denoting closed terms
  *)

  Definition Denotes {pas : Pas} (t : term 0) : Prop := exists a : pas, t ≃ &a.
  Hint Unfold Denotes.
  Local Notation "t !" := (Denotes t) (at level 70).

  Instance denotesProper {pas : Pas} : Proper (ClosedTermEq ==> iff) Denotes.
  Proof. intros u v H. unfold Denotes. setoid_rewrite H. tauto. Qed.

  (**
  ** Subterms
  *)

  Inductive Subterm {pas : Pas} {n} : term n -> term n -> Prop :=
  | subtermRefl u     : Subterm u u
  | subtermL    u v w : Subterm u v -> Subterm u (v*w)
  | subtermR    u v w : Subterm u w -> Subterm u (v*w).
  Hint Constructors Subterm.

  Instance subtermReflexive {pas : Pas} {n} : Reflexive (Subterm (n := n)).
  Proof. auto. Qed.

  Instance subtermTransitive {pas : Pas} {n} : Transitive (Subterm (n := n)).
  Proof. intros u v w Huv Hvw. induction Hvw; auto. Qed.

  Lemma subtermDenotes {pas : Pas} (u v : term 0) :
    Subterm u v -> v! -> u!.
  Proof.
    intros H. induction H as [ | u v w H IH | u v w H IH].
    - tauto.
    - unfold Denotes. setoid_rewrite correctness1. firstorder.
    - unfold Denotes. setoid_rewrite correctness1. firstorder.
  Qed.

  Lemma subtermDenotesProduct {pas : Pas} {n : nat} (t : term 0)
                              (f : VEC.t (term 0) n) :
    t**f! -> t!.
  Proof.
    induction n as [ | n IHn].
    - destruct f. tauto.
    - destruct f as [f a]. intro H. apply (IHn f).
      apply subtermDenotes with (v := (t ** (f;; a))); [ | exact H].
      apply subtermL. reflexivity.
  Qed.

  (**
  ** Notations
  *)

  Module NOTATIONS.
    Delimit Scope PAS with PAS.
    Notation "§ t" := § t (at level 6) : PAS.
    Notation "& t" := &t (at level 6) : PAS.
    Notation "&& f" := &&f (at level 6) : PAS.
    Notation "t !" := (t!) (at level 70) : PAS.
    Infix "*" := appl : PAS.
    Infix "**" := product (at level 39, left associativity) : PAS.
    Infix "/" := substitution : PAS.
    Infix "==" := CarrierEq (at level 70) : PAS.
    Infix "≃" := ClosedTermEq (at level 70) : PAS.
  End NOTATIONS.

End PAS.

(**
** Coercions
*)

Module PAS_COERCIONS.
  Coercion PAS.carrier : PAS.Pas >-> Sortclass.
End PAS_COERCIONS.
