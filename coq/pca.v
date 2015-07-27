(**
* Partial combinatory algebras
*)

Require Coq.Arith.Minus.
Require Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Classes.SetoidClass.

Require Import fin.
Require Import pas.
Require Import vec.

Import FIN.NOTATIONS.
Import PAS.
Import PAS.NOTATIONS.
Import PAS.THMS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.
Local Open Scope PAS.

Module PCA.

  (**
  ** Definitions
  *)

  Class Pca `(pas : Pas) (k : carrier) (s : carrier) := {
    kSpec (a b : carrier) : &k*&a*&b ≃ &a;
    sSpec1 (a b : carrier) : &s*&a*&b!;
    sSpec2 (a b c: carrier) : &s*&a*&b*&c ≃ &a*&c*(&b*&c)
  }.

  Definition NonTrivial `(pca : Pca) : Prop := exists a b : carrier, ~ a == b.

  (**
  *** Identity combinator
  *)

  Definition identityCombinator `{_ : Pca} : term 0 := &s*&k*&k.
  Local Notation ι := identityCombinator.

  (**
  *** Term representations
  *)

  Definition representation' `{pca : Pca} {n : nat} (t : term (S n)) : term 0.
  Proof.
    induction n as [ | n IHn].
    - induction t as [a | x | u IHu v IHv].
      + exact (&k*&a).
      + exact ι.
      + exact (&s*IHu*IHv).
    - induction t as [a | x |u IHu v IHv].
      + exact (IHn (&k*&a)).
      + destruct x as [x | x].
        * exact (IHn (&k * var x)).
        * exact (IHn §ι).
      + set (i := idVec 0 (n := S n)).
        set (u' := §IHu ** i).
        set (v' := §IHv ** i).
        exact (IHn (&s*u'*v')).
  Defined.
  Local Notation λ' := representation'.

  Definition representation `{_ : Pca} {n : nat} : term n -> term 0 :=
  match n with
  | O   => fun t => t
  | S n => fun t => λ' t
  end.
  Local Notation λ := representation.

  (**
  *** κ combinator
  *)

  Definition kAltCombinator `{_ : Pca} : term 0 := &k*ι.
  Local Notation κ := kAltCombinator.

  (**
  *** Pairing combinator
  *)

  Definition pairingCombinator `{_ : Pca} : term 0 := λ (x23*x03*x13).
  Local Notation π := pairingCombinator.

  (**
  *** Projection combinators
  *)

  Definition leftProjectionCombinator `{_ : Pca} : term 0 := λ (x01*&k).
  Local Notation π1 := leftProjectionCombinator.

  Definition rightProjectionCombinator `{_ : Pca} : term 0 := λ (x01 * §κ).
  Local Notation π2 := rightProjectionCombinator.

  (**
  *** Combinators representing naturals
  *)

  Fixpoint natRepresentationCombinator `{_ : Pca} (n : nat) : term 0 :=
  match n with
  | O   => ι
  | S n => π * κ * (natRepresentationCombinator n)
  end.
  Local Notation "# n" := (natRepresentationCombinator n) (at level 5).

  (**
  *** Case combinator
  *)

  Definition caseCombinator `{_ : Pca} : term 0 := λ (§π1 * x23 * x03 * x13).
  Local Notation δ := caseCombinator.

  (**
  *** Successor combinator
  *)

  Definition successorCombinator `{_ : Pca} : term 0 := π * κ.
  Local Notation σ := successorCombinator.

  (**
  *** Predecessor combinator
  *)

  Definition predecessorCombinator `{_ : Pca} : term 0 :=
    λ (§π1 * x01 * §#0 * §π2 * x01).
  Local Notation ψ := predecessorCombinator.

  (**
  *** Fixed point combinator
  *)

  Definition fixedPointCombinator `{_ : Pca} : term 0 :=
    let u := λ (x12*(x02*x02*x12)) in u*u.
  Local Notation φ1 := fixedPointCombinator.

  (**
  *** Double fixed point combinator
  *)

  Definition doubleFixedPointCombinator `{_ : Pca} : term 0 :=
    let u := λ (x13*(x03*x03*x13)*x23) in u*u.
  Local Notation φ2 := doubleFixedPointCombinator.

  (**
  *** Primitive recursion combinator
  *)

(*
  Local Notation r' :=
    (λ (x25 * (§ψ * x35) * (x05 * x15 * x25 * (§ψ * x35) * &k))).
  Local Notation r :=
    (λ (§δ * (&k * x14) * (§r' * x04 * x14 * x24 * x34) * x34)).
*)
  Definition r' `{_ : Pca} :=
    (λ (x25 * (§ψ * x35) * (x05 * x15 * x25 * (§ψ * x35) * &k))).
  Definition r `{_ : Pca} :=
    (λ (§δ * (&k * x14) * (§r' * x04 * x14 * x24 * x34) * x34)).
  Definition primitiveRecursionCombinator `{_ : Pca} : term 0 :=
    λ (§φ2 * §r * x03 * x13 * x23 * &k).
  Local Notation ρ := primitiveRecursionCombinator.

  (**
  *** Addition combinator
  *)

  Definition additionCombinator `{_ : Pca} : term 0 :=
    λ (§ρ * x12 * (&k * §σ) * x02).
  Local Notation α := additionCombinator.

  (**
  *** Multiplication combinator
  *)

  Definition multiplicationCombinator `{_ : Pca} : term 0 :=
    λ (§ρ * §#0 * (&k * (§α * x12)) * x02).
  Local Notation μ := multiplicationCombinator.

  (**
  ** Notations
  *)

  Module NOTATIONS.

    Delimit Scope PCA with PCA.

    Notation ι := ι.
    Notation λ := λ.
    Notation κ := κ.
    Notation π := π.
    Notation π1 := π1.
    Notation π2 := π2.
    Notation δ := δ.
    Notation σ := σ.
    Notation ψ := ψ.
    Notation φ1 := φ1.
    Notation φ2 := φ2.
    Notation ρ := ρ.
    Notation α := α.
    Notation μ := μ.
    Notation "# n" := #n : PCA.

  End NOTATIONS.

  (**
  ** Theorems
  *)

  Module Type THMS_SIG.

    (**
    *** Immediate consequenses of axioms
    *)

    Axiom kSpec' : forall `{_ : Pca} (t : term 0) (b : carrier), &k*t*&b ≃ t.

    Axiom kaDenotes : forall `{_ : Pca} (a : carrier), &k*&a!.

    Axiom sSpec2' : forall `{_ : Pca} (u v w : term 0), &s*u*v*w ≃ u*w*(v*w).

    Axiom saDenotes : forall `{_ : Pca} (a : carrier), &s*&a!.

    (**
    *** Nontrivial if and only if k and s are distinct
    *)

    Axiom ksDistinctIffNonTrivial :
      forall `{pca : Pca}, ~ k == s <-> NonTrivial pca.

    (**
    *** Combinatory completeness
    *)

    Axiom combinatoryCompleteness1 :
      forall `{_ : Pca} {n : nat} (t : term (S n)) (f : VEC.t carrier n),
      λ t ** &&f !.

    Axiom combinatoryCompleteness2 :
      forall `{_ : Pca} {n : nat} (t : term n) (f : VEC.t carrier n),
      λ t ** &&f ≃ t/&&f.

    Axiom combinatoryCompleteness1' :
      forall `{_ : Pca} {n : nat} (t : term (S n)) (f : VEC.t (term 0) n),
      (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f !.

    Axiom combinatoryCompleteness2' :
      forall `{_ : Pca} {n : nat} (t : term n) (f : VEC.t (term 0) n),
      (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f ≃ t / f.

    Axiom combinatoryCompletenessInstance1 :
      forall `{_ : Pca} (t : term 1) (a : carrier), λ t * &a ≃ t / &&((();; a)).

    Axiom combinatoryCompletenessInstance2 :
      forall `{_ : Pca} (t : term 2) (a b : carrier),
      λ t * &a * &b ≃ t / &&((();; a;; b)).

    Axiom combinatoryCompletenessInstance3 :
      forall `{_ : Pca} (t : term 3) (a b c : carrier),
      λ t * &a * &b * &c ≃ t / &&((();; a;; b;; c)).

    Axiom combinatoryCompletenessInstance4 :
      forall `{_ : Pca} (t : term 4) (a b c d : carrier),
      λ t * &a * &b * &c * &d ≃ t / &&((();; a;; b;; c;; d)).

    Axiom combinatoryCompletenessInstance5 :
      forall `{_ : Pca} (t : term 5) (a b c d e: carrier),
      λ t * &a * &b * &c * &d * &e ≃ t / &&((();; a;; b;; c;; d;; e)).

    (**
    *** Representations denote
    *)

    Axiom representationsDenote :
      forall `{_ : Pca} {n : nat} (t : term (S n)), λ t !.

    Axiom representationsDenote' :
      forall `{_ : Pca} {n m : nat} (t : term (S (m + n)))
             (f : VEC.t carrier n),
      λ t ** &&f!.

    Axiom representationsDenote'' :
      forall `{_ : Pca} {n m : nat} (t : term (S n)) (f : VEC.t carrier m),
      Compare_dec.leb m n = true -> λ t ** &&f!.

    (**
    *** Properties and correctness of combinators
    *)

    Axiom identityCombinatorCorrect :
      forall `{_ : Pca} (a : carrier), ι*&a ≃ &a.

    Axiom identityCombinatorCorrect' : forall `{_ : Pca} (t : term 0), ι*t ≃ t.

    Axiom identityCombinatorDenotes : forall `{_ : Pca}, ι!.

    Axiom kAltCombinatorCorrect :
      forall `{_ : Pca} (a b : carrier), κ*&a*&b ≃ &b.

    Axiom kAltCombinatorCorrect' :
      forall `{_ : Pca} (a : carrier) (t : term 0), κ*&a*t ≃ t.

    Axiom kAltCombinatorDenotes : forall `{_ : Pca}, κ!.

    Axiom kAltCombinatorDenotes' : forall `{_ : Pca} (a : carrier), κ*&a!.

    Axiom pairingCombinatorDenotes : forall `{_ : Pca}, π!.

    Axiom pairingCombinatorDenotes' : forall `{_ : Pca} (a : carrier), π*&a!.

    Axiom pairingCombinatorDenotes'':
      forall `{_ : Pca} (a b : carrier), π*&a*&b!.

    Axiom leftProjectionCombinatorCorrect :
      forall `{_ : Pca} (a b : carrier), π1*(π*&a*&b) ≃ &a.

    Axiom leftProjectionCombinatorCorrect' :
      forall `{_ : Pca} (t : term 0) (b : carrier), π1*(π*t*&b) ≃ t.

    Axiom leftProjectionCombinatorDenotes : forall `{_ : Pca}, π1!.

    Axiom rightProjectionCombinatorCorrect :
      forall `{_ : Pca} (a b : carrier), π2*(π*&a*&b) ≃ &b.

    Axiom rightProjectionCombinatorCorrect' :
      forall `{_ : Pca} (a : carrier) (t : term 0), π2*(π*&a*t) ≃ t.

    Axiom rightProjectionCombinatorDenotes : forall `{_ : Pca}, π2!.

    Axiom natRepresentationCombinatorDenotes : forall `{_ : Pca} (n : nat), #n!.

    Axiom caseCombinatorCorrect0 :
      forall `{_ : Pca} (a b : carrier), δ*&a*&b*#0 ≃ &a.

    Axiom caseCombinatorCorrect0' :
      forall `{_ : Pca} (t : term 0) (b : carrier), δ*t*&b*#0 ≃ t.

    Axiom caseCombinatorCorrectS :
      forall `{_ : Pca} (n : nat) (a b : carrier), δ*&a*&b*#(S n) ≃ &b.

    Axiom caseCombinatorCorrectS' :
      forall `{_ : Pca} (a : carrier) (t : term 0) (x : nat), δ*&a*t*#(S x) ≃ t.

    Axiom caseCombinatorDenotes : forall `{_ : Pca}, δ!.

    Axiom caseCombinatorDenotes' : forall `{_ : Pca} (a : carrier), δ*&a!.

    Axiom caseCombinatorDenotes'' : forall `{_ : Pca} (a b : carrier), δ*&a*&b!.

    Axiom successorCombinatorCorrect :
      forall `{_ : Pca} (n : nat), σ*#n ≃ #(S n).

    Axiom successorCombinatorDenotes : forall `{_ : Pca}, σ!.

    Axiom successorCombinatorDenotes' : forall `{_ : Pca} (n : nat), σ*#n!.

    Axiom predecessorCombinatorCorrect0 : forall `{_ : Pca}, ψ*#0 ≃ #0.

    Axiom predecessorCombinatorCorrectS :
      forall `{_ : Pca} (n : nat), ψ*#(S n) ≃ #n.

    Axiom predecessorCombinatorCorrect :
      forall `{_ : Pca} (n : nat), ψ*#n ≃ #(n-1).

    Axiom predecessorCombinatorDenotes :
      forall `{_ : Pca}, ψ!.

    Axiom fixedPointCombinatorCorrect :
      forall `{_ : Pca} (a : carrier), φ1*&a ≃ &a*(φ1*&a).

    Axiom fixedPointCombinatorCorrect' :
      forall `{_ : Pca} (t : term 0), φ1*t ≃ t*(φ1*t).

    Axiom doubleFixedPointCombinatorCorrect :
      forall `{_ : Pca} (a b : carrier), φ2*&a*&b ≃ &a*(φ2*&a)*&b.

    Axiom doubleFixedPointCombinatorDenotes : forall `{_ : Pca}, φ2!.

    Axiom doubleFixedPointCombinatorDenotes' :
      forall `{_ : Pca} (a : carrier), φ2*&a!.

    Axiom primitiveRecursionCombinatorCorrect0 :
      forall `{_ : Pca} (a b : carrier), ρ*&a*&b*#0 ≃ &a.

    Axiom primitiveRecursionCombinatorCorrectS :
      forall `{_ : Pca} (a b : carrier) (x : nat),
      ρ*&a*&b*#(S x) ≃ &b*#x*(ρ*&a*&b*#x).

    Axiom primitiveRecursionCombinatorDenotes : forall `{_ : Pca}, ρ!.

    Axiom primitiveRecursionCombinatorDenotes' :
      forall `{_ : Pca} (a : carrier), ρ*&a!.

    Axiom primitiveRecursionCombinatorDenotes'' :
      forall `{_ : Pca} (a b : carrier), ρ*&a*&b!.

    Axiom additionCombinatorCorrect :
      forall `{_ : Pca} (x y : nat), α*#x*#y ≃ #(x + y).

    Axiom additionCombinatorDenotes : forall `{_ : Pca}, α!.

    Axiom additionCombinatorDenotes' : forall `{_ : Pca} (x : nat), α*#x!.

    Axiom multiplicationCombinatorCorrect :
      forall `{_ : Pca} (x y : nat), μ*#x*#y ≃ #(x * y).

    Axiom multiplicationCombinatorDenotes' :
      forall `{_ : Pca} (x : nat), μ*#x!.

    Axiom multiplicationCombinatorDenotes :
      forall `{_ : Pca}, μ!.

    (**
    *** Arithmetic correct in nontrivial PCAs
    *)

    Axiom correctArithmetic :
      forall `{pca : Pca} (x y : nat), NonTrivial pca -> #x ≃ #y -> x = y.

  End THMS_SIG.

  (**
  ** Proofs
  *)

  Module THMS : THMS_SIG.

    Theorem kSpec' `{pca : Pca} (t : term 0) (b : carrier) : &k*t*&b ≃ t.
    Proof.
      apply PAS.THMS.correctness2. intro a. split; intro H.
      - assert (&k*t*&b!) as H' by eauto.
        assert (t!) as [a' Ht] by eauto using subtermDenotes.
        rewrite <- H, Ht. symmetry. apply kSpec.
      - rewrite H. apply kSpec.
    Qed.

    Theorem kaDenotes `{pca : Pca} (a : carrier) : &k*&a!.
    Proof. cut (&k*&a*&a!); eauto using subtermDenotes, kSpec. Qed.

    Theorem sSpec2' `{pca : Pca} (u v w : term 0) : &s*u*v*w ≃ u*w*(v*w).
    Proof.
      apply correctness2. intro d. split; intro H; rewrite <- H.
      - assert (&s*u*v*w!) as H' by eauto.
        assert (u!) as [a Hua] by eauto using subtermDenotes.
        assert (v!) as [b Hvb] by eauto using subtermDenotes.
        assert (w!) as [c Hwc] by eauto using subtermDenotes.
        rewrite Hua, Hvb, Hwc. symmetry. apply sSpec2.
      - assert (u*w*(v*w)!) as H' by eauto.
        assert (u!) as [a Hua] by eauto using subtermDenotes.
        assert (v!) as [b Hvb] by eauto using subtermDenotes.
        assert (w!) as [c Hwc] by eauto using subtermDenotes.
        rewrite Hua, Hvb, Hwc. apply sSpec2.
    Qed.

    Theorem saDenotes `{pca : Pca} (a : carrier) : &s*&a!.
    Proof. cut (&s*&a*&a!); eauto using subtermDenotes, sSpec1. Qed.

    Theorem identityCombinatorCorrect `{pca : Pca} (a : carrier) : ι*&a ≃ &a.
    Proof.
      unfold ι.
      rewrite sSpec2.
      destruct (kaDenotes a) as [ka Hka]. rewrite Hka at 2.
      apply kSpec.
    Qed.

    Theorem identityCombinatorCorrect' `{pca : Pca} (t : term 0) : ι*t ≃ t.
    Proof.
      apply correctness2. intro a. split; intro H.
      - assert (t!) as [b Htb] by eauto using subtermDenotes. rewrite Htb in *.
        rewrite identityCombinatorCorrect in H. exact H.
      -  rewrite H. apply identityCombinatorCorrect.
    Qed.

    Theorem identityCombinatorDenotes `{pca : Pca} : ι!.
    Proof. apply sSpec1. Qed.

    Theorem ksDistinctIffNonTrivial `{pca : Pca} : ~ k == s <-> NonTrivial pca.
    Proof.
      unfold NonTrivial. split; [eauto | ].
      intros [a [b Hab]] Hks. apply Hab, constInjective.
      assert (forall a : carrier, &a ≃ &k) as H. {
        clear a b Hab. intro a.
        setoid_rewrite <- identityCombinatorCorrect at 1.
        unfold identityCombinator.
        rewrite <- Hks, kSpec at 1.
        setoid_rewrite <- identityCombinatorCorrect at 1.
        unfold identityCombinator.
        rewrite <- Hks, kSpec, kSpec.
        reflexivity.
      }
      setoid_rewrite H. reflexivity.
    Qed.

    Lemma representationDefinition' `{pca : Pca} {n : nat} (t : term (S n)) :
      representation' (n := n) t =
      (fun (n : nat) => match n with
      | O   => fun t => match t with
               | &a    => &k*&a
               | var _ => ι
               | u*v   => &s * λ' u * λ' v
               end
      | S n => fun t => match t with
               | &a    => λ' (n := n) (&k*&a)
               | var x => match x with
                          | inl x => λ' (n := n) (&k * var x)
                          | inr _ => λ' (n := n) §ι
                          end
               | u*v   =>
                   let id := idVec 0 (n := S n) in
                   λ' (&s * §(λ' u) ** id * §(λ' v) ** id)
               end
      end) n t.
    Proof. destruct n; destruct t; auto. Qed.

    Opaque representation'.

    Theorem combinatoryCompleteness' `{pca : Pca} {n : nat} (t : term (S n))
                                     (f : VEC.t (term 0) (S n)) :
      (forall x : FIN.t (S n), VEC.nth f x !) -> λ' t ** f ≃ t / f.
    Proof.
      revert t f.
      induction n as [ | n IHn].
      - intros t [[] t'] Hf. destruct (Hf FIN.last) as [a Ha]. simpl in Ha.
        unfold product. simpl.
        induction t as [b | x | u IHu v IHv]; rewrite representationDefinition'.
        + simpl. rewrite Ha. apply kSpec.
        + rewrite identityCombinatorCorrect'.
          setoid_rewrite FIN.THMS.t1Singleton.
          reflexivity.
        + rewrite sSpec2', IHu, IHv. reflexivity.
      - intros t [f t'] Hf.
        destruct (Hf FIN.last) as [b Hb]. simpl in Hb.
        assert (λ' t ** (f;; t') = λ' t ** f * t') as H by reflexivity.
        rewrite H. clear H.
        assert (forall x, VEC.nth f x!) as H. { intro x. exact (Hf ++x). }
        induction t as [a' | x | u IHu v IHv];
        rewrite representationDefinition'.
        + rewrite IHn; [ | exact H]. simpl. rewrite Hb. apply kSpec.
        + destruct x as [x | x].
          * rewrite IHn; [ | exact H]. simpl. rewrite Hb. apply kSpec'.
          * rewrite IHn; [ | exact H]. apply identityCombinatorCorrect'.
        + rewrite IHn; [ | exact H].
          simpl.
          setoid_rewrite (idVecProductSubstitutionEq0' _ f).
          setoid_rewrite sSpec2'.
          rewrite IHu, IHv.
          reflexivity.
    Qed.

    Theorem combinatoryCompleteness1' `{pca : Pca} {n : nat} (t : term (S n))
                                      (f : VEC.t (term 0) n) :
      (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f !.
    Proof.
      simpl. intro H.
      induction n.
      - unfold product. simpl.
        induction t as [a | x | u IHu v IHv]; rewrite representationDefinition'.
        + apply kaDenotes.
        + apply identityCombinatorDenotes.
        + destruct IHu as [a IHu], IHv as [b IHv].
          rewrite IHu, IHv. apply sSpec1.
      - induction t as [a | x | u [u' IHu] v [v' IHv]];
        rewrite representationDefinition'.
        + rewrite (combinatoryCompleteness' _ _ H). simpl. apply kaDenotes.
        + destruct x as [x | x].
          * rewrite (combinatoryCompleteness' _ _ H).
            unfold substitution, pasVecToTermVec.
            destruct (H x) as [a Ha]. rewrite Ha. apply kaDenotes.
          * rewrite
              (combinatoryCompleteness' _ _ H), closedTermSubstitutionEq0.
            apply identityCombinatorDenotes.
        + rewrite (combinatoryCompleteness' _ _ H).
          assert
            ((&s * §(λ' u) ** idVec 0 * §(λ' v) ** idVec 0) / f =
             (&s / f) * ((§(λ' u) ** idVec 0) / f) * ((§(λ' v) ** idVec 0) / f))
          as H' by reflexivity.
          setoid_rewrite H'. clear H'.
          setoid_rewrite idVecProductSubstitutionEq0'.
          rewrite IHu, IHv. simpl.
          apply sSpec1.
    Qed.

    Theorem combinatoryCompleteness2' `{pca : Pca} {n : nat} (t : term n)
                                      (f : VEC.t (term 0) n) :
      (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f ≃ t / f.
    Proof.
      intro H.
      destruct n as [ | n].
      - destruct f. simpl.
        rewrite emptySubstitutionEq, closedTermToClosedTermEq.
        reflexivity.
      - apply combinatoryCompleteness'. exact H.
    Qed.

    Theorem combinatoryCompleteness1 `{pca : Pca} {n : nat} (t : term (S n))
                                     (f : VEC.t carrier n) :
      λ t ** &&f !.
    Proof.
      apply combinatoryCompleteness1'. intro x.
      unfold pasVecToTermVec. rewrite VEC.THMS.nthMapEq.
      exists (VEC.nth f x). reflexivity.
    Qed.

    Theorem combinatoryCompleteness2 `{pca : Pca} {n : nat} (t : term n)
                                     (f : VEC.t carrier n) :
      λ t ** &&f ≃ t/&&f.
    Proof.
      apply combinatoryCompleteness2'. intro x.
      unfold pasVecToTermVec. rewrite VEC.THMS.nthMapEq.
      exists (VEC.nth f x). reflexivity.
    Qed.

    Opaque representation.

    Theorem representationsDenote `{pca : Pca} {n : nat} (t : term (S n)) :
      λ t !.
    Proof.
      set (f := VEC.copies n k).
      apply (subtermDenotesProduct _ &&f).
      apply combinatoryCompleteness1.
    Qed.

    Theorem representationsDenote' `{pca : Pca} {n m : nat}
                                   (t : term (S (m + n)))
                                   (f : VEC.t carrier n) :
      λ t ** &&f!.
    Proof.
      set (g := VEC.copies m k).
      apply (subtermDenotesProduct _ &&g).
      rewrite doubleProductEq.
      unfold pasVecToTermVec. rewrite <- VEC.THMS.mapConcatEq.
      apply combinatoryCompleteness1.
    Qed.

    Theorem representationsDenote'' `{pca : Pca} {n m : nat} (t : term (S n))
                                    (f : VEC.t carrier m) :
      Compare_dec.leb m n = true -> λ t ** &&f!.
    Proof.
      rewrite Compare_dec.leb_iff.
      intro H. apply NPeano.Nat.le_exists_sub in H. destruct H as [k' [H _]].
      subst. apply representationsDenote'.
    Qed.

    Theorem combinatoryCompletenessInstance1 `{pca : Pca} (t : term 1)
                                             (a : carrier) :
      λ t * &a ≃ t / &&((();; a)).
    Proof.
      cutrewrite (λ t * &a = λ t ** &&(();; a)); [ | reflexivity].
      apply combinatoryCompleteness2.
    Qed.

    Theorem combinatoryCompletenessInstance2 `{pca : Pca} (t : term 2)
                                             (a b : carrier) :
      λ t * &a * &b ≃ t / &&((();; a;; b)).
    Proof.
      cutrewrite (λ t * &a*&b = λ t ** &&(();; a;; b)); [ | reflexivity].
      apply combinatoryCompleteness2.
    Qed.

    Theorem combinatoryCompletenessInstance3 `{pca : Pca} (t : term 3)
                                             (a b c : carrier) :
      λ t * &a * &b * &c ≃ t / &&((();; a;; b;; c)).
    Proof.
      cutrewrite (λ t * &a*&b*&c = λ t ** &&(();; a;; b;; c)); [ | reflexivity].
      apply combinatoryCompleteness2.
    Qed.

    Theorem combinatoryCompletenessInstance4 `{pca : Pca} (t : term 4)
                                             (a b c d : carrier) :
      λ t * &a * &b * &c * &d ≃ t / &&((();; a;; b;; c;; d)).
    Proof.
      cutrewrite (λ t * &a*&b*&c*&d = λ t ** &&(();; a;; b;; c;; d));
        [ | reflexivity].
      apply combinatoryCompleteness2.
    Qed.

    Theorem combinatoryCompletenessInstance5 `{pca : Pca} (t : term 5)
                                             (a b c d e: carrier) :
      λ t * &a * &b * &c * &d * &e ≃ t / &&((();; a;; b;; c;; d;; e)).
    Proof.
      cutrewrite (λ t * &a*&b*&c*&d*&e = λ t ** &&(();; a;; b;; c;; d;; e));
        [ | reflexivity].
      apply combinatoryCompleteness2.
    Qed.

    Theorem kAltCombinatorCorrect `{pca : Pca} (a b : carrier) : κ*&a*&b ≃ &b.
    Proof. unfold κ. rewrite kSpec'. apply identityCombinatorCorrect. Qed.

    Theorem kAltCombinatorCorrect' `{pca : Pca} (a : carrier) (t : term 0) :
      κ*&a*t ≃ t.
    Proof. unfold κ. rewrite kSpec'. apply identityCombinatorCorrect'. Qed.

    Theorem kAltCombinatorDenotes `{pca : Pca} : κ!.
    Proof.
      unfold κ. destruct identityCombinatorDenotes as [i Hi]. rewrite Hi.
      apply kaDenotes.
    Qed.

    Theorem kAltCombinatorDenotes' `{pca : Pca} (a : carrier) : κ*&a!.
    Proof.
      cut (κ*&a*&a!); eauto using subtermDenotes, kAltCombinatorCorrect.
    Qed.

    Theorem pairingCombinatorDenotes `{pca : Pca} : π!.
    Proof. apply representationsDenote. Qed.

    Theorem pairingCombinatorDenotes'' `{pca : Pca} (a b : carrier) : π*&a*&b!.
    Proof.
      cutrewrite (π*&a*&b = π**&&(((), a, b) : VEC.t carrier 2));
      [ | reflexivity].
      apply combinatoryCompleteness1.
    Qed.

    Theorem pairingCombinatorDenotes' `{pca : Pca} (a : carrier) : π*&a!.
    Proof.
      cut (π*&a*&a!); eauto using subtermDenotes, pairingCombinatorDenotes''.
    Qed.

    Theorem leftProjectionCombinatorCorrect `{pca : Pca} (a b : carrier) :
      π1*(π*&a*&b) ≃ &a.
    Proof.
      destruct (pairingCombinatorDenotes'' a b) as [p Hp]. rewrite Hp.
      unfold π1. rewrite combinatoryCompletenessInstance1. simpl.
      rewrite <- Hp. unfold π. setoid_rewrite combinatoryCompletenessInstance3.
      apply kSpec.
    Qed.

    Theorem leftProjectionCombinatorCorrect' `{pca : Pca} (t : term 0)
                                             (b : carrier) :
      π1*(π*t*&b) ≃ t.
    Proof.
      apply correctness2. intro a. split; intro H.
      - assert (t!) as [a' Ht] by eauto 7 using subtermDenotes. rewrite Ht in *.
        rewrite leftProjectionCombinatorCorrect in H. exact H.
      - rewrite H. apply leftProjectionCombinatorCorrect.
    Qed.

    Theorem leftProjectionCombinatorDenotes `{pca : Pca} : π1!.
    Proof.
      cut (π1*(π*&k*&k)!);
      eauto using subtermDenotes, leftProjectionCombinatorCorrect.
    Qed.

    Theorem rightProjectionCombinatorCorrect `{pca : Pca} (a b : carrier) :
      π2*(π*&a*&b) ≃ &b.
    Proof.
      destruct (pairingCombinatorDenotes'' a b) as [p Hp]. rewrite Hp.
      unfold π2. rewrite combinatoryCompletenessInstance1. simpl.
      destruct (kAltCombinatorDenotes) as [k' Hk'].
      rewrite Hk', <- Hp. unfold π. rewrite combinatoryCompletenessInstance3.
      simpl. rewrite <- Hk'. apply kAltCombinatorCorrect.
    Qed.

    Theorem rightProjectionCombinatorCorrect' `{pca : Pca} (a : carrier)
                                              (t : term 0) :
      π2*(π*&a*t) ≃ t.
    Proof.
      apply correctness2. intro b. split; intro H.
      - assert (t!) as [b' Ht] by eauto 6 using subtermDenotes. rewrite Ht in *.
        rewrite rightProjectionCombinatorCorrect in H. exact H.
      - rewrite H. apply rightProjectionCombinatorCorrect.
    Qed.

    Theorem rightProjectionCombinatorDenotes `{pca : Pca} : π2!.
    Proof.
      assert (π2*(π*&k*&k)!) by eauto using rightProjectionCombinatorCorrect.
      eauto using subtermDenotes, rightProjectionCombinatorCorrect.
    Qed.

    Theorem natRepresentationCombinatorDenotes `{pca : Pca} (n : nat) : #n!.
    Proof.
      induction n as [ | n [a IHn]].
      - apply identityCombinatorDenotes.
      - unfold natRepresentationCombinator. rewrite IHn.
        destruct kAltCombinatorDenotes as [k' Hk']. rewrite Hk'.
        apply pairingCombinatorDenotes''.
    Qed.

    Theorem caseCombinatorCorrect0 `{pca : Pca} (a b : carrier) :
      δ*&a*&b*#0 ≃ &a.
    Proof.
      simpl. destruct identityCombinatorDenotes as [i Hi]. rewrite Hi.
      setoid_rewrite combinatoryCompletenessInstance3. simpl.
      setoid_rewrite closedTermSubstitutionEq0.
      setoid_rewrite combinatoryCompletenessInstance1. simpl.
      rewrite <- Hi, identityCombinatorCorrect'.
      apply kSpec.
    Qed.

    Theorem caseCombinatorCorrect0' `{pca : Pca} (t : term 0) (b : carrier) :
      δ*t*&b*#0 ≃ t.
    Proof.
      apply correctness2. intro a. split; intro H.
      - assert (t!) as [a' Ht] by eauto 7 using subtermDenotes. rewrite Ht in *.
        rewrite caseCombinatorCorrect0 in H. exact H.
      - rewrite H. apply caseCombinatorCorrect0.
    Qed.

    Theorem caseCombinatorCorrectS `{pca : Pca} (n : nat) (a b : carrier) :
      δ*&a*&b*#(S n) ≃ &b.
    Proof.
      destruct
        (natRepresentationCombinatorDenotes n) as [n' Hn],
        (natRepresentationCombinatorDenotes (S n)) as [Sn HSn].
      unfold δ. rewrite HSn, combinatoryCompletenessInstance3. simpl.
      setoid_rewrite closedTermSubstitutionEq0.
      rewrite <- HSn. simpl. rewrite Hn, leftProjectionCombinatorCorrect'.
      apply kAltCombinatorCorrect.
    Qed.

    Theorem caseCombinatorCorrectS' `{pca : Pca} (a : carrier) (t : term 0)
                                    (x : nat) :
      δ*&a*t*#(S x) ≃ t.
    Proof.
      apply correctness2. intro b. split; intro H.
      - assert (t!) as [b' Ht] by eauto 7 using subtermDenotes. rewrite Ht in *.
        rewrite caseCombinatorCorrectS in H. exact H.
      - rewrite H. apply caseCombinatorCorrectS.
    Qed.

    Theorem caseCombinatorDenotes'' `{pca : Pca} (a b : carrier) : δ*&a*&b!.
    Proof.
      assert (δ*&a*&b*#0!) by eauto using caseCombinatorCorrect0.
      destruct (natRepresentationCombinatorDenotes 0) as [x Hx].
      rewrite Hx in H. eauto using subtermDenotes.
    Qed.

    Theorem caseCombinatorDenotes' `{pca : Pca} (a : carrier) : δ*&a!.
    Proof.
      pose proof (caseCombinatorDenotes'' a a). eauto using subtermDenotes.
    Qed.

    Theorem caseCombinatorDenotes `{pca : Pca} : δ!.
    Proof.
      pose proof (caseCombinatorDenotes' k). eauto using subtermDenotes.
    Qed.

    Theorem successorCombinatorCorrect `{pca : Pca} (n : nat) : σ*#n ≃ #(S n).
    Proof. reflexivity. Qed.

    Theorem successorCombinatorDenotes' `{pca : Pca} (n : nat) : σ*#n!.
    Proof.
      rewrite successorCombinatorCorrect.
      apply natRepresentationCombinatorDenotes.
    Qed.

    Theorem successorCombinatorDenotes `{pca : Pca} : σ!.
    Proof.
      pose proof (successorCombinatorDenotes' 0). eauto using subtermDenotes.
    Qed.

    Theorem predecessorCombinatorCorrect0 `{pca : Pca} : ψ*#0 ≃ #0.
    Proof.
      unfold natRepresentationCombinator.
      destruct
        identityCombinatorDenotes as [i Hi],
        rightProjectionCombinatorDenotes as [p2 Hp2].
      rewrite Hi.
      unfold ψ. rewrite combinatoryCompletenessInstance1. simpl.
      setoid_rewrite closedTermSubstitutionEq0.
      assert (π1*&i ≃ &k) as H. {
        unfold π1. rewrite combinatoryCompletenessInstance1. simpl.
        rewrite <- Hi. apply identityCombinatorCorrect.
      }
      rewrite H, Hp2, Hi, kSpec, <- Hi.
      apply identityCombinatorCorrect'.
    Qed.

    Theorem predecessorCombinatorCorrectS `{pca : Pca} (n : nat) :
      ψ*#(S n) ≃ #n.
    Proof.
      destruct
        (natRepresentationCombinatorDenotes n) as [n' Hn],
        (natRepresentationCombinatorDenotes (S n)) as [Sn HSn].
      rewrite Hn, HSn.
      unfold ψ. rewrite combinatoryCompletenessInstance1. simpl.
      rewrite closedTermSubstitutionEq0, closedTermSubstitutionEq0.
      rewrite <- HSn. simpl. rewrite Hn at 1.
      rewrite leftProjectionCombinatorCorrect'.
      destruct
        identityCombinatorDenotes as [i Hi],
        kAltCombinatorDenotes as [k' Hk'].
      rewrite
        Hi, kAltCombinatorCorrect', Hk', rightProjectionCombinatorCorrect', Hn.
      reflexivity.
    Qed.

    Theorem predecessorCombinatorCorrect `{pca : Pca} (n : nat) : ψ*#n ≃ #(n-1).
    Proof.
      destruct n as [ | n].
      - rewrite predecessorCombinatorCorrect0. reflexivity.
      - rewrite predecessorCombinatorCorrectS. simpl.
        rewrite <- Minus.minus_n_O.
        reflexivity.
    Qed.

    Theorem predecessorCombinatorDenotes `{pca : Pca} : ψ!.
    Proof. apply representationsDenote. Qed.

    Theorem fixedPointCombinatorCorrect `{pca : Pca} (a : carrier) :
      φ1*&a ≃ &a*(φ1*&a).
    Proof.
      unfold φ1 at 1. simpl.
      set (u := x12*(x02*x02*x12)). unfold u at 1.
      destruct (representationsDenote u) as [u' Hu].
      rewrite Hu, combinatoryCompletenessInstance2. simpl. rewrite <- Hu.
      reflexivity.
    Qed.

    Theorem fixedPointCombinatorCorrect' `{pca : Pca} (t : term 0) :
      φ1*t ≃ t*(φ1*t).
    Proof.
      apply correctness2. intro a. split; intro H.
      - assert (t!) as [b Ht] by eauto using subtermDenotes.
        rewrite Ht, <- H in *. symmetry.
        apply fixedPointCombinatorCorrect.
      - assert (t!) as [b Ht] by eauto using subtermDenotes.
        rewrite Ht, <- H in *.
        apply fixedPointCombinatorCorrect.
    Qed.

    Theorem doubleFixedPointCombinatorDenotes `{pca : Pca} : φ2!.
    Proof.
      unfold φ2.
      set (u := x13*(x03*x03*x13)*x23). unfold u at 1.
      destruct (representationsDenote u) as [u' Hu]. rewrite Hu. clear Hu.
      fold u. cutrewrite (λ u * &u' = λ u ** &&(();; u')); [ | reflexivity].
      apply representationsDenote''. reflexivity.
    Qed.

    Theorem doubleFixedPointCombinatorDenotes' `{pca : Pca} (a : carrier) :
      φ2*&a!.
    Proof.
      unfold φ2.
      set (u := x13*(x03*x03*x13)*x23). unfold u at 1.
      destruct (representationsDenote u) as [u' Hu].
      rewrite Hu. fold u.
      cutrewrite (λ u * &u' * &a = λ u ** &&(();; u';; a)); [ | reflexivity].
      apply combinatoryCompleteness1.
    Qed.

    Theorem doubleFixedPointCombinatorCorrect `{pca : Pca} (a b : carrier) :
      φ2*&a*&b ≃ &a*(φ2*&a)*&b.
    Proof.
      unfold φ2 at 1. simpl.
      set (u := x13*(x03*x03*x13)*x23). unfold u at 1.
      destruct (representationsDenote u) as [u' Hu].
      rewrite Hu, combinatoryCompletenessInstance3. simpl. rewrite <- Hu.
      reflexivity.
    Qed.

    Lemma primitiveRecursionCombinatorEq `{pca : Pca} (a b : carrier)
                                         (x : nat) :
      ρ*&a*&b*#x ≃ δ*(&k*&a)*(r'*(φ2*r)*&a*&b*#x)*#x*&k.
    Proof.
      destruct (natRepresentationCombinatorDenotes x) as [x' Hx]. rewrite Hx.
      unfold ρ. rewrite combinatoryCompletenessInstance3. simpl.
      setoid_rewrite closedTermSubstitutionEq0.
      assert (r!) as Hr by eauto using representationsDenote.
      destruct Hr as [r'' Hr]. rewrite Hr.
      setoid_rewrite doubleFixedPointCombinatorCorrect.
      destruct (doubleFixedPointCombinatorDenotes' r'') as [φr Hφr].
      setoid_rewrite Hφr.
      setoid_rewrite <- Hr.
      setoid_rewrite combinatoryCompletenessInstance4. simpl.
      rewrite closedTermSubstitutionEq0.
      rewrite closedTermSubstitutionEq0.
      rewrite <- Hφr, <- Hr.
      reflexivity.
    Qed.

    Lemma rDenotes' `{pca : Pca} (a b : carrier) (x : nat) :
      r'*(φ2*r)*&a*&b*#x!.
    Proof.
      assert (r!) as [c Hc] by eauto using representationsDenote.
      destruct
        (doubleFixedPointCombinatorDenotes' c) as [d Hd],
        (natRepresentationCombinatorDenotes x) as [e He].
      rewrite Hc, Hd, He.
      cutrewrite (r' * &d * &a * &b * &e = r' ** &&(();; d;; a;; b;; e));
        [ | reflexivity].
      apply combinatoryCompleteness1.
    Qed.

    Theorem primitiveRecursionCombinatorCorrect0 `{pca : Pca} (a b : carrier) :
      ρ*&a*&b*#0 ≃ &a.
    Proof.
      rewrite primitiveRecursionCombinatorEq.
      destruct (rDenotes' a b 0) as [r'' Hr].
      rewrite Hr, caseCombinatorCorrect0', kSpec.
      reflexivity.
    Qed.

    Theorem primitiveRecursionCombinatorCorrectS `{pca : Pca} (a b : carrier)
                                                 (x : nat) :
      ρ*&a*&b*#(S x) ≃ &b*#x*(ρ*&a*&b*#x).
    Proof.
      rewrite primitiveRecursionCombinatorEq.
      destruct (rDenotes' a b (S x)) as [r'' Hr''].
      destruct (kaDenotes a) as [ka Hka].
      rewrite Hr'', Hka, caseCombinatorCorrectS', <- Hr''.
      assert (r!) as [r''' Hr'''] by eauto using representationsDenote.
      destruct
        (natRepresentationCombinatorDenotes x) as [x' Hx],
        (natRepresentationCombinatorDenotes (S x)) as [Sx HSx],
        (doubleFixedPointCombinatorDenotes' r''') as [φr Hφr].
      unfold r, r' in *.
      rewrite Hx, HSx, Hr''', Hφr, combinatoryCompletenessInstance5. simpl.
      setoid_rewrite closedTermSubstitutionEq0.
      rewrite <- HSx, predecessorCombinatorCorrect, <- Hφr, <- Hr'''. simpl.
      rewrite <- Minus.minus_n_O.
      unfold ρ. rewrite combinatoryCompletenessInstance3. simpl.
      rewrite closedTermSubstitutionEq0.
      rewrite closedTermSubstitutionEq0.
      rewrite <- Hx.
      reflexivity.
    Qed.

    Theorem primitiveRecursionCombinatorDenotes `{pca : Pca} : ρ!.
    Proof. apply representationsDenote. Qed.

    Theorem primitiveRecursionCombinatorDenotes'' `{pca : Pca} (a b : carrier) :
      ρ*&a*&b!.
    Proof.
      cutrewrite (ρ*&a*&b = ρ ** &&(();; a;; b)); [ | reflexivity].
      apply combinatoryCompleteness1.
    Qed.

    Theorem primitiveRecursionCombinatorDenotes' `{pca : Pca} (a : carrier) :
      ρ*&a!.
    Proof.
      pose proof (primitiveRecursionCombinatorDenotes'' a a) as H.
      eauto using subtermDenotes.
    Qed.

    Theorem additionCombinatorCorrect `{pca : Pca} (x y : nat) :
      α*#x*#y ≃ #(x + y).
    Proof.
      unfold α.
      destruct
        (natRepresentationCombinatorDenotes x) as [x' Hx],
        (natRepresentationCombinatorDenotes y) as [y' Hy],
        successorCombinatorDenotes as [S HS].
      destruct (kaDenotes S) as [kS HkS].
      rewrite Hx, Hy, combinatoryCompletenessInstance2. simpl.
      rewrite closedTermSubstitutionEq0.
      rewrite closedTermSubstitutionEq0.
      rewrite <- Hx, HS, HkS. clear x' Hx.
      induction x as [ | x IHx].
      - setoid_rewrite primitiveRecursionCombinatorCorrect0. rewrite <- Hy.
        reflexivity.
      - setoid_rewrite primitiveRecursionCombinatorCorrectS.
        destruct (natRepresentationCombinatorDenotes x) as [x' Hx].
        rewrite IHx, Hx, <- HkS, <- HS, kSpec', successorCombinatorCorrect.
        reflexivity.
    Qed.

    Theorem additionCombinatorDenotes' `{pca : Pca} (x : nat) : α*#x!.
    Proof.
      assert (α*#x*#x!) as H. {
        destruct (natRepresentationCombinatorDenotes (x + x)) as [xx Hxx].
        exists xx. rewrite additionCombinatorCorrect, <- Hxx. reflexivity.
      }
      eauto using subtermDenotes.
    Qed.

    Theorem additionCombinatorDenotes `{pca : Pca} : α!.
    Proof.
      pose proof (additionCombinatorDenotes' 0) as H.
      eauto using subtermDenotes.
    Qed.

    Theorem multiplicationCombinatorCorrect `{pca : Pca} (x y : nat) :
      μ*#x*#y ≃ #(x * y).
    Proof.
      unfold μ.
      destruct
        (natRepresentationCombinatorDenotes x) as [x' Hx],
        (natRepresentationCombinatorDenotes y) as [y' Hy],
        (additionCombinatorDenotes' y) as [αy Hαy].
      rewrite Hx, Hy, combinatoryCompletenessInstance2. simpl.
      rewrite closedTermSubstitutionEq0.
      rewrite closedTermSubstitutionEq0.
      destruct
        (kaDenotes αy) as [kαy Hkαy], identityCombinatorDenotes as [i Hi].
      rewrite <- Hx, <- Hy, Hαy, Hkαy, Hi. clear x' Hx.
      induction x as [ | x IHx].
      - rewrite primitiveRecursionCombinatorCorrect0, Hi. reflexivity.
      - rewrite primitiveRecursionCombinatorCorrectS.
        destruct (natRepresentationCombinatorDenotes x) as [x' Hx].
        rewrite IHx, Hx, <- Hkαy, <- Hαy, kSpec', additionCombinatorCorrect.
        reflexivity.
    Qed.

    Theorem multiplicationCombinatorDenotes' `{pca : Pca} (x : nat) : μ*#x!.
    Proof.
      assert (μ*#x*#x!) as H. {
        destruct (natRepresentationCombinatorDenotes (x * x)) as [xx Hxx].
        exists xx. rewrite multiplicationCombinatorCorrect, <- Hxx. reflexivity.
      }
      eauto using subtermDenotes.
    Qed.

    Theorem multiplicationCombinatorDenotes `{pca : Pca} : μ!.
    Proof.
      pose proof (multiplicationCombinatorDenotes' 0) as H.
      eauto using subtermDenotes.
    Qed.

    Theorem correctArithmetic `{pca : Pca} (x y : nat) :
      NonTrivial pca -> #x ≃ #y -> x = y.
    Proof.
      rewrite <- ksDistinctIffNonTrivial. intro ksDistinct.
      assert (forall x, ~ #(S x) ≃ #0) as H. {
        clear x y. simpl. intros x H. apply ksDistinct.
        destruct (natRepresentationCombinatorDenotes x) as [x' Hx'].
        rewrite Hx' in H.
        pose proof (leftProjectionCombinatorCorrect' κ x') as H'.
        rewrite H in H'.
        unfold π1 in H'.
        destruct identityCombinatorDenotes as [i Hi]. rewrite Hi in H'.
        rewrite combinatoryCompletenessInstance1 in H'. simpl in H'.
        rewrite <- Hi, identityCombinatorCorrect in H'.
        apply constInjective.
        pose proof (kSpec k s) as H''.
        rewrite H' in H'' at 1.
        rewrite kAltCombinatorCorrect in H''.
        symmetry in H''.
        exact H''.
      }
      clear ksDistinct.
      revert y. induction x as [ | x IHx].
      - intro y. destruct y as [ | y]; [tauto | ].
        intro H'. symmetry in H'. apply H in H'. contradiction.
      - destruct y as [ | y].
        + intro H'. apply H in H'. contradiction.
        + simpl. intro H'.
          destruct kAltCombinatorDenotes as [k' Hk']. rewrite Hk' in *.
          pose proof (rightProjectionCombinatorCorrect' k' #x) as Hx.
          pose proof (rightProjectionCombinatorCorrect' k' #y) as Hy.
          rewrite <- H', Hx in Hy. rewrite (IHx _ Hy). reflexivity.
    Qed.

  End THMS.

  (**
  Hide implementations.
  *)

  Global Opaque representation.
  Global Opaque ι λ κ π π1 π2 δ σ ψ φ1 φ2 ρ α μ natRepresentationCombinator.

End PCA.
