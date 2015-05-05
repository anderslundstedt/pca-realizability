Require Coq.Arith.Minus.
Require Coq.Numbers.Natural.Peano.NPeano.

Require Import myvec.
Require Import pas.

Import FIN.NOTATIONS.
Import PAS.
Import PAS.NOTATIONS.
Import PAS_COERCIONS.
Import VEC.NOTATIONS.

Local Open Scope FIN.
Local Open Scope VEC.
Local Open Scope PAS.

Module PCA.

  Class Pca := {
    pas :> Pas;
    k : pas;
    s : pas;
    ksDistinct : ~ k == s;
    kSpec (a b : pas) : &k*&a*&b ≃ &a;
    sSpec1 (a b : pas) : &s*&a*&b!;
    sSpec2 (a b c: pas) : &s*&a*&b*&c ≃ &a*&c*(&b*&c)
  }.
  Local Coercion pas : Pca >-> Pas.

  Lemma kSpec' {pca : Pca} (t : term 0) (b : pca) : &k*t*&b ≃ t.
  Proof.
    apply correctness2. intro a. split; intro H.
    - assert (&k*t*&b!) as H' by eauto.
      assert (t!) as [a' Ht] by eauto using subTermDenotes.
      rewrite <- H, Ht. symmetry. apply kSpec.
    - rewrite H. apply kSpec.
  Qed.

  Lemma kaDenotes {pca : Pca} (a : pca) : &k*&a!.
  Proof. cut (&k*&a*&a!); eauto using subTermDenotes, kSpec. Qed.

  Lemma sSpec2' {pca : Pca} (u v w : term 0) : &s*u*v*w ≃ u*w*(v*w).
  Proof.
    apply correctness2. intro d. split; intro H; rewrite <- H.
    - assert (&s*u*v*w!) as H' by eauto.
      assert (u!) as [a Hua] by eauto using subTermDenotes.
      assert (v!) as [b Hvb] by eauto using subTermDenotes.
      assert (w!) as [c Hwc] by eauto using subTermDenotes.
      rewrite Hua, Hvb, Hwc. symmetry. apply sSpec2.
    - assert (u*w*(v*w)!) as H' by eauto.
      assert (u!) as [a Hua] by eauto using subTermDenotes.
      assert (v!) as [b Hvb] by eauto using subTermDenotes.
      assert (w!) as [c Hwc] by eauto using subTermDenotes.
      rewrite Hua, Hvb, Hwc. apply sSpec2.
  Qed.

  Lemma saDenotes {pca : Pca} (a : pca) : &s*&a!.
  Proof. cut (&s*&a*&a!); eauto using subTermDenotes, sSpec1. Qed.

  Definition identityCombinator {_ : Pca} : term 0 := &s*&k*&k.
  Local Notation ι := identityCombinator.

  Definition representation' {pca : Pca} {n : nat} (t : term (S n)) : term 0.
  Proof.
    induction n as [ | n IHn].
    - induction t as [a | x | u IHu v IHv].
      + exact (&k*&a).
      + exact ι.
      + exact (&s*IHu*IHv).
    - induction t as [a | x |u IHu v IHv].
      + exact (IHn (&k*&a)).
      + destruct x as [x | x].
        * exact (IHn (&k * termVar x)).
        * exact (IHn $ ι).
      + set (i := idVec 0 (n := S n)).
        set (u' := $ IHu ** i).
        set (v' := $ IHv ** i).
        exact (IHn (&s*u'*v')).
  Defined.
  Local Notation λ' := representation'.

  Lemma representationDefinition' {pca : Pca} {n : nat} (t : term (S n)) :
    @representation' pca n t =
    (fun (n : nat) => match n with
    | O   => fun t => match t with
             | &a        => &k*&a
             | termVar _ => ι
             | u*v       => &s * λ' u * λ' v
             end
    | S n => fun t => match t with
             | &a        => λ' (n := n) (&k*&a)
             | termVar x => match x with
                            | inl x => λ' (n := n) (&k * termVar x)
                            | inr _ => λ' (n := n) $ ι
                            end
             | u*v       =>
                 let id := idVec 0 (n := S n) in
                 λ' (&s * $ (λ' u) ** id * $ (λ' v) ** id)
             end
    end) n t.
  Proof. destruct n; destruct t; auto. Qed.

  Global Opaque representation'.

  Definition representation {_ : Pca} {n : nat} : term n -> term 0 :=
  match n with
  | O   => fun t => t
  | S n => fun t => λ' t
  end.
  Local Notation λ := representation.

  Definition kAltCombinator {_ : Pca} : term 0 := &k*ι.
  Local Notation κ := kAltCombinator.

  Definition pairingCombinator {_ : Pca} : term 0 := λ (x33*x13*x23).
  Local Notation π := pairingCombinator.

  Definition leftProjectionCombinator {_ : Pca} : term 0 := λ (x11*&k).
  Local Notation π1 := leftProjectionCombinator.

  Definition rightProjectionCombinator {_ : Pca} : term 0 := λ (x11 * $ κ).
  Local Notation π2 := rightProjectionCombinator.

  Fixpoint natRepresentationCombinator `{_ : Pca} (n : nat) : term 0 :=
  match n with
  | O   => ι
  | S n => π * κ * (natRepresentationCombinator n)
  end.
  Local Notation "# n" := (natRepresentationCombinator n) (at level 5).

  Definition caseCombinator {_ : Pca} : term 0 := λ ($ π1 * x33 * x13 * x23).
  Local Notation δ := caseCombinator.

  Definition successorCombinator {_ : Pca} : term 0 := π * κ.
  Local Notation σ := successorCombinator.

  Definition predecessorCombinator {_ : Pca} : term 0 :=
    λ ($ π1 * x11 * $ #0 * $ π2 * x11).
  Local Notation ψ := predecessorCombinator.

  Definition fixedPointCombinator {_ : Pca} : term 0 :=
    let u := λ (x22*(x12*x12*x22)) in u*u.
  Local Notation φ1 := fixedPointCombinator.

  Definition doubleFixedPointCombinator {_ : Pca} : term 0 :=
    let u := λ (x23*(x13*x13*x23)*x33) in u*u.
  Local Notation φ2 := doubleFixedPointCombinator.

  Local Notation r' :=
    (λ (x35 * ($ ψ * x45) * (x15 * x25 * x35 * ($ ψ * x45) * &k))).
  Local Notation r :=
    (λ ($ δ * (&k * x24) * ($ r' * x14 * x24 * x34 * x44) * x44)).
  Definition primitiveRecursionCombinator {_ : Pca} : term 0 :=
    λ ($ φ2 * $ r * x13 * x23 * x33 * &k).
  Local Notation ρ := primitiveRecursionCombinator.

  Definition additionCombinator {_ : Pca} : term 0 :=
    λ ($ ρ * x22 * (&k * $ σ) * x12).
  Local Notation α := additionCombinator.

  Definition multiplicationCombinator {_ : Pca} : term 0 :=
    λ ($ ρ * $ #0 * (&k * ($ α * x22)) * x12).
  Local Notation μ := multiplicationCombinator.

  Lemma identityCombinatorCorrect {pca : Pca} (a : pca) : ι*&a ≃ &a.
  Proof.
    unfold ι.
    rewrite sSpec2.
    destruct (kaDenotes a) as [ka Hka]. rewrite Hka at 2.
    apply kSpec.
  Qed.

  Lemma identityCombinatorCorrect' {pca : Pca} (t : term 0) : ι*t ≃ t.
  Proof.
    apply correctness2. intro a. split; intro H.
    - assert (t!) as [b Htb] by eauto using subTermDenotes. rewrite Htb in *.
      rewrite identityCombinatorCorrect in H. exact H.
    -  rewrite H. apply identityCombinatorCorrect.
  Qed.

  Lemma identityCombinatorDenotes {pca : Pca} : ι!.
  Proof. apply sSpec1. Qed.

  Theorem combinatoryCompleteness' {pca : Pca} {n : nat} (t : term (S n))
                                   (f : VEC.t (term 0) (S n)) :
    (forall x : FIN.t (S n), VEC.nth f x !) -> λ' t ** f ≃ t / f.
  Proof.
    revert t f.
    induction n as [ | n IHn].
    - intros t [[] t'] Hf. destruct (Hf FIN.last) as [a Ha]. simpl in Ha.
      unfold product. simpl.
      induction t as [b | x | u IHu v IHv]; rewrite representationDefinition'.
      + simpl. rewrite Ha. apply kSpec.
      + rewrite identityCombinatorCorrect'. setoid_rewrite FIN.t1Singleton.
        reflexivity.
      + rewrite sSpec2', IHu, IHv. reflexivity.
    - intros t [f t'] Hf.
      destruct (Hf FIN.last) as [b Hb]. simpl in Hb.
      assert (λ' t ** (f;; t') = λ' t ** f * t') as H by reflexivity.
      rewrite H. clear H.
      assert (forall x, VEC.nth f x!) as H. { intro x. exact (Hf ++x). }
      induction t as [a' | x | u IHu v IHv]; rewrite representationDefinition'.
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

  Theorem combinatoryCompleteness1' {pca : Pca} {n : nat} (t : term (S n))
                                    (f : VEC.t (term 0) n) :
    (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f !.
  Proof.
    simpl. intro H.
    induction n.
    - unfold product. simpl.
      induction t as [a | x | u IHu v IHv]; rewrite representationDefinition'.
      + apply kaDenotes.
      + apply identityCombinatorDenotes.
      + destruct IHu as [a IHu], IHv as [b IHv]. rewrite IHu, IHv. apply sSpec1.
    - induction t as [a | x | u [u' IHu] v [v' IHv]];
      rewrite representationDefinition'.
      + rewrite (combinatoryCompleteness' _ _ H). simpl. apply kaDenotes.
      + destruct x as [x | x].
        * rewrite (combinatoryCompleteness' _ _ H).
          unfold substitution, pasVecToTermVec.
          destruct (H x) as [a Ha]. rewrite Ha. apply kaDenotes.
        * rewrite
            (combinatoryCompleteness' _ _ H), closedTermSubstitutionLemma0.
          apply identityCombinatorDenotes.
      + rewrite (combinatoryCompleteness' _ _ H).
        assert
          ((&s * $ (λ' u) ** idVec 0 * $ (λ' v) ** idVec 0) / f =
           (&s / f) * (($ (λ' u) ** idVec 0) / f) * (($ (λ' v) ** idVec 0) / f))
        as H' by reflexivity.
        setoid_rewrite H'. clear H'.
        setoid_rewrite idVecProductSubstitutionEq0'.
        rewrite IHu, IHv. simpl.
        apply sSpec1.
  Qed.

  Theorem combinatoryCompleteness2' {pca : Pca} {n : nat} (t : term n)
                                    (f : VEC.t (term 0) n) :
    (forall x : FIN.t n, VEC.nth f x !) -> λ t ** f ≃ t / f.
  Proof.
    intro H.
    destruct n as [ | n].
    - destruct f. simpl. rewrite emptySubstitutionLemma, closedTermToTermLemma.
      reflexivity.
    - apply combinatoryCompleteness'. exact H.
  Qed.

  Theorem combinatoryCompleteness1 {pca : Pca} {n : nat} (t : term (S n))
                                   (f : VEC.t pca n) :
    λ t ** &&f !.
  Proof.
    apply combinatoryCompleteness1'. intro x.
    unfold pasVecToTermVec. rewrite VEC.mapNth.
    exists (VEC.nth f x). reflexivity.
  Qed.

  Theorem combinatoryCompleteness2 {pca : Pca} {n : nat} (t : term n)
                                   (f : VEC.t pca n) :
    λ t ** &&f ≃ t/&&f.
  Proof.
    apply combinatoryCompleteness2'. intro x.
    unfold pasVecToTermVec. rewrite VEC.mapNth.
    exists (VEC.nth f x). reflexivity.
  Qed.

  Global Opaque representation.

  Lemma representationsDenote {pca : Pca} {n : nat} (t : term (S n)) : λ t !.
  Proof.
    set (f := VEC.copies n k).
    apply (subTermDenotesProduct _ &&f).
    apply combinatoryCompleteness1.
  Qed.

  Lemma representationsDenote' {pca : Pca} {n m : nat} (t : term (S (m + n)))
                               (f : VEC.t pca n) :
    λ t ** &&f!.
  Proof.
    set (g := VEC.copies m k).
    apply (subTermDenotesProduct _ &&g).
    rewrite productApplicationEq.
    unfold pasVecToTermVec. rewrite <- VEC.concatMap.
    apply combinatoryCompleteness1.
  Qed.

  Lemma representationsDenote'' {pca : Pca} {n m : nat} (t : term (S n))
                                (f : VEC.t pca m) :
    Compare_dec.leb m n = true -> λ t ** &&f!.
  Proof.
    rewrite Compare_dec.leb_iff.
    intro H. apply NPeano.Nat.le_exists_sub in H. destruct H as [k [H _]].
    subst. apply representationsDenote'.
  Qed.

  Lemma combinatoryCompletenessInstance1 {pca : Pca} (t : term 1) (a : pca) :
    λ t * &a ≃ t / &&((tt, a) : VEC.t pca 1).
  Proof.
    cutrewrite (λ t * &a = λ t ** &&(();; a)); [ | reflexivity].
    apply combinatoryCompleteness2.
  Qed.

  Lemma combinatoryCompletenessInstance2 {pca : Pca} (t : term 2) (a b : pca) :
    λ t * &a * &b ≃ t / &&((tt, a, b) : VEC.t pca 2).
  Proof.
    cutrewrite (λ t * &a*&b = λ t ** &&(();; a;; b)); [ | reflexivity].
    apply combinatoryCompleteness2.
  Qed.

  Lemma combinatoryCompletenessInstance3 {pca : Pca} (t : term 3)
                                         (a b c : pca) :
    λ t * &a * &b * &c ≃ t / &&((tt, a, b, c) : VEC.t pca 3).
  Proof.
    cutrewrite (λ t * &a*&b*&c = λ t ** &&(();; a;; b;; c)); [ | reflexivity].
    apply combinatoryCompleteness2.
  Qed.

  Lemma combinatoryCompletenessInstance4 {pca : Pca} (t : term 4)
                                         (a b c d : pca) :
    λ t * &a * &b * &c * &d ≃ t / &&((tt, a, b, c, d) : VEC.t pca 4).
  Proof.
    cutrewrite (λ t * &a*&b*&c*&d = λ t ** &&(();; a;; b;; c;; d));
      [ | reflexivity].
    apply combinatoryCompleteness2.
  Qed.

  Lemma combinatoryCompletenessInstance5 {pca : Pca} (t : term 5)
                                         (a b c d e: pca) :
    λ t * &a * &b * &c * &d * &e ≃ t / &&((tt, a, b, c, d, e) : VEC.t pca 5).
  Proof.
    cutrewrite (λ t * &a*&b*&c*&d*&e = λ t ** &&(();; a;; b;; c;; d;; e));
      [ | reflexivity].
    apply combinatoryCompleteness2.
  Qed.

  Lemma kAltCombinatorCorrect {pca : Pca} (a b : pca) : κ*&a*&b ≃ &b.
  Proof. unfold κ. rewrite kSpec'. apply identityCombinatorCorrect. Qed.

  Lemma kAltCombinatorCorrect' {pca : Pca} (a : pca) (t : term 0) : κ*&a*t ≃ t.
  Proof. unfold κ. rewrite kSpec'. apply identityCombinatorCorrect'. Qed.

  Lemma kAltCombinatorDenotes {pca : Pca} : κ!.
  Proof.
    unfold κ. destruct identityCombinatorDenotes as [i Hi]. rewrite Hi.
    apply kaDenotes.
  Qed.

  Lemma kAltCombinatorDenotes' {pca : Pca} (a : pca) : κ*&a!.
  Proof. cut (κ*&a*&a!); eauto using subTermDenotes, kAltCombinatorCorrect. Qed.

  Lemma pairingCombinatorDenotes {pca : Pca} : π!.
  Proof. apply representationsDenote. Qed.

  Lemma pairingCombinatorDenotes'' {pca : Pca} (a b : pca) : π*&a*&b!.
  Proof.
    cutrewrite (π*&a*&b = π**&&((tt, a, b) : VEC.t pca 2)); [ | reflexivity].
    apply combinatoryCompleteness1.
  Qed.

  Lemma pairingCombinatorDenotes' {pca : Pca} (a : pca) : π*&a!.
  Proof.
    cut (π*&a*&a!); eauto using subTermDenotes, pairingCombinatorDenotes''.
  Qed.

  Lemma leftProjectionCombinatorCorrect {pca : Pca} (a b : pca) :
    π1*(π*&a*&b) ≃ &a.
  Proof.
    destruct (pairingCombinatorDenotes'' a b) as [p Hp]. rewrite Hp.
    unfold π1. rewrite combinatoryCompletenessInstance1. simpl.
    rewrite <- Hp. unfold π. setoid_rewrite combinatoryCompletenessInstance3.
    apply kSpec.
  Qed.

  Lemma leftProjectionCombinatorCorrect' {pca : Pca} (t : term 0) (b : pca) :
    π1*(π*t*&b) ≃ t.
  Proof.
    apply correctness2. intro a. split; intro H.
    - assert (t!) as [a' Ht] by eauto 7 using subTermDenotes. rewrite Ht in *.
      rewrite leftProjectionCombinatorCorrect in H. exact H.
    - rewrite H. apply leftProjectionCombinatorCorrect.
  Qed.

  Lemma leftProjectionCombinatorDenotes {pca : Pca} : π1!.
  Proof.
    cut (π1*(π*&k*&k)!);
    eauto using subTermDenotes, leftProjectionCombinatorCorrect.
  Qed.

  Lemma rightProjectionCombinatorCorrect {pca : Pca} (a b : pca) :
    π2*(π*&a*&b) ≃ &b.
  Proof.
    destruct (pairingCombinatorDenotes'' a b) as [p Hp]. rewrite Hp.
    unfold π2. rewrite combinatoryCompletenessInstance1. simpl.
    destruct (kAltCombinatorDenotes) as [k' Hk'].
    rewrite Hk', <- Hp. unfold π. rewrite combinatoryCompletenessInstance3. simpl.
    rewrite <- Hk'. apply kAltCombinatorCorrect.
  Qed.

  Lemma rightProjectionCombinatorCorrect' {pca : Pca} (a : pca) (t : term 0) :
    π2*(π*&a*t) ≃ t.
  Proof.
    apply correctness2. intro b. split; intro H.
    - assert (t!) as [b' Ht] by eauto 6 using subTermDenotes. rewrite Ht in *.
      rewrite rightProjectionCombinatorCorrect in H. exact H.
    - rewrite H. apply rightProjectionCombinatorCorrect.
  Qed.

  Lemma rightProjectionCombinatorDenotes {pca : Pca} : π2!.
  Proof.
    assert (π2*(π*&k*&k)!) by eauto using rightProjectionCombinatorCorrect.
    eauto using subTermDenotes, rightProjectionCombinatorCorrect.
  Qed.

  Lemma natRepresentationCombinatorDenotes {pca : Pca} (n : nat) : #n!.
  Proof.
    induction n as [ | n [a IHn]].
    - apply identityCombinatorDenotes.
    - unfold natRepresentationCombinator. rewrite IHn.
      destruct kAltCombinatorDenotes as [k' Hk']. rewrite Hk'.
      apply pairingCombinatorDenotes''.
  Qed.

  Lemma caseCombinatorCorrect0 {pca : Pca} (a b : pca) : δ*&a*&b*#0 ≃ &a.
  Proof.
    simpl. destruct identityCombinatorDenotes as [i Hi]. rewrite Hi.
    setoid_rewrite combinatoryCompletenessInstance3. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    setoid_rewrite combinatoryCompletenessInstance1. simpl.
    rewrite <- Hi, identityCombinatorCorrect'.
    apply kSpec.
  Qed.

  Lemma caseCombinatorCorrect0' {pca : Pca} (t : term 0) (b : pca) :
    δ*t*&b*#0 ≃ t.
  Proof.
    apply correctness2. intro a. split; intro H.
    - assert (t!) as [a' Ht] by eauto 7 using subTermDenotes. rewrite Ht in *.
      rewrite caseCombinatorCorrect0 in H. exact H.
    - rewrite H. apply caseCombinatorCorrect0.
  Qed.

  Lemma caseCombinatorCorrectS {pca : Pca} (n : nat) (a b : pca) :
    δ*&a*&b*#(S n) ≃ &b.
  Proof.
    destruct
      (natRepresentationCombinatorDenotes n) as [n' Hn],
      (natRepresentationCombinatorDenotes (S n)) as [Sn HSn].
    unfold δ. rewrite HSn, combinatoryCompletenessInstance3. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- HSn. simpl. rewrite Hn, leftProjectionCombinatorCorrect'.
    apply kAltCombinatorCorrect.
  Qed.

  Lemma caseCombinatorCorrectS' {pca : Pca} (a : pca) (t : term 0) (x : nat) :
    δ*&a*t*#(S x) ≃ t.
  Proof.
    apply correctness2. intro b. split; intro H.
    - assert (t!) as [b' Ht] by eauto 7 using subTermDenotes. rewrite Ht in *.
      rewrite caseCombinatorCorrectS in H. exact H.
    - rewrite H. apply caseCombinatorCorrectS.
  Qed.

  Lemma caseCombinatorDenotes'' {pca : Pca} (a b : pca) : δ*&a*&b!.
  Proof.
    assert (δ*&a*&b*#0!) by eauto using caseCombinatorCorrect0.
    destruct (natRepresentationCombinatorDenotes 0) as [x Hx]. rewrite Hx in H.
    eauto using subTermDenotes.
  Qed.

  Lemma caseCombinatorDenotes' {pca : Pca} (a : pca) : δ*&a!.
  Proof.
    pose proof (caseCombinatorDenotes'' a a). eauto using subTermDenotes.
  Qed.

  Lemma caseCombinatorDenotes {pca : Pca} : δ!.
  Proof. pose proof (caseCombinatorDenotes' k). eauto using subTermDenotes. Qed.

  Lemma successorCombinatorCorrect {pca : Pca} (n : nat) : σ*#n ≃ #(S n).
  Proof. reflexivity. Qed.

  Lemma successorCombinatorDenotes' {pca : Pca} (n : nat) : σ*#n!.
  Proof.
    rewrite successorCombinatorCorrect.
    apply natRepresentationCombinatorDenotes.
  Qed.

  Lemma successorCombinatorDenotes {pca : Pca} : σ!.
  Proof.
    pose proof (successorCombinatorDenotes' 0). eauto using subTermDenotes.
  Qed.

  Lemma predecessorCombinatorCorrect0 {pca : Pca} : ψ*#0 ≃ #0.
  Proof.
    unfold natRepresentationCombinator.
    destruct
      identityCombinatorDenotes as [i Hi],
      rightProjectionCombinatorDenotes as [p2 Hp2].
    rewrite Hi.
    unfold ψ. rewrite combinatoryCompletenessInstance1. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    assert (π1*&i ≃ &k) as H. {
      unfold π1. rewrite combinatoryCompletenessInstance1. simpl. rewrite <- Hi.
      apply identityCombinatorCorrect.
    }
    rewrite H, Hp2, Hi, kSpec, <- Hi.
    apply identityCombinatorCorrect'.
  Qed.

  Lemma predecessorCombinatorCorrectS {pca : Pca} (n : nat) : ψ*#(S n) ≃ #n.
  Proof.
    destruct
      (natRepresentationCombinatorDenotes n) as [n' Hn],
      (natRepresentationCombinatorDenotes (S n)) as [Sn HSn].
    rewrite Hn, HSn.
    unfold ψ. rewrite combinatoryCompletenessInstance1. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- HSn. simpl. rewrite Hn at 1.
    rewrite leftProjectionCombinatorCorrect'.
    destruct
      identityCombinatorDenotes as [i Hi],
      kAltCombinatorDenotes as [k' Hk'].
    rewrite
      Hi, kAltCombinatorCorrect', Hk', rightProjectionCombinatorCorrect', Hn.
    reflexivity.
  Qed.

  Lemma predecessorCombinatorCorrect {pca : Pca} (n : nat) : ψ*#n ≃ #(n-1).
  Proof.
    destruct n as [ | n].
    - rewrite predecessorCombinatorCorrect0. reflexivity.
    - rewrite predecessorCombinatorCorrectS. simpl. rewrite <- Minus.minus_n_O.
      reflexivity.
  Qed.

  Lemma predecessorCombinatorDenotes {pca : Pca} : ψ!.
  Proof. apply representationsDenote. Qed.

  Lemma fixedPointCombinatorCorrect {pca : Pca} (a : pca) : φ1*&a ≃ &a*(φ1*&a).
  Proof.
    unfold φ1 at 1. simpl.
    set (u := x22*(x12*x12*x22)). unfold u at 1.
    destruct (representationsDenote u) as [u' Hu].
    rewrite Hu, combinatoryCompletenessInstance2. simpl. rewrite <- Hu.
    reflexivity.
  Qed.

  Lemma fixedPointCombinatorCorrect' {pca : Pca} (t : term 0) : φ1*t ≃ t*(φ1*t).
  Proof.
    apply correctness2. intro a. split; intro H.
    - assert (t!) as [b Ht] by eauto using subTermDenotes.
      rewrite Ht, <- H in *. symmetry.
      apply fixedPointCombinatorCorrect.
    - assert (t!) as [b Ht] by eauto using subTermDenotes.
      rewrite Ht, <- H in *.
      apply fixedPointCombinatorCorrect.
  Qed.

  Lemma doubleFixedPointCombinatorDenotes {pca : Pca} : φ2!.
  Proof.
    unfold φ2.
    set (u := x23*(x13*x13*x23)*x33). unfold u at 1.
    destruct (representationsDenote u) as [u' Hu]. rewrite Hu. clear Hu.
    fold u. cutrewrite (λ u * &u' = λ u ** &&(();; u')); [ | reflexivity].
    apply representationsDenote''. reflexivity.
  Qed.

  Lemma doubleFixedPointCombinatorDenotes' {pca : Pca} (a : pca) : φ2*&a!.
  Proof.
    unfold φ2.
    set (u := x23*(x13*x13*x23)*x33). unfold u at 1.
    destruct (representationsDenote u) as [u' Hu].
    rewrite Hu. fold u.
    cutrewrite (λ u * &u' * &a = λ u ** &&(();; u';; a)); [ | reflexivity].
    apply combinatoryCompleteness1.
  Qed.

  Lemma doubleFixedPointCombinatorCorrect {pca : Pca} (a b : pca) :
    φ2*&a*&b ≃ &a*(φ2*&a)*&b.
  Proof.
    unfold φ2 at 1. simpl.
    set (u := x23*(x13*x13*x23)*x33). unfold u at 1.
    destruct (representationsDenote u) as [u' Hu].
    rewrite Hu, combinatoryCompletenessInstance3. simpl. rewrite <- Hu.
    reflexivity.
  Qed.

  Lemma primitiveRecursionCombinatorLemma {pca : Pca} (a b : pca) (x : nat) :
    ρ*&a*&b*#x ≃ δ*(&k*&a)*(r'*(φ2*r)*&a*&b*#x)*#x*&k.
  Proof.
    destruct (natRepresentationCombinatorDenotes x) as [x' Hx]. rewrite Hx.
    unfold ρ. rewrite combinatoryCompletenessInstance3. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    assert (r!) as Hr by eauto using representationsDenote.
    destruct Hr as [r'' Hr]. rewrite Hr.
    setoid_rewrite doubleFixedPointCombinatorCorrect.
    destruct (doubleFixedPointCombinatorDenotes' r'') as [φr Hφr].
    setoid_rewrite Hφr.
    setoid_rewrite <- Hr.
    setoid_rewrite combinatoryCompletenessInstance4. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- Hφr, <- Hr.
    reflexivity.
  Qed.

  Lemma rDenotationLemma {pca : Pca} (a b : pca) (x : nat) :
    r'*(φ2*r)*&a*&b*#x!.
  Proof.
    assert (r!) as [c Hc] by auto using representationsDenote.
    destruct
      (doubleFixedPointCombinatorDenotes' c) as [d Hd],
      (natRepresentationCombinatorDenotes x) as [e He].
    rewrite Hc, Hd, He.
    cutrewrite (r' * &d * &a * &b * &e = r' ** &&(();; d;; a;; b;; e));
      [ | reflexivity].
    apply combinatoryCompleteness1.
  Qed.

  Lemma primitiveRecursionCombinatorCorrect0 {pca : Pca} (a b : pca) :
    ρ*&a*&b*#0 ≃ &a.
  Proof.
    rewrite primitiveRecursionCombinatorLemma.
    destruct (rDenotationLemma a b 0) as [r'' Hr].
    rewrite Hr, caseCombinatorCorrect0', kSpec.
    reflexivity.
  Qed.

  Lemma primitiveRecursionCombinatorCorrectS {pca : Pca} (a b : pca) (x : nat) :
    ρ*&a*&b*#(S x) ≃ &b*#x*(ρ*&a*&b*#x).
  Proof.
    rewrite primitiveRecursionCombinatorLemma.
    destruct (rDenotationLemma a b (S x)) as [r'' Hr''].
    destruct (kaDenotes a) as [ka Hka].
    rewrite Hr'', Hka, caseCombinatorCorrectS', <- Hr''.
    assert (r!) as [r''' Hr'''] by eauto using representationsDenote.
    destruct
      (natRepresentationCombinatorDenotes x) as [x' Hx],
      (natRepresentationCombinatorDenotes (S x)) as [Sx HSx],
      (doubleFixedPointCombinatorDenotes' r''') as [φr Hφr].
    rewrite Hx, HSx, Hr''', Hφr, combinatoryCompletenessInstance5. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- HSx, predecessorCombinatorCorrect, <- Hφr, <- Hr'''. simpl.
    rewrite <- Minus.minus_n_O.
    unfold ρ. rewrite combinatoryCompletenessInstance3. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- Hx.
    reflexivity.
  Qed.

  Lemma primitiveRecursionCombinatorDenotes {pca : Pca} : ρ!.
  Proof. apply representationsDenote. Qed.

  Lemma primitiveRecursionCombinatorDenotes'' {pca : Pca} (a b : pca) :
    ρ*&a*&b!.
  Proof.
    cutrewrite (ρ*&a*&b = ρ ** &&(();; a;; b)); [ | reflexivity].
    apply combinatoryCompleteness1.
  Qed.

  Lemma primitiveRecursionCombinatorDenotes' {pca : Pca} (a : pca) : ρ*&a!.
  Proof.
    pose proof (primitiveRecursionCombinatorDenotes'' a a) as H.
    eauto using subTermDenotes.
  Qed.

  Lemma additionCombinatorCorrect {pca : Pca} (x y : nat) : α*#x*#y ≃ #(x + y).
  Proof.
    unfold α.
    destruct
      (natRepresentationCombinatorDenotes x) as [x' Hx],
      (natRepresentationCombinatorDenotes y) as [y' Hy],
      successorCombinatorDenotes as [S HS].
    destruct (kaDenotes S) as [kS HkS].
    rewrite Hx, Hy, combinatoryCompletenessInstance2. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    rewrite <- Hx, HS, HkS. clear x' Hx.
    induction x as [ | x IHx].
    - setoid_rewrite primitiveRecursionCombinatorCorrect0. rewrite <- Hy.
      reflexivity.
    - setoid_rewrite primitiveRecursionCombinatorCorrectS.
      destruct (natRepresentationCombinatorDenotes x) as [x' Hx].
      rewrite IHx, Hx, <- HkS, <- HS, kSpec', successorCombinatorCorrect.
      reflexivity.
  Qed.

  Lemma additionCombinatorDenotes' {pca : Pca} (x : nat) : α*#x!.
  Proof.
    assert (α*#x*#x!) as H. {
      destruct (natRepresentationCombinatorDenotes (x + x)) as [xx Hxx].
      exists xx. rewrite additionCombinatorCorrect, <- Hxx. reflexivity.
    }
    eauto using subTermDenotes.
  Qed.

  Lemma additionCombinatorDenotes {pca : Pca} : α!.
  Proof.
    pose proof (additionCombinatorDenotes' 0) as H. eauto using subTermDenotes.
  Qed.

  Lemma multiplicationCombinatorCorrect {pca : Pca} (x y : nat) :
    μ*#x*#y ≃ #(x * y).
  Proof.
    unfold μ.
    destruct
      (natRepresentationCombinatorDenotes x) as [x' Hx],
      (natRepresentationCombinatorDenotes y) as [y' Hy],
      (additionCombinatorDenotes' y) as [αy Hαy].
    rewrite Hx, Hy, combinatoryCompletenessInstance2. simpl.
    setoid_rewrite closedTermSubstitutionLemma0.
    destruct (kaDenotes αy) as [kαy Hkαy], identityCombinatorDenotes as [i Hi].
    rewrite <- Hx, <- Hy, Hαy, Hkαy, Hi. clear x' Hx.
    induction x as [ | x IHx].
    - rewrite primitiveRecursionCombinatorCorrect0, Hi. reflexivity.
    - rewrite primitiveRecursionCombinatorCorrectS.
      destruct (natRepresentationCombinatorDenotes x) as [x' Hx].
      rewrite IHx, Hx, <- Hkαy, <- Hαy, kSpec', additionCombinatorCorrect.
      reflexivity.
  Qed.

  Lemma multiplicationCombinatorDenotes' {pca : Pca} (x : nat) : μ*#x!.
  Proof.
    assert (μ*#x*#x!) as H. {
      destruct (natRepresentationCombinatorDenotes (x * x)) as [xx Hxx].
      exists xx. rewrite multiplicationCombinatorCorrect, <- Hxx. reflexivity.
    }
    eauto using subTermDenotes.
  Qed.

  Lemma multiplicationCombinatorDenotes {pca : Pca} : μ!.
  Proof.
    pose proof (multiplicationCombinatorDenotes' 0) as H.
    eauto using subTermDenotes.
  Qed.

  Lemma correctArithmetic {pca : Pca} (x y : nat) : x = y <-> #x ≃ #y.
  Proof. (* TODO *) admit. Qed.

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

  Global Opaque ι λ κ π π1 π2 δ σ ψ φ1 φ2 ρ α μ natRepresentationCombinator.

End PCA.

Module PCA_COERCIONS.
  Import PCA.
  Import PAS.
  Coercion pas : Pca >-> Pas.
End PCA_COERCIONS.
