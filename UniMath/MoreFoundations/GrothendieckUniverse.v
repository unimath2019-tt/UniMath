(* -*- coding: utf-8 *)

(** * Grothendieck Universes *)
(*Require Import Coq.Init.Prelude.*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Definition pre_guniverse : UU := ∑ (A : hSet), A → hSet.
Definition pr1GUni : pre_guniverse -> hSet := @pr1 hSet _.
Coercion pr1GUni: pre_guniverse >-> hSet.
Definition El {A : pre_guniverse} : A → hSet := (pr2 A).

Theorem emptyisaset : isaset empty.
Proof. intros a. contradiction. Defined.
Definition emptyset : hSet := hSetpair empty emptyisaset.

Definition guniverse_bool (A : pre_guniverse) :=
  ∑ (b : A), El b = boolset.
Definition guniverse_empty (A : pre_guniverse) :=
  ∑ (emp : A), El emp  = emptyset.
Definition guniverse_sigma (A : pre_guniverse) : UU :=
  ∏ (a : A) (b : El a → A),
    ∑ (p : A), El p  = (∑ (x : El a), El (b x))%set.
Definition guniverse_pi (A : pre_guniverse) : UU :=
  ∏ (a : A) (b : El a → A),
    ∑ (p : A), El p  = (∏ (x : El a), El (b x))%set.

Definition is_guniverse (A : pre_guniverse) : UU :=
  guniverse_bool A ×
  guniverse_empty A ×
  guniverse_sigma A ×
  guniverse_pi A.
Definition guniverse : UU :=
  ∑ (A : pre_guniverse), is_guniverse A.

Section nat_grothendieck_universe.
  Definition decode_nat : nat -> hSet.
    induction 1 as [|_ IH].
    - exact emptyset.
    - exact (setcoprod unitset IH).
  Defined.

  (* A series of lemmas that we will need for the main theorem *)
  Lemma equal_carrier_equal_hset {A B : hSet} : (A : UU) = (B : UU) → A = B.
  Proof.
    intros H; destruct A, B; apply total2_paths2_f with H; apply isapropisaset.
  Defined.

  Lemma decode_nat_plus (a b : nat) :
    decode_nat a ⨿ decode_nat b = decode_nat (a + b).
  Proof.
    induction a; simpl in *.
    - symmetry. apply weqtopaths; refine (_ ,, isweqii2withneg _ _); auto.
    - rewrite (weqtopaths (weqcoprodasstor _ _ _)), IHa; auto.
  Defined.

  Lemma decode_nat_times (a b : nat) :
    (decode_nat a × decode_nat b) = decode_nat (a * b).
  Proof.
    induction a; simpl in *.
    - apply weqtopaths; apply weqtoempty; destruct 1; auto.
    - rewrite (weqtopaths (weqdirprodcomm _ _)).
      rewrite (weqtopaths (weqrdistrtocoprod _ _ _)).
      rewrite (pathsinv0 (weqtopaths (weqtodirprodwithunit _))).
      rewrite (weqtopaths (weqdirprodcomm _ _)).
      rewrite natpluscomm, IHa, decode_nat_plus.
      auto.
  Defined.

  Lemma bool_decode_nat : setcoprod unitset (setcoprod unitset emptyset) = boolset.
  Proof.
    apply equal_carrier_equal_hset; simpl.
    rewrite (pathsinv0 (weqtopaths (weqcoprodasstor _ _ _))).
    rewrite (weqtopaths boolascoprod).
    symmetry; apply weqtopaths; refine (inl ,, isweqii1withneg _ _); auto.
  Defined.

  Definition sigma_encode (a : nat) (b : decode_nat a → nat) : nat.
    induction a.
    - exact 0.
    - exact (b (inl tt) + IHa (fun x => b (inr x))).
  Defined.

  Definition iterated_coprod (a : nat) (b : decode_nat a → UU) : UU.
    induction a.
    - exact empty.
    - exact (b (inl tt) ⨿ IHa (fun x => b (inr x))).
  Defined.

  Lemma sigma_encode_iterated_coprod (a : nat) (b : decode_nat a → nat) :
    (decode_nat (sigma_encode a b) : UU) = iterated_coprod a (fun x => decode_nat (b x)).
  Proof.
    induction a.
    - auto.
    - simpl in *. rewrite (pathsinv0 (IHa _)), decode_nat_plus; auto.
  Defined.

  Definition finite_sigma_as_coprod (a : nat) (b : decode_nat a -> UU) :
    (∑ (x : decode_nat a), b x) = iterated_coprod a b.
  Proof.
    induction a; simpl in *.
    - apply weqtopaths. apply weqtoempty. exact pr1.
    - rewrite
        (weqtopaths (weqtotal2overcoprod b)),
      (weqtopaths (weqtotal2overunit (fun x => b (inl x)))),
      (IHa (fun x => b (inr x))).
      auto.
  Defined.

  Lemma sigma_decode_nat (a : nat) (b : decode_nat a → nat) :
    decode_nat (sigma_encode a b) = (∑ (c : decode_nat a), decode_nat (b c))%set.
  Proof.
    apply equal_carrier_equal_hset. simpl.
    rewrite (sigma_encode_iterated_coprod a b), finite_sigma_as_coprod.
    auto.
  Defined.

  Definition pi_encode (a : nat) (b : decode_nat a → nat) : nat.
    induction a.
    - exact 1.
    - exact (b (inl tt) * IHa (fun x => b (inr x))).
  Defined.

  Definition iterated_prod (a : nat) (b : decode_nat a → UU) : UU.
    induction a.
    - exact unit.
    - exact (b (inl tt) × IHa (fun x => b (inr x))).
  Defined.

  Lemma pi_encode_iterated_prod (a : nat) (b : decode_nat a → nat) :
    (decode_nat (pi_encode a b) : UU) = iterated_prod a (fun x => decode_nat (b x)).
  Proof.
    induction a; simpl.
    - symmetry; apply weqtopaths; refine (inl ,, isweqii1withneg _ _); auto.
    - simpl in *. rewrite (pathsinv0 (IHa _)), decode_nat_times; auto.
  Defined.

  Definition iscontr_empty (X : ∅ → UU) :
    iscontr  (∏ (a : ∅), X a).
  Proof.
    exists fromemptysec; intros. apply funextsec. unfold homotsec. intros; contradiction.
  Qed.


  Definition finite_pi_as_prod (a : nat) (b : decode_nat a -> UU) :
    (∏ (x : decode_nat a), b x) = iterated_prod a b.
  Proof.
    induction a; simpl in *.
    - apply weqtopaths. apply weqcontrtounit. apply iscontr_empty.
    - rewrite
        (weqtopaths (weqsecovercoprodtoprod _)),
      (weqtopaths (weqsecoverunit _)),
      (IHa (fun x => b (inr x))).
      auto.
  Defined.

  Lemma pi_decode_nat (a : nat) (b : decode_nat a → nat) :
    decode_nat (pi_encode a b) = (∏ (c : decode_nat a), decode_nat (b c))%set.
  Proof.
    apply equal_carrier_equal_hset. simpl.
    rewrite (pi_encode_iterated_prod a b), finite_pi_as_prod.
    auto.
  Defined.


  Theorem nat_is_set_of_finite_sets : is_guniverse (natset ,, decode_nat).
  Proof.
    repeat split.
    - exact (2 ,, bool_decode_nat).
    - exists 0; auto.
    - intros a b. exists (sigma_encode a b); simpl; apply sigma_decode_nat.
    - intros a b. exists (pi_encode a b); simpl; apply pi_decode_nat.
  Defined.
End nat_grothendieck_universe.

(* A construction of Gylterud's V universe from
 *   From Multisets to Sets in Homotopy Type Theory
 * October 9 2018
 *)
Section gylterud_grothendieck_universe.

  (* For now, we will define this as an inductive. Later we may attempt
   * to remove this and postulate/construct it manually
   *)
  Inductive W (A : hSet) (B : A → hSet) : UU :=
  | sup : ∏ (a : A), (B a → W A B) → W A B.
  Arguments sup {_} {_} _ _.

  Definition prjlbl {A B} (w : W A B) :=
    match w with
    | sup a b => a
    end.
  Definition prjfun {A B} (w : W A B) : B (prjlbl w) → W A B:=
    match w with
    | sup a b => b
    end.

  Definition W_unfolding (A : hSet) (B : A → hSet):
    W A B ≃ (∑ (a : A), B a → W A B).
  Proof.
    use tpair.
    - destruct 1. exact (a ,, w).
    - simpl.
      intro w.
      use tpair.
      * destruct w as [a b].
        exists (sup a b); auto.
      * simpl.
        intros [w' p].
        destruct w' as [a' b'].
        rewrite <-p.
        auto.
  Defined.


  (* It is unclear if we will require these next two lemmas lemmas at the end of the day.
   * This follows
   *  https://homotopytypetheory.org/2012/09/21/positive-h-levels-are-closed-under-w/
   *)
  Definition supequalf
    {A : hSet} {B : A → hSet} {a a' : A} {b : B a → W A B} {b' : B a' → W A B} :
    (sup a b = sup a' b') ≃
    (∑ (p : a = a'), ∏ (x : B a'), transportf (fun x => B x → W A B) p b x = b' x).
  Proof.
    set (H := total2_paths_equiv (fun a => B a → W A B) (a ,, b) (a' ,, b')).
    unfold PathPair in *. simpl in *.
    assert
      ((∑ p : a = a', transportf (λ x : A, B x → W A B) p b = b') ≃
       (∑ p0 : a = a', ∏ x : B a', transportf (λ x0 : A, B x0 → W A B) p0 b x = b' x)) as H'.
    { apply (weqtotal2 (idweq _)).
      intro p.
      apply invweq.
      apply weqfunextsec. }
    rewrite <-(weqtopaths H').
    rewrite <-(weqtopaths H).
    apply (weqonpaths (W_unfolding A B)).
  Qed.

  Lemma W_isaset A B : isaset (W A B).
  Proof.
    intros w.
    induction w as [a b IH].
    intros [a' b'].
    rewrite (weqtopaths supequalf).

    refine
      (isaprop_total2
         ((a = a') ,, (pr2 A a a'))
         (fun p =>  ((∏ x : B a', transportf (λ x0 : A, B x0 → W A B) p b x = b' x) ,, _))).
    apply impred_isaprop.
    intro c.
    rewrite <-(pathsinv0inv0 p).
    rewrite (idpath _ : transportf _ (! (! p)) b = transportb _ (! p) b).
    rewrite <-transportb_fun'.
    apply IH.
  Defined.

End gylterud_grothendieck_universe.
