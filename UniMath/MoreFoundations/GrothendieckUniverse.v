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

Definition decode : nat -> hSet.
  induction 1 as [|_ IH].
  - exact emptyset.
  - exact (setcoprod unitset IH).
Defined.


(* A series of lemmas that we will need for the main theorem *)
Lemma equal_carrier_equal_hset {A B : hSet} : (A : UU) = (B : UU) → A = B.
Proof.
  intros H; destruct A, B; apply total2_paths2_f with H; apply isapropisaset.
Defined.

Lemma decode_plus (a b : nat) :
  decode a ⨿ decode b = decode (a + b).
Proof.
  induction a; simpl in *.
  - symmetry. apply weqtopaths; refine (_ ,, isweqii2withneg _ _); auto.
  - rewrite (weqtopaths (weqcoprodasstor _ _ _)), IHa; auto.
Defined.

Lemma decode_times (a b : nat) :
  (decode a × decode b) = decode (a * b).
Proof.
  induction a; simpl in *.
  - apply weqtopaths; apply weqtoempty; destruct 1; auto.
  - rewrite (weqtopaths (weqdirprodcomm _ _)).
    rewrite (weqtopaths (weqrdistrtocoprod _ _ _)).
    rewrite (pathsinv0 (weqtopaths (weqtodirprodwithunit _))).
    rewrite (weqtopaths (weqdirprodcomm _ _)).
    rewrite natpluscomm, IHa, decode_plus.
    auto.
Defined.

Lemma bool_decode : setcoprod unitset (setcoprod unitset emptyset) = boolset.
Proof.
  apply equal_carrier_equal_hset; simpl.
  rewrite (pathsinv0 (weqtopaths (weqcoprodasstor _ _ _))).
  rewrite (weqtopaths boolascoprod).
  symmetry; apply weqtopaths; refine (inl ,, isweqii1withneg _ _); auto.
Defined.

Definition sigma_encode (a : nat) (b : decode a → nat) : nat.
  induction a.
  - exact 0.
  - exact (b (inl tt) + IHa (fun x => b (inr x))).
Defined.

Definition iterated_coprod (a : nat) (b : decode a → UU) : UU.
  induction a.
  - exact empty.
  - exact (b (inl tt) ⨿ IHa (fun x => b (inr x))).
Defined.

Lemma sigma_encode_iterated_coprod (a : nat) (b : decode a → nat) :
  (decode (sigma_encode a b) : UU) = iterated_coprod a (fun x => decode (b x)).
Proof.
  induction a.
  - auto.
  - simpl in *. rewrite (pathsinv0 (IHa _)), decode_plus; auto.
Defined.

Definition finite_sigma_as_coprod (a : nat) (b : decode a -> UU) :
  (∑ (x : decode a), b x) = iterated_coprod a b.
Proof.
  induction a; simpl in *.
  - apply weqtopaths. apply weqtoempty. exact pr1.
  - rewrite
      (weqtopaths (weqtotal2overcoprod b)),
      (weqtopaths (weqtotal2overunit (fun x => b (inl x)))),
      (IHa (fun x => b (inr x))).
    auto.
Defined.

Lemma sigma_decode (a : nat) (b : decode a → nat) :
  decode (sigma_encode a b) = (∑ (c : decode a), decode (b c))%set.
Proof.
  apply equal_carrier_equal_hset. simpl.
  rewrite (sigma_encode_iterated_coprod a b), finite_sigma_as_coprod.
  auto.
Defined.

Definition pi_encode (a : nat) (b : decode a → nat) : nat.
  induction a.
  - exact 1.
  - exact (b (inl tt) * IHa (fun x => b (inr x))).
Defined.

Definition iterated_prod (a : nat) (b : decode a → UU) : UU.
  induction a.
  - exact unit.
  - exact (b (inl tt) × IHa (fun x => b (inr x))).
Defined.

Lemma pi_encode_iterated_prod (a : nat) (b : decode a → nat) :
  (decode (pi_encode a b) : UU) = iterated_prod a (fun x => decode (b x)).
Proof.
  induction a; simpl.
  - symmetry; apply weqtopaths; refine (inl ,, isweqii1withneg _ _); auto.
  - simpl in *. rewrite (pathsinv0 (IHa _)), decode_times; auto.
Defined.

Definition iscontr_empty (X : ∅ → UU) :
  iscontr  (∏ (a : ∅), X a).
Proof.
  exists fromemptysec; intros. apply funextsec. unfold homotsec. intros; contradiction.
Qed.


Definition finite_pi_as_prod (a : nat) (b : decode a -> UU) :
  (∏ (x : decode a), b x) = iterated_prod a b.
Proof.
  induction a; simpl in *.
  - apply weqtopaths. apply weqcontrtounit. apply iscontr_empty.
  - rewrite
      (weqtopaths (weqsecovercoprodtoprod _)),
      (weqtopaths (weqsecoverunit _)),
      (IHa (fun x => b (inr x))).
    auto.
Defined.

Lemma pi_decode (a : nat) (b : decode a → nat) :
  decode (pi_encode a b) = (∏ (c : decode a), decode (b c))%set.
Proof.
  apply equal_carrier_equal_hset. simpl.
  rewrite (pi_encode_iterated_prod a b), finite_pi_as_prod.
  auto.
Defined.


Theorem nat_is_set_of_finite_sets : is_guniverse (natset ,, decode).
Proof.
  repeat split.
  - exact (2 ,, bool_decode).
  - exists 0; auto.
  - intros a b. exists (sigma_encode a b); simpl; apply sigma_decode.
  - intros a b. exists (pi_encode a b); simpl; apply pi_decode.
Defined.
