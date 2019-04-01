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

Lemma bool_decode : setcoprod unitset unitset = boolset.
Proof.
  apply equal_carrier_equal_hset; exact (weqtopaths boolascoprod).
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

Theorem hereditarily_finite : is_guniverse (natset ,, decode).
Proof.
Admitted.
