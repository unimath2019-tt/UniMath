(* -*- coding: utf-8 *)

(** * Grothendieck Universes *)
(*Require Import Coq.Init.Prelude.*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Definition pre_guniverse : UU := ∑ (A : UU), A → hSet.
Definition pr1GUni : pre_guniverse -> UU := @pr1 UU _.
Coercion pr1GUni: pre_guniverse >-> UU.
Definition El {A : pre_guniverse} : A → hSet := (pr2 A).

Theorem emptyisaset : isaset empty.
Proof. intros a. contradiction. Qed.
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
Definition guniverse : UU :=
  ∑ (A : pre_guniverse),
  guniverse_bool A ×
  guniverse_empty A ×
  guniverse_sigma A ×
  guniverse_pi A.
