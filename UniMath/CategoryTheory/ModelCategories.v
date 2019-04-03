(** model categories **)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Definition lifting_prop {C: precategory} {a b x y: C} (l: a --> b) (r: x --> y) :=
  ∏(f: a --> x) (g: b --> y), ∑(h: b --> x), (h∘l = f) × (r∘h = g) : UU.

Definition llp {C: precategory} {a b x y: C} (l: a --> b) (r: x --> y) :=

Definition weak_factorization_system {A: category} :=
