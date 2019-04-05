(** model categories **)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.pushouts.

Local Open Scope cat.


Lemma non_dep_transportf_trivial {A B: UU} {a a': A} (b: B) (p: a = a'):
  transportf (λ x, B) p b = b.
Proof.
  apply (eqtohomot (transportf_const p B)).
Defined.

Section WeakFactorisationSystem.

  Context {C: precategory}.

  Definition class_mors (C: precategory) := ∏(a b: C), hsubtype (C ⟦a,b⟧).

  Definition comm_square {a b x y: C} (l: a --> b) (r: x --> y) :=
    ∑(f: a --> x) (g: b --> y), r∘f = g∘l.

  Definition lifting_to_comm_square {a b x y: C} (l: a --> b) (r: x --> y) :
    C⟦b,x⟧ → comm_square l r :=
    λ h, (h∘l,, r∘h,, assoc' l h r).

  Definition lifting {a b x y: C} (l: a --> b) (r: x --> y) :=
    ∏(sq: comm_square l r), hfiber (lifting_to_comm_square l r) sq.

  Definition llp {a b: C} (l: a --> b) (R: class_mors C) :=
    ∏(x y: C), ∏(r : R x y), lifting l (pr1 r).

  Definition rlp {x y: C} (L: class_mors C) (r: x --> y) :=
    ∏(a b: C), ∏(l : L a b), lifting (pr1 l) r.

  Definition is_left_orth (L R: class_mors C) :=
    ∏(a b: C), ∏(l: a --> b), llp l R ≃ L a b l.

  Definition is_right_orth (L R: class_mors C) :=
    ∏(a b: C), ∏(r: a --> b), rlp L r ≃ R a b r.

  Definition is_factorization_system (L R: class_mors C) :=
    ∏(a b: C), ∏(f: a --> b), ∑(c: C), ∑(l: a --> c) (r: c --> b), f = r∘l.

  Definition is_weak_factorization_system  (L R: class_mors C) :=
    (is_left_orth L R)
      × (is_right_orth L R)
      × (is_factorization_system L R).

  Lemma has_homsets_isos_llp (hs: has_homsets C) {a b: C} (α: iso a b) :
    ∏(x y: C), ∏(f: x --> y), lifting α f.
  Proof.
    intros x y f. intros [X [Y p]].
    exists (X ∘ inv_from_iso α).
    unfold lifting_to_comm_square.

    eapply total2_paths2_f.
    rewrite transportf_total2. simpl.
    eapply total2_paths2_f.
    apply hs.
    Unshelve.
    rewrite assoc, iso_inv_after_iso, id_left. reflexivity.
    Unshelve.
    {
      rewrite non_dep_transportf_trivial.
      rewrite assoc'. apply iso_inv_on_right. exact p.
    }
  Defined.

  Lemma has_homsets_isos_rlp (hs: has_homsets C) {x y: C} (α: iso x y) :
    ∏(a b: C), ∏(f: a --> b), lifting f α.
  Proof.
    intros a b f. intros [X [Y p]].
    exists (inv_from_iso α ∘ Y).
    unfold lifting_to_comm_square.

    eapply total2_paths2_f. rewrite transportf_total2. simpl.
    eapply total2_paths2_f. apply hs.

    Unshelve.
    {
      rewrite assoc. symmetry.
      apply iso_inv_on_left. symmetry.
      exact p.
    }

    Unshelve.
    {
      rewrite non_dep_transportf_trivial.
      rewrite assoc', iso_after_iso_inv, id_right.
      reflexivity.
    }
  Defined.

  Theorem has_homsets_implies_lifting_sets (hs: has_homsets C) :
    ∏(a b x y: C), ∏(l:a --> b), ∏(r: x --> y),
    ∏(sq: comm_square l r), isaset(hfiber (lifting_to_comm_square l r) sq).
  Proof.
    intros a b x y l r [X [Y p]].
    apply isaset_hfiber. apply hs.
    apply isaset_total2. apply hs.
    intro X'. apply isaset_total2. apply hs.
    intro Y'. apply isasetaprop. apply hs.
  Defined.

End WeakFactorisationSystem.

Section WFS_homsets.

  Context {C: category}.

  Lemma isos_llp {a b:C} (α: iso a b) :
    ∏(x y: C), ∏(f: x --> y), lifting α f.
  Proof.
    apply (has_homsets_isos_llp (pr2 C) α).
  Defined.

  Lemma isos_rlp {x y:C} (α: iso x y) :
    ∏(a b: C), ∏(f: a --> b), lifting f α.
  Proof.
    apply (has_homsets_isos_rlp (pr2 C) α).
  Defined.

End WFS_homsets.

Section ModelStructure.

  Context {C: precategory}.

  Definition two_out_of_three (W: class_mors C) :=
    ∏(a b c: C), ∏(f: a --> b) (g: b --> c),
    ((W a b f × W b c g) -> W a c (g∘f))
      × ((W a b f × W a c (g∘f)) -> W b c g)
      × ((W b c g × W a c (g∘f)) -> W a b f).

  Definition intersect (L R: class_mors C) : class_mors C.
    intros a b f. exact (hconj (L a b f) (R a b f)).
  Defined.

End ModelStructure.

Definition model_structure (C: precategory) :=
  ∑(Cof Weq Fib: class_mors C),
  (two_out_of_three Weq)
    × (is_weak_factorization_system (intersect Cof Weq) Fib)
    × (is_weak_factorization_system Cof (intersect Fib Weq)).

Definition Weq (C: precategory) (S: model_structure C) := pr1 (pr2 C).
Definition Cof (C: precategory) (S: model_structure C) := pr1 C.
Definition Fib (C: precategory) (S: model_structure C) := pr1( pr2 (pr2 C)).

Definition model_category :=
  ∑(C: category), (BinProducts C) × (BinCoproducts C) × (model_structure C).

Definition category_from_modelcat : model_category -> category :=
  fun C => pr1 C.

Coercion category_from_modelcat : model_category >-> category.

Definition structure_from_modelcat : ∏(C: model_category), model_structure C :=
  fun C => pr222 C.

Coercion structure_from_modelcat : model_category >-> model_structure.

Section Cylinders.

  Context {C: model_category}.

  Definition codiagonal (a: C) (aua: BinCoproduct C a a): aua --> a.
    apply (pr2 aua). exact (identity a). exact (identity a).
  Defined.

End Cylinders.