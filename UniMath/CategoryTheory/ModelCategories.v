(** model categories **)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.


Lemma non_dep_transportf_trivial {A B: UU} {a a': A} (b: B) (p: a = a'):
  transportf (λ x, B) p b = b.
Proof.
  induction p.
  rewrite idpath_transportf.
  reflexivity.
Defined.

Section WeakFactorisationSystem.

  Context (C: precategory).

  Definition class_mors := ∏(a b: C), hsubtype (C ⟦a,b⟧).

  Definition comm_square {a b x y: C} (l: a --> b) (r: x --> y) :=
    ∑(f: a --> x) (g: b --> y), r∘f = g∘l.

  Definition lifting_to_comm_square {a b x y: C} (l: a --> b) (r: x --> y) :
    C⟦b,x⟧ → comm_square l r :=
    λ h, (h∘l,, r∘h,, assoc' l h r).

  Definition lifting {a b x y: C} (l: a --> b) (r: x --> y) :=
    ∏(sq: comm_square l r), hfiber (lifting_to_comm_square l r) sq.

  Definition llp {a b: C} (l: a --> b) (R: class_mors ) :=
    ∏(x y: C), ∏(r : R x y), lifting l (pr1 r).

  Definition rlp {x y: C} (L: class_mors) (r: x --> y) :=
    ∏(a b: C), ∏(l : L a b), lifting (pr1 l) r.

  Definition is_left_orth (L R: class_mors) :=
    ∏(a b: C), ∏(l: a --> b), llp l R ≃ L a b l.

  Definition is_right_orth (L R: class_mors) :=
    ∏(a b: C), ∏(r: a --> b), rlp L r ≃ R a b r.

  Definition is_factorization_system (L R: class_mors) :=
    ∏(a b: C), ∏(f: a --> b), ∑(c: C), ∑(l: a --> c) (r: c --> b), f = r∘l.

  Definition is_weak_factorization_system  (L R: class_mors) :=
    (is_left_orth L R)
      × (is_right_orth L R)
      × (is_factorization_system L R).



  Lemma isos_llp {hs: has_homsets C} {a b: C} (α: iso a b) : ∏(x y: C), ∏(f: x --> y), lifting α f.
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
      rewrite (non_dep_transportf_trivial (inv_from_iso α · X · f) _).
      rewrite assoc'. apply iso_inv_on_right. exact p.
    }
  Defined.

  Lemma isos_rlp {x y: C} (α: iso x y) : ∏(a b: C), ∏(f: a --> b), lifting f α.
  Proof.
    intros a b f. intros X Y. intro p.
    exists (inv_from_iso α ∘ Y).
    split.
    - rewrite assoc. symmetry. apply iso_inv_on_left. symmetry.
      exact p.
    - rewrite assoc', iso_after_iso_inv, id_right.
      reflexivity.
  Defined.

  Theorem has_homsets_implies_lifting_sets :
    has_homsets C -> ∏(a b x y: C), ∏(l:a --> b), ∏(r: x --> y),
    ∏(f: a --> x), ∏(g: b --> y), ∏(p: r∘f = g∘l), isaset().

End WeakFactorisationSystem.

Section ModelCategory.

  Context (C: precategory).

  Definition two_out_of_three (W: class_mors C) :=
    ∏(a b c: C), ∏(f: a --> b) (g: b --> c),
    ((W a b f × W b c g) -> W a c (g∘f))
      × ((W a b f × W a c (g∘f)) -> W b c g)
      × ((W b c g × W a c (g∘f)) -> W a b f).

  Definition intersect (L R: class_mors C) : class_mors C.
    intros a b f. exact (hconj (L a b f) (R a b f)).
  Defined.

  Definition model_structure :=
    ∑(Cof Weq Fib: class_mors C),
    (two_out_of_three Weq)
      × (is_weak_factorization_system C (intersect Cof Weq) Fib)
      × (is_weak_factorization_system C Cof (intersect Fib Weq)).

End ModelCategory.