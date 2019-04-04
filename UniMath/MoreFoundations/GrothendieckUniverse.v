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
  Lemma equal_carrier_equal_hset {A B : hSet} : (A : UU) = (B : UU) ≃ A = B.
  Proof.
    rewrite (weqtopaths (hSet_univalence _ _)).
    apply univalence.
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
  Defined.

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
  Inductive W (A : UU) (B : A → UU) : UU :=
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

  Definition W_unfolding (A : UU) (B : A → UU):
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
    {A} {B : A → UU} {a a' : A} {b : B a → W A B} {b' : B a' → W A B} :
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
  Defined.

  Lemma W_isofhlevel n {A : UU} {B : A → UU} :
    isofhlevel (S n) A →
    (∏ (a : A), isofhlevel (S n) (B a)) →
    isofhlevel (S n) (W A B).
  Proof.
    intros hlevelA hlevelB w.
    induction w as [a b IH].
    intros [a' b'].
    rewrite (weqtopaths supequalf).

    apply (isofhleveltotal2 n); auto.
    intro p.
    apply impred.
    intro c.
    rewrite <-(pathsinv0inv0 p).
    rewrite (idpath _ : transportf _ (! (! p)) b = transportb _ (! p) b).
    rewrite <-transportb_fun'.
    apply IH.
  Defined.

  (* The type of multisets, NOT an hSet. *)
  Definition M : UU := W hSet (fun A => (A : UU)).

  Definition memberM (m1 m2 : M) : UU.
  Proof.
    induction m2 as [A El _].
    exact (∑ (a : A), El a = m1).
  Defined.

  Definition memberM_isaset (m1 m2 : M) :
    isaset (memberM m1 m2).
  Proof.
    induction m2 as [A El _].
    refine (isaset_total2_hSet A (fun a => ((El a = m1) ,, _))).
    set (H' := @W_isofhlevel 2 hSet (fun a => (a : UU))).
    assert (isofhlevel 3 hSet) as hoflevel3.
    { apply isofhlevelssn.
      intros [A' A'_isaset].
      rewrite <-(weqtopaths equal_carrier_equal_hset).
      apply (isofhlevelpathspace 2 A' A'); apply isofhlevelssnset; auto.
    }
    apply H' in hoflevel3.
    change isaset with (isofhlevel 2).
    exact (hoflevel3 (El a) m1).
    intros [? ?].
    apply hlevelntosn.
    change isaset with (isofhlevel 2).
    auto.
  Defined.

  Definition M_eq : M → M → UU.
  Proof.
    intros m1; induction m1 as [A ElA IH].
    intros m2; induction m2 as [B ElB _].
    exact (∑ (p : A = B), ∏ (x : B), IH (transportb (fun x => x) (base_paths _ _ p) x) (ElB x)).
  Defined.

  Definition M_eq_char :
    ∏ (m1 m2 : M), m1 = m2 ≃ M_eq m1 m2.
  Proof.
    intros m1; induction m1 as [A ElA IH].
    intros m2; induction m2 as [B ElB _].
    apply (weqcomp supequalf).
    simpl M_eq.
    apply weqfibtototal.
    intro p.
    apply weqonsecfibers.
    intro b.
    unfold transportb; induction p; simpl.
    do 2 rewrite idpath_transportf.
    apply IH.
  Defined.

  Definition forward {A B C : UU} {f : A → C} {g : B → C} :
    (∑ (p : A → B), homotsec f (g ∘ p))
      →
    (∏ (c : C), hfiber f c → hfiber g c).
  Proof.
    intros [p h] c [a q]. exists (p a). exact ((! (h a)) @ q).
  Defined.

  Definition backward {A B C : UU} {f : A → C} {g : B → C} :
    (∏ (c : C), hfiber f c → hfiber g c)
      →
    (∑ (p : A → B), homotsec f (g ∘ p)).
  Proof.
    intros F.
    set (p := fun a => pr1 (F (f a) (a ,, idpath _))).
    set (h := fun a => ! (pr2 (F (f a) (a ,, idpath _)))).
    set (x := @tpair _ (fun p => homotsec f (g ∘ p)) p h).
    exact x.
  Defined.

  Lemma forwardbackward {A B C : UU} (f : A → C) (g : B → C) :
    ∏ (x : ∑ (p : A → B), homotsec f (g ∘ p)), backward (forward x) = x.
  Proof.
    intros x.
    induction x as [p h].
    unfold forward, backward.
    simpl.
    apply (total2_paths2_f (idpath _)).
    apply funextsec. intros a.
    rewrite idpath_transportf.
    rewrite pathscomp0rid.
    rewrite pathsinv0inv0.
    auto.
  Defined.

  Lemma backwardforward {A B C : UU} (f : A → C) (g : B → C) :
    ∏ (x : ∏ (c : C), hfiber f c → hfiber g c), forward (backward x) = x.
  Proof.
    intros F.
    unfold forward, backward.
    simpl.
    apply funextsec. intros c.
    apply funextsec. intros [a p].
    simpl.
    rewrite pathsinv0inv0.
    induction p.
    rewrite pathscomp0rid.
    auto.
  Defined.

  Lemma forward_isaweq A B C f g:
    isweq (@forward A B C f g).
  Proof.
    apply (isweq_iso forward backward).
    apply forwardbackward.
    apply backwardforward.
  Defined.

  Lemma homot_transportfb (A B : UU) (p : A = B) :
    (fun x => x) = (transportf (λ x : UU, x) p ∘ transportb (λ x : UU, x) p).
  Proof.
    apply funextfun.
    intro x.
    unfold funcomp; simpl.
    rewrite transportfbinv; auto.
  Defined.

  Lemma natural_homot {A B} {f g : A → B} {x y : A} :
    ∏ (p : x = y)(α : homotsec f g),
    α x @ maponpaths g p = maponpaths f p @ α y.
  Proof.
    intros p α.
    induction p.
    simpl.
    rewrite pathscomp0rid.
    auto.
  Defined.

  Lemma abstracted_forward' {A B C : UU} {f : A → C} {g : B → C} {p : A ≃ B} (α : homotsec f (g ∘ p)) c :
    isweq (forward (tpair (fun (p : A → B) => homotsec f (g ∘ p)) p α) c).
  Proof.
    use gradth.
    - intros [b q].
      set (β := homotweqinv f p g α).
      exact (invmap p b ,, β b @ q).
    - simpl.
      intros [a q].
      apply (total2_paths2_f (homotinvweqweq p a)).
      induction q.
      rewrite pathscomp0rid.
      apply (@transport_fun_path _ _ f (fun x => f a)).
      rewrite maponpaths_for_constant_function.
      do 2 rewrite pathscomp0rid.
      unfold homotweqinv.
      apply hornRotation.
      rewrite pathsinv0inv0.
      rewrite <- homotweqinvweqweq.
      rewrite (maponpathscomp p g).
      apply (natural_homot (homotinvweqweq p a) α).
    - simpl; intros [b q].
      unfold forward; simpl.
      apply (total2_paths2_f (homotweqinvweq p b)).
      induction q.
      rewrite pathscomp0rid.
      apply (@transport_fun_path _ _ g (fun x => g b)).
      rewrite maponpaths_for_constant_function.
      do 2 rewrite pathscomp0rid.
      unfold homotweqinv.
      rewrite path_assoc.
      rewrite (pathsinv0l (α (invmap p b))) .
      auto.
  Qed.

  Definition forward' {A B C : UU} {f : A → C} {g : B → C} :
    (∑ (p : A ≃ B), homotsec f (g ∘ p))
      →
    (∏ (c : C), hfiber f c ≃ hfiber g c).
  Proof.
    intros [p α] c.
    exists (forward ((p : A → B) ,, α) c).
    apply abstracted_forward'.
  Defined.

  Definition transportf_on_hfiber {A B} {f : A → B} {a : A} {b : B} :
    ∏ (p : f a = b), transportf (hfiber f) p (a ,, idpath _) = (a ,, p).
  Proof.
    intros p; induction p.
    rewrite idpath_transportf.
    auto.
  Defined.

  Lemma transportf_fun'' {A : UU} {P Q : A → UU} {a1 a2 : A} (f : P a1 → Q a1) (p : a1 = a2) (x : P a2)  :
    transportf (fun x => P x → Q x) p f x =
    transportf Q p (f (transportb P p x)).
  Proof.
    induction p; auto.
  Defined.

  Lemma abstracted_backwards' {A B C : UU} {f : A → C} {g : B → C} :
    ∏ (F : ∏ c : C, hfiber f c ≃ hfiber g c),
    isweq (pr1 (backward (λ c : C, F c))).
  Proof.
    intros F.
    use gradth.
    - intros b.
      exact (pr1 (invmap (F (g b)) (b ,, idpath _))).
    - intros a.
      simpl.
      set (p := pr2 ((F (f a)) (a,, idpath (f a)))).
      simpl in p.
      set (w := F (f a)) in *.
      set (fib := w (a ,, idpath (f a))) in *.
      assert (invmap (F (g (pr1 fib))) (pr1 fib,, idpath (g (pr1 fib))) =
              transportf (hfiber f) (! p) (a,, idpath (f a))) as pp.
      { set (q := (transport_section F (!p))).
        rewrite <-q.
        rewrite <-transport_invmap.
        rewrite transportf_fun''.
        unfold transportb; rewrite pathsinv0inv0.
        rewrite (transportf_on_hfiber p).
        change (pr1 fib,, p) with fib.
        unfold fib, w.
        rewrite (homotinvweqweq (F (f a))); auto. }
      rewrite pp.
      rewrite (transportf_on_hfiber (!p)).
      auto.
    - intros b.
      simpl.
      set (p := pr2 (invmap (F (g b)) (b ,, idpath (g b)))).
      simpl in p.
      set (w := invmap (F (g b))) in *.
      set (fib := w (b ,, idpath (g b))) in *.
      assert (F (f (pr1 fib)) (pr1 fib,, idpath (f (pr1 fib))) =
              transportf (hfiber g) (! p) (b,, idpath (g b))) as pp.
      { set (q := (transport_section (F : ∏ (c : C), _ → _) (!p))).
        rewrite <-q.
        rewrite transportf_fun''.
        unfold transportb; rewrite pathsinv0inv0.
        rewrite (transportf_on_hfiber p).
        change (pr1 fib,, p) with fib.
        unfold fib, w.
        rewrite (homotweqinvweq (F (g b))); auto. }
      rewrite pp.
      rewrite (transportf_on_hfiber (!p)).
      auto.
  Qed.

  Definition backwards' {A B C : UU} {f : A → C} {g : B → C} :
    (∏ (c : C), hfiber f c ≃ hfiber g c)
      →
    (∑ (p : A ≃ B), homotsec f (g ∘ p)).
  Proof.
    intros F.
    refine ((pr1 (backward F) ,, _) ,, pr2 (backward F)).
    apply abstracted_backwards'.
  Defined.

  Lemma fib_weq {A B C : UU} (f : A → C) (g : B → C) :
    (∑ (p : A ≃ B), homotsec f (g ∘ p))
      ≃
    (∏ (c : C), hfiber f c ≃ hfiber g c).
  Proof.
    exists forward'.
    use gradth.
    - exact backwards'.
    - intros [[p isweq_p] α].
      unfold backwards', forward'.
      unfold pr1weq in *.
      unfold pr1 in *.
      change (λ c : C, forward (p,, α) c) with (forward (p,, α)).
      set (x := abstracted_backwards' _).
      assert (x = isweq_p).
      { apply isapropisweq. }
      rewrite X.
      use total2_paths_f.
      * auto.
      * simpl. rewrite idpath_transportf.
        apply funextsec.
        intros a.
        rewrite pathscomp_inv.
        simpl.
        rewrite pathsinv0inv0.
        auto.
    - intros x.
      unfold backwards', forward'.
      unfold pr1weq in *.
      unfold pr2, pr1.
      apply funextsec.
      intros c.
      apply subtypeEquality; [intros a; apply isapropisweq|].
      unfold pr1.
      rewrite backwardforward.
      auto.
  Defined.

  Definition lift_equality_to_hSet {A B : hSet} : @paths UU A B → @paths hSet A B.
  Proof.
    intros p.
    apply (total2_paths_f p).
    apply isapropisaset.
  Defined.

  Lemma lift_equality_to_hSet_reduce {A B : hSet} (p : @paths UU A B) :
    base_paths _ _ (lift_equality_to_hSet p) = p.
  Proof.
    unfold lift_equality_to_hSet.
    apply base_total2_paths.
  Defined.

  Lemma lift_equality_to_hSet_eta {A B : hSet} (p : @paths hSet A B) :
    lift_equality_to_hSet (base_paths A B p) = p.
  Proof.
    unfold lift_equality_to_hSet.
    rewrite <-(total2_fiber_paths p).
    rewrite base_total2_paths.
    set (q := pr1 (isapropisaset (pr1 B) (transportf isaset (base_paths A B p) (pr2 A)) (pr2 B))).
    assert (q = fiber_paths p).
    { rewrite (pr2 (isapropisaset (pr1 B) (transportf isaset (base_paths A B p) (pr2 A)) (pr2 B))).
      auto. }
    rewrite X.
    auto.
  Defined.


  Definition remove_hSet_equality {A B : hSet} (P : A = B → UU) :
    (∑ (p : A = B), P p)
      ≃
    (∑ (p : (A : UU) = (B : UU)), P (lift_equality_to_hSet p)).
  Proof.
    unfold pr1hSet.
    use weqtotal2.
    - apply path_sigma_hprop.
      apply isapropisaset.
    - intros p; simpl.
      rewrite lift_equality_to_hSet_eta.
      apply idweq.
  Defined.

  Definition correct_equality_equivalence {A B : hSet} {C} (f : A → C) (g : B → C) (P : A = B → UU) :
    (∏ (p : A = B), P p ≃ homotsec f (g ∘ transportf (fun x => x) (base_paths _ _ p))) →
    (∑ (p : (A : UU) = (B : UU)), P (lift_equality_to_hSet p))
      ≃
    (∑ (p : A ≃ B), homotsec f (g ∘ p)).
  Proof.
    induction A as [A' A'_isaset].
    induction B as [B' B'_isaset].
    intros w.
    use weqtotal2.
    - apply univalence.
    - intros q.
      apply (weqcomp (w (lift_equality_to_hSet q))).
      rewrite (lift_equality_to_hSet_reduce q).
      simpl in *.
      apply eqweqmap.
      apply maponpaths.
      apply funextfun.
      intro a.
      unfold funcomp.
      apply maponpaths.
      induction q.
      now rewrite idpath_transportf.
  Qed.

  Definition M_extensional :
    ∏ (m1 m2 : M), m1 = m2 ≃ ∏ (m : M), memberM m m1 ≃ memberM m m2.
  Proof.
    intros m1; induction m1 as [A ElA IH].
    intros m2; induction m2 as [B ElB _].
    apply (weqcomp (M_eq_char _ _)).
    simpl.
    set (P := fun (p : @paths hSet A B) => ∏ x : B, M_eq (ElA (transportb (λ x0 : UU, x0) (base_paths _ _ p) x)) (ElB x)).
    apply (weqcomp (remove_hSet_equality P)).
    rewrite (fun x => weqtopaths (correct_equality_equivalence ElA ElB P x)).
    - apply fib_weq.
    - intros p.
      unfold P. clear P.
      set (P := fun x => M_eq (ElA (transportb (λ x0 : UU, x0) (base_paths A B p) x)) (ElB x)).
      set (w := tpair (fun f => isweq f) (transportf (fun x => x) (base_paths _ _ p)) (isweqtransportf (fun x => x) (base_paths _ _ p))).
      apply (weqcomp (weqonsecbase P w)).
      apply weqonsecfibers.
      intros a.
      unfold P.
      apply (weqcomp (invweq (M_eq_char _ _))).
      simpl.
      rewrite transportbfinv.
      unfold funcomp.
      rewrite transportb_fun'.
      apply idweq.
  Defined.

  Definition itset (m : M) : hProp.
  Proof.
    induction m as [A El IH].
    refine ((isincl El × ∏ (a : A), IH a) ,, _).
    apply isapropdirprod; [| apply impred; apply IH].
    unfold isincl, isofhlevelf. apply impred. intros t.
    apply isapropisofhlevel.
  Defined.

  (* The universe of sets *)
  Definition V : UU :=  ∑ (m : M), itset m.

  Definition V_eq_char (v1 v2 : V) :
    v1 = v2 ≃ (pr1 v1 = pr1 v2).
  Proof.
    apply subtypeInjectivity; intros m.
    apply (pr2 (itset m)).
  Defined.

  Definition memberV (v1 v2 : V) := memberM (pr1 v1) (pr1 v2).

  Lemma itset_member_prop (m : M) :
    itset m → (∏ (m' : M), isaprop (memberM m' m)).
  Proof.
    intros i.
    induction m as [A ElA _].
    induction i as [em children_itset].
    intros m'.
    apply em.
  Defined.

  Definition V_isaset : isaset V.
  Proof.
    intros v1 v2.
    rewrite (weqtopaths (V_eq_char v1 v2)).
    rewrite (weqtopaths (M_extensional (pr1 v1) (pr1 v2))).
    apply impred.
    intros m.
    apply isapropweqfromprop.
    induction v1 as [m1 prop1].
    induction m1 as [A ElA].
    apply itset_member_prop.
    simpl in prop1.
    apply prop1.
  Defined.

  Definition decode_V : V → hSet.
  Proof.
    induction 1 as [m _].
    induction m as [A ElA IH].
    refine ( (W A IH) ,, _).
    apply W_isofhlevel.
    - apply (pr2 A).
    - intros a; apply (pr2 (IH a)).
  Defined.

  Definition V_uni : pre_guniverse := ( (V ,, V_isaset) ,, decode_V).

  Definition V_empty :
    ∑ (v : V), decode_V v = emptyset.
  Proof.
    use tpair.
    - exists (sup emptyset fromempty).
      split; [|intros a; exact (fromempty a)].
      unfold isincl, isofhlevelf. intros ? x x'.
      induction x as [[] _ _].
    - unfold decode_V; simpl.
      use subtypeEquality.
      * intros a; apply isapropisaset.
      * apply weqtopaths; apply weqtoempty.
        intros w; induction w; auto.
  Defined.

End gylterud_grothendieck_universe.
