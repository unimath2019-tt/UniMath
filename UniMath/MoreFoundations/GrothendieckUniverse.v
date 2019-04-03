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
    (* Massive overkill *)
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

  Definition isembedding {A B} (f : A → B) : UU :=
    ∏ (x y : A), isweq (@maponpaths _ _ f x y).

  Lemma isaprop_isembedding {A B : UU} (f : A → B) :
    isaprop (isembedding f).
  Proof.
    apply impred; intros x.
    apply impred; intros y.
    apply isapropisweq.
  Qed.

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
    exact (∑ (p : A = B), ∏ (x : B), IH (transportb _ p x) (ElB x)).
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

  Lemma fib_weq {A B C : UU} (f : A → C) (g : B → C) :
    (∑ (p : A = B), homotsec f (g ∘ (transportf _ p)))
      ≃
    (∏ (c : C), hfiber f c ≃ hfiber g c).
  Proof.
    use tpair.
    - intros [p h] c.
      set (w := weqhfibersgwtog ((transportf _ p ,, isweqtransportf (fun x => x)  p) : A ≃ B) g c).
      refine (weqcomp _ w).
      apply weqhfibershomot.
      auto.
    - simpl.
  Admitted.

  (*   assert ((∏ (c : C), hfiber f c ≃ hfiber (g ∘ transportf _ p) c) ≃ (∏ (c : C), hfiber f c ≃ hfiber g c)) as w1. *)
  (*   rewrite weqhfibershomot *)



  (* Qed. *)

  Definition M_extensional :
    ∏ (m1 m2 : M), m1 = m2 ≃ ∏ (m : M), memberM m m1 ≃ memberM m m2.
  Proof.
    intros m1; induction m1 as [A ElA IH].
    intros m2; induction m2 as [B ElB _].
    apply (weqcomp (M_eq_char _ _)).
    simpl.

    change memberM with hfiber.

  Definition itset (m : M) : hProp.
  Proof.
    induction m as [A El IH].
    refine ((isembedding El × ∏ (a : A), IH a) ,, _).
    apply isapropdirprod;
      [apply isaprop_isembedding | apply impred; apply IH].
  Defined.

  (* The universe of sets *)
  Definition V : UU :=  ∑ (m : M), itset m.

  Definition V_isaset : isaset V.
  Proof.


Definition isembedding {A B : UU} (f : A → B) : UU :=
  ∏ (x y : A), isweq (@maponpaths A B f x y).


Inductive M : UU :=
  sup : ∏ (A : UU) (f : A → M), M.

Definition memberM (x y : M) : UU.
Proof.
destruct y as [a f].
use total2.
- apply a.
- intros i.
  exact (f i = x).
Defined.

Definition itset (x : M) : UU.
Proof.
induction x as [a f H].
apply dirprod.
apply (isembedding f).
apply (∏ (i : a), H i).
Defined.

Lemma isaprop_itset (x : M) : isaprop (itset x).
Proof.
induction x as [a f H]; simpl.
apply isapropdirprod.
- apply isaprop_isembedding.
- apply impred; intro i; apply H.
Qed.

Definition itset_predicate (x : M) : hProp :=
  (itset x,,isaprop_itset x).

Definition V : UU := ∑ (x : M), itset x.

Lemma V_eq (x y : V) : (x = y) ≃ (pr1 x = pr1 y).
Proof.
now apply subtypeInjectivity; intros X; apply isaprop_itset.
Qed.

Lemma isasetV : isaset V.
Admitted.

Lemma asdf (A : UU) (f : A → M) (h : itset (sup A f)) : isaset A.
Proof.
intros x y.
induction h as [h1 h2].
apply (isofhlevelweqb _ (_,,h1 x y)).
exact (isofhlevelweqf 1 (V_eq _ _) (isasetV (f x,,h2 x) (f y,,h2 y))).
Qed.

(* Definition Vprecategory : precategory. *)
(* Proof. *)
(* use mk_precategory. *)
(* - use tpair. *)
(*   + use (V,,_). *)
(*     intros x y. *)
(*     induction (pr1 x) as [a f _]. *)
(*     induction (pr1 y) as [b g _]. *)
(*     apply (a → b). *)
(*   + split; simpl. *)
(*     * intros x. *)
(*       induction (pr1 x) as [a f _]; cbn. *)
(*       apply idfun. *)
(*     * intros x y z. *)
(*       induction (pr1 x) as [a f _]. *)
(*       induction (pr1 y) as [b g _]. *)
(*       induction (pr1 z) as [c h _]; cbn. *)
(*       intros F G w; apply (G (F w)). *)
(* - repeat split; simpl. *)
(*   + intros x y; cbn. *)
(*     now induction (pr1 x); induction (pr1 y). *)
(*   + intros x y; cbn. *)
(*     now induction (pr1 x); induction (pr1 y). *)
(*   + intros x y z w; cbn. *)
(*     induction (pr1 x); induction (pr1 y); induction (pr1 z); induction (pr1 w). *)
(*     now intros; apply funextfun. *)
(* Defined. *)

(* Lemma has_homsets_Vprecategory : has_homsets Vprecategory. *)
(* Proof. *)
(* intros [x1 x2] [y1 y2]. *)
(* cbn. *)
(* induction y1 as [b g _]. *)
(* induction x1 as [a f _]. *)
(* simpl. *)
(* apply impred_isaset; intros x. *)
(* apply (asdf _ g y2). *)
(* Qed. *)

(* Lemma InitialV : Initial Vprecategory. *)
(* Proof. *)
(* use mk_Initial. *)
(* - use tpair. *)
(*   + now apply (sup ∅). *)
(*   + now split; intros x. *)
(* - intros x; cbn. *)
(*   induction (pr1 x); cbn. *)
(*   now apply impred_iscontr. *)
(* Defined. *)

End gylterud_grothendieck_universe.
