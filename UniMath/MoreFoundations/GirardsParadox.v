(* This file provides a direct formalizatoin of Girard's paradox, as explained in Martin-Lof's 1972
"An intuitionistic theory of types". It can serve as a test as to whether the version of Coq being
used is (in the most obvious way) inconsistent. *)

(* This section has an arbitrary type instead of False *)
Section girard.

Variable Flse : Type.

(* an "ordering without infinite descending chains" (wf is for "well-founded") *)
Definition wf (T : Type) := sigT (fun (lt : T -> T -> Type) =>
                                    prod (forall x y z: T, lt x y -> lt y z -> lt x z)
                                         (forall h : (nat -> T),
                                             (forall n : nat, lt (h (S n)) (h n)) -> Flse)).

(* the type of such orderings *)
Definition wfs := sigT wf.

(* the underyling set *)
Definition uset (w : wfs) : Type := projT1 w.
(* the underlying order *)
Definition uord (w : wfs) : uset w -> uset w -> Type := projT1 (projT2 w).
(* the transitivity property *)
Definition trans (w : wfs) {x y z : uset w} := fst (projT2 (projT2 w)) x y z.
(* the well-foundedness property *)
Definition wfp (w : wfs) := snd (projT2 (projT2 w)).

(* the order on wfs: an order-preserving function on underlying sets and an
   element of the second set which dominates the image *)
Definition wfs_wf_uord (v : wfs) (w : wfs) : Type :=
  sigT (fun (f : uset v -> uset w) =>
          prod (forall x y : uset v, (uord v) x y -> (uord w) (f x) (f y))
               (sigT (fun (y : uset w) => forall (x: uset v), (uord w) (f x) y))).

(* the underlying function *)
Definition ufun {v : wfs} {w : wfs} (a : wfs_wf_uord v w) := projT1 a.
(* the homomorpshim property *)
Definition homo {v : wfs} {w : wfs} (a : wfs_wf_uord v w) := fst (projT2 a).
(* the dominating element *)
Definition domi {v : wfs} {w : wfs} (a : wfs_wf_uord v w) := projT1 (snd (projT2 a)).
(* the relation comparing the dominating element to the various images *)
Definition domicom {v : wfs} {w : wfs} (a : wfs_wf_uord v w) := projT2 (snd (projT2 a)).

(* transitivty of the ordering on wfs *)
Definition wfs_wf_trans : forall x y z : wfs, wfs_wf_uord x y -> wfs_wf_uord y z -> wfs_wf_uord x z.
Proof.
  intros x y z.
  intros f g.
  exists (fun a : uset x => (ufun g) ((ufun f) a)).
  split.
  + intros x0 y0.
    intro x0y0.
    exact (homo g _ _ (homo f _ _ x0y0)).
  + exists (domi g).
    intro x0.
    set (y0 := ufun f x0).
    set (ydom := domi f).
    set (co := domicom f x0).
    exact (trans z (homo g _ _ co) (domicom g (domi f))).
Defined.

(* the following three definitions and lemmas are for showing that wfs_wf_uord is well founded *)

(* given a descending sequence f : nat -> wfs, map each f(n) to f(0) by composing all the maps *)

Definition wfs_wf_wfp_shift (f : nat -> wfs) (b : forall n : nat, wfs_wf_uord (f (S n)) (f n)) :
  forall (n : nat), (uset (f n) -> uset (f 0)).
Proof.
  intro n.
  induction n.
  intro a; exact a.
  intro x.
  exact (IHn (ufun (b n) x)).
Defined.

(* thus obtain a sequence in (f 0) *)
Definition wfs_wf_wfp_seq (f : nat -> wfs) (b : forall n : nat, wfs_wf_uord (f (S n)) (f n)) :
  nat -> uset (f 0).
Proof.
  intro n.
  exact (wfs_wf_wfp_shift f b n (domi (b n))).
Defined.

(* obtain comparisons between the shifted elements *)
Definition wfs_wf_wfp_compshift (f : nat -> wfs) (b : forall n : nat, wfs_wf_uord (f (S n)) (f n)) :
  forall (n : nat) {x y : uset (f n)},
    uord (f n) x y -> uord (f 0) (wfs_wf_wfp_shift f b n x) (wfs_wf_wfp_shift f b n y).
Proof.
  intros n.
  induction n.
  intros x y p.
  exact p.
  intros x y p.
  exact (IHn _ _ (homo (b n) x y p)).
Qed.

(* show that the resulting sequence on (f 0) is descending *)
Lemma wfs_wf_wfp_desc (f : nat -> wfs) (b : forall n : nat, wfs_wf_uord (f (S n)) (f n)) :
  forall n : nat, uord (f 0) (wfs_wf_wfp_seq f b (S n)) (wfs_wf_wfp_seq f b n).
Proof.
  intro n.
  exact (wfs_wf_wfp_compshift f b n (domicom (b n) (domi (b (S n))))).
Defined.

(* the wf on wfs *)
Definition wfs_wf : wf wfs.
Proof.
  exists wfs_wf_uord.
  split.
  exact wfs_wf_trans.
  intro h.
  intro b.
  exact (wfp _ (wfs_wf_wfp_seq h b) (wfs_wf_wfp_desc  h b)).
Defined.

(* the wf on wfs as an element of wfs *)
Definition wfs_wf_t : wfs := existT (fun T => wf T) wfs (wfs_wf).

(* this definition and the following three lemmas show that wfs_wf has a maximal element *)

(* function mapping each wf to the set of wfs (by taking inital segments) *)
Definition maxi_fun (w : wfs) : uset w -> wfs.
Proof.
  intro x.
  exists (sigT (fun y : uset w => uord w y x)).
  exists (fun a b => uord w (projT1 a) (projT1 b)).
  split.
  - intros x0 y z p q.
    exact (trans w p q).
  - intro h.
    intro b.
    exact (wfp w (fun n => projT1 (h n)) b).
Defined.

(* maxi_fun preserves the order *)
Lemma maxi_homo (w : wfs) : forall (x y : uset w),
    uord w x y -> wfs_wf_uord (maxi_fun w x) (maxi_fun w y).
Proof.
  intros x y p.
  exists (fun (z : uset (maxi_fun w x)) => existT _ (projT1 z) (trans w (projT2 z) p)).
  split.
  - intros x0 y0 q.
    exact q.
  - exists (existT _ x p).
    intro x0.
    exact (projT2 x0).
Defined.

(* w itself dominates the image of w under maxi_fun *)
Lemma maxidom (w : wfs) : forall (x : uset w), wfs_wf_uord (maxi_fun w x) w.
Proof.
  intro x.
  exists (fun (z : uset (maxi_fun w x)) => projT1 z).
  split.
  - intros x0 y p.
    exact p.
  - exists x.
    intro x0.
    exact (projT2 x0).
Defined.

(* wfs_wf_t is maximal with respect to wfs_wf *)
Lemma maxi (w : wfs) : wfs_wf_uord w wfs_wf_t.
Proof.
  exists (maxi_fun w).
  split.
  - exact (maxi_homo w).
  - exact (existT _ _ (maxidom w)).
Defined.

(* in particular wfs_wf_t is greather than itself *)
Proposition whoa : uord wfs_wf_t wfs_wf_t wfs_wf_t.
Proof.
  apply maxi.
Defined.

(* but wfs are irreflexive *)
Proposition irref (w : wfs) : forall (x : uset w), (uord w) x x -> Flse.
Proof.
  intro x.
  intro p.
  exact (wfp w (fun n => x) (fun n => p)).
Defined.

(* therefore the world explodes *)
Proposition the_world_explodes : Flse.
Proof.
  exact (irref wfs_wf_t wfs_wf_t whoa).
Defined.

End girard.

(* especially if Flse=False *)
Proposition but_seriously_the_world_explodes : False.
  exact (the_world_explodes False).
Defined.
