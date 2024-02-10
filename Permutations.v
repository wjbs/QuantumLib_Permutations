Require Import VectorStates.

(** Facts about permutations and matrices that implement them. *)

Local Open Scope nat_scope.

(** * Permutations on (0,...,n-1) *)
Definition permutation (n : nat) (f : nat -> nat) :=
  exists g, forall x, x < n -> (f x < n /\ g x < n /\ g (f x) = x /\ f (g x) = x).

Lemma permutation_is_injective : forall n f,
  permutation n f -> 
  forall x y, x < n -> y < n -> f x = f y -> x = y.
Proof.
  intros n f [g Hbij] x y Hx Hy H.
  destruct (Hbij x Hx) as [_ [_ [H0 _]]].
  destruct (Hbij y Hy) as [_ [_ [H1 _]]].
  rewrite <- H0. 
  rewrite <- H1.
  rewrite H.
  reflexivity.
Qed.

Lemma permutation_is_surjective : forall n f,
  permutation n f ->
  forall k, k < n -> exists k', k' < n /\ f k' = k.
Proof.
  intros n f Hf k Hk.
  destruct Hf as [finv Hfinv].
  specialize (Hfinv k Hk).
  exists (finv k).
  intuition.
Qed.

Lemma permutation_compose : forall n f g,
  permutation n f ->
  permutation n g ->
  permutation n (f ∘ g)%prg.
Proof.
  intros n f g [finv Hfbij] [ginv Hgbij].
  exists (ginv ∘ finv)%prg.
  unfold compose.
  intros x Hx.
  destruct (Hgbij x) as [? [_ [? _]]]; auto.
  destruct (Hfbij (g x)) as [? [_ [Hinv1 _]]]; auto.
  destruct (Hfbij x) as [_ [? [_ ?]]]; auto.
  destruct (Hgbij (finv x)) as [_ [? [_ Hinv2]]]; auto.
  repeat split; auto.
  rewrite Hinv1. 
  assumption.
  rewrite Hinv2. 
  assumption.
Qed.

(** The identity permutation (on any 0..n-1) *)
Local Notation idn := (fun (k : nat) => k).

Lemma compose_idn_l : forall {T} (f: T -> nat), (idn ∘ f = f)%prg.
Proof.
  intros.
	unfold compose.
	apply functional_extensionality; easy.
Qed.

Lemma compose_idn_r : forall {T} (f: nat -> T), (f ∘ idn = f)%prg.
Proof.
  intros.
  unfold compose.
	apply functional_extensionality; easy.
Qed.

Lemma idn_permutation : forall n, permutation n idn.
Proof.
  intros. 
  exists idn.
  easy. 
Qed.

(** Notions of injectivity, boundedness, and surjectivity of f : nat -> nat 
  (interpreted as a function from [n]_0 to [n]_0) and their equivalences *)
Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bdd  n f := (forall k, k < n -> f k < n).
Local Notation perm_inj  n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).

Lemma fswap_injective_if_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f -> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy Hinj k l Hk Hl.
  unfold fswap.
  bdestruct (k =? x); bdestruct (k =? y);
  bdestruct (l =? x); bdestruct (l =? y);
  subst; auto using Hinj.
  all: intros Heq;
    epose proof (Hinj _ _ _ _ Heq); 
    exfalso; lia.
  Unshelve.
  all: assumption.
Qed.

Lemma fswap_injective_iff_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f <-> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy.
  split.
  - apply fswap_injective_if_injective; easy.
  - intros Hinj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_injective_if_injective; easy.
Qed.

Lemma fswap_surjective_if_surjective : forall n f x y, 
  x < n -> y < n -> 
  perm_surj n f -> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hsurj k Hk.
  destruct (Hsurj k Hk) as [k' [Hk' Hfk']].
  bdestruct (k' =? x); [|bdestruct (k' =? y)].
  - exists y.
    split; [assumption|].
    subst.
    rewrite fswap_simpl2.
    easy.
  - exists x.
    split; [assumption|].
    subst.
    rewrite fswap_simpl1.
    easy.
  - exists k'.
    split; [assumption|].
    rewrite fswap_neq; lia.
Qed.

Lemma fswap_surjective_iff_surjective : forall n f x y,
  x < n -> y < n ->
  perm_surj n f <-> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_surjective_if_surjective; easy.
  - intros Hsurj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_surjective_if_surjective; easy.
Qed.

Lemma fswap_bounded_if_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f -> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hbdd k Hk.
  unfold fswap.
  bdestruct_all;
  apply Hbdd; 
  easy.
Qed.

Lemma fswap_bounded_iff_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f <-> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_bounded_if_bounded; easy.
  - intros Hbdd.
    rewrite <- (fswap_involutive f x y).
    apply fswap_bounded_if_bounded; easy.
Qed.

Lemma surjective_of_eq_boundary_shrink : forall n f,
  perm_surj (S n) f -> f n = n -> perm_surj n f.
Proof.
  intros n f Hsurj Hfn k Hk.
  assert (HkS : k < S n) by lia.
  destruct (Hsurj k HkS) as [k' [Hk' Hfk']].
  bdestruct (k' =? n).
  - exfalso; subst; lia.
  - exists k'.
    split; [lia | assumption].
Qed.

Lemma surjective_of_eq_boundary_grow : forall n f,
  perm_surj n f -> f n = n -> perm_surj (S n) f.
Proof.
  intros n f Hsurj Hfn k Hk.
  bdestruct (k =? n).
  - exists n; lia.
  - assert (H'k : k < n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    exists k'; lia.
Qed.

Lemma fswap_at_boundary_surjective : forall n f n',
  n' < S n -> perm_surj (S n) f -> f n' = n -> 
  perm_surj n (fswap f n' n).
Proof.
  intros n f n' Hn' Hsurj Hfn' k Hk.
  bdestruct (k =? f n).
  - exists n'.
    split.
    + assert (Hneq: n' <> n); [|lia].
      intros Hfalse.
      rewrite Hfalse in Hfn'.
      rewrite Hfn' in H.
      lia.
    + rewrite fswap_simpl1; easy.
  - assert (H'k : k < S n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    assert (Hk'n: k' <> n) by (intros Hfalse; subst; lia).
    assert (Hk'n': k' <> n') by (intros Hfalse; subst; lia).
    exists k'.
    split; [lia|].
    rewrite fswap_neq; lia.
Qed.

Lemma injective_monotone : forall {A} n (f : nat -> A) m, 
  m < n -> perm_inj n f -> perm_inj m f.
Proof.
  intros A n f m Hmn Hinj k l Hk Hl Hfkl.
  apply Hinj; auto; lia.
Qed.

Lemma injective_and_bounded_grow_of_boundary : forall n f,
  perm_inj n f /\ perm_bdd n f -> f n = n ->
  perm_inj (S n) f /\ perm_bdd (S n) f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - intros k l Hk Hl Hfkl.
    bdestruct (k =? n).
    + subst.
      bdestruct (l =? n); [easy|].
      assert (H'l : l < n) by lia.
      specialize (Hbdd _ H'l).
      lia.
    + assert (H'k : k < n) by lia.
      bdestruct (l =? n).
      * specialize (Hbdd _ H'k). 
        subst. lia.
      * assert (H'l : l < n) by lia.
        apply Hinj; easy.
  - intros k Hk.
    bdestruct (k <? n).
    + specialize (Hbdd _ H). lia.
    + replace k with n by lia.
      lia.
Qed.

Lemma injective_and_bounded_of_surjective : forall n f,
  perm_surj n f -> perm_inj n f /\ perm_bdd n f.
Proof.
  intros n.
  induction n; [easy|].
  intros f Hsurj.
  assert (HnS : n < S n) by lia.
  destruct (Hsurj n HnS) as [n' [Hn' Hfn']].
  pose proof (fswap_at_boundary_surjective _ _ _ Hn' Hsurj Hfn') as Hswap_surj.
  specialize (IHn (fswap f n' n) Hswap_surj).
  rewrite (fswap_injective_iff_injective _ f n' n); [|easy|easy].
  rewrite (fswap_bounded_iff_bounded _ f n' n); [|easy|easy].
  apply injective_and_bounded_grow_of_boundary;
  [| rewrite fswap_simpl2; easy].
  easy.
Qed.

Lemma injective_and_bounded_shrink_of_boundary : forall n f,
  perm_inj (S n) f /\ perm_bdd (S n) f -> f n = n -> 
  perm_inj n f /\ perm_bdd n f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - eapply injective_monotone, Hinj; lia.
  - intros k Hk.
    assert (H'k : k < S n) by lia.
    specialize (Hbdd k H'k).
    bdestruct (f k =? n).
    + rewrite <- Hfn in H.
      assert (HnS : n < S n) by lia.
      specialize (Hinj _ _ H'k HnS H).
      lia.
    + lia.
Qed.

(* Formalization of proof sketch of pigeonhole principle
   from https://math.stackexchange.com/a/910790 *)
Lemma exists_bounded_decidable : forall n P,
  (forall k, k < n -> {P k} + {~ P k}) ->
  {exists j, j < n /\ P j} + {~ exists j, j < n /\ P j}.
Proof.
  intros n P HPdec.
  induction n.
  - right; intros [x [Hlt0 _]]; inversion Hlt0.
  - destruct (HPdec n) as [HPn | HnPn]; [lia| |].
    + left. exists n; split; [lia | assumption].
    + destruct IHn as [Hex | Hnex].
      * intros k Hk; apply HPdec; lia.
      * left. 
        destruct Hex as [j [Hjn HPj]].
        exists j; split; [lia | assumption].
      * right.
        intros [j [Hjn HPj]].
        apply Hnex.
        bdestruct (j =? n).
        -- exfalso; apply HnPn; subst; easy.
        -- exists j; split; [lia | easy].
Qed.

Lemma has_preimage_decidable : forall n f, 
  forall k, k < n ->
  {exists j, j < n /\ f j = k} + {~exists j, j < n /\ f j = k}.
Proof.
  intros n f k Hk.
  apply exists_bounded_decidable.
  intros k' Hk'.
  bdestruct (f k' =? k).
  - left; easy.
  - right; easy.
Qed.

Lemma pigeonhole_S : forall n f, 
  (forall i, i < S n -> f i < n) ->
  exists i j, i < S n /\ j < i /\ f i = f j.
Proof.
  intros n.
  destruct n;
    [intros f Hbdd; specialize (Hbdd 0); lia|].
  induction n; intros f Hbdd.
  (* Base case: *)
  1: {
    exists 1, 0.
    pose (Hbdd 0).
    pose (Hbdd 1). 
    lia.
  }
  destruct (has_preimage_decidable (S (S n)) f (f (S (S n)))) as [Hex | Hnex].
  - apply Hbdd; lia.
  - destruct Hex as [j [Hj Hfj]].
    exists (S (S n)), j.
    repeat split; lia.
  - destruct (IHn (fun k => if f k <? f (S (S n)) then f k else f k - 1)) as
      [i [j [Hi [Hj Hgij]]]].
    + intros i Hi.
      bdestruct (f i <? f (S (S n))).
      * specialize (Hbdd (S (S n))).
        lia.
      * specialize (Hbdd i).
        lia.
    + exists i, j.
      repeat (split; [lia|]).
      assert (Hnex': forall k, k < S (S n) -> f k >= f (S (S n)) -> f k > f (S (S n))). 1:{
        intros k Hk Hge.
        bdestruct (f k =? f (S (S n))).
        - exfalso; apply Hnex; exists k; split; lia.
        - lia.
      }
      bdestruct (f i <? f (S (S n)));
      bdestruct (f j <? f (S (S n)));
      try easy.
      * specialize (Hnex' j); lia.
      * specialize (Hnex' i); lia.
      * pose (Hnex' j).
        pose (Hnex' i Hi H).
        lia.
Qed.

Lemma n_has_preimage_of_injective_and_bounded : forall n f,
  perm_inj (S n) f /\ perm_bdd (S n) f -> exists k, k < S n /\ f k = n.
Proof. 
  intros n f [Hinj Hbdd].
  destruct (has_preimage_decidable (S n) f n) as [Hex | Hnex]; 
    [lia | assumption |].
  (* Now, contradict injectivity using pigeonhole principle *)
  exfalso.
  assert (Hbdd': forall j, j < S n -> f j < n). 1:{
    intros j Hj.
    specialize (Hbdd j Hj).
    bdestruct (f j =? n).
    - exfalso; apply Hnex; exists j; easy.
    - lia.
  }
  destruct (pigeonhole_S n f Hbdd') as [i [j [Hi [Hj Heq]]]].
  absurd (i = j).
  - lia.
  - apply Hinj; lia.
Qed.

Lemma surjective_of_injective_and_bounded : forall n f,
  perm_inj n f /\ perm_bdd n f -> perm_surj n f.
Proof. 
  induction n; [easy|].
  intros f Hinj_bdd.
  destruct (n_has_preimage_of_injective_and_bounded n f Hinj_bdd) as [n' [Hn' Hfn']].
  rewrite (fswap_injective_iff_injective _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_bounded_iff_bounded _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_surjective_iff_surjective _ _ n n');
    [|lia|easy].
  intros k Hk.
  bdestruct (k =? n).
  - exists n.
    split; [lia|].
    rewrite fswap_simpl1; subst; easy.
  - pose proof (injective_and_bounded_shrink_of_boundary n _ Hinj_bdd) as Hinj_bdd'.
    rewrite fswap_simpl1 in Hinj_bdd'.
    specialize (Hinj_bdd' Hfn').
    destruct (IHn (fswap f n n') Hinj_bdd' k) as [k' [Hk' Hfk']]; [lia|].
    exists k'.
    split; [lia|assumption].
Qed.


(** Explicit inverse of a permutation *)
Fixpoint perm_inv n f k : nat :=
  match n with
  | 0 => 0%nat
  | S n' => if f n' =? k then n'%nat else perm_inv n' f k
  end.

Lemma perm_inv_bounded_S : forall n f k,
  perm_inv (S n) f k < S n.
Proof.
  intros n f k. 
  induction n; simpl.
  - bdestructΩ (f 0 =? k).
  - bdestruct (f (S n) =? k); [|transitivity (S n); [apply IHn|]]. 
  all: apply Nat.lt_succ_diag_r.
Qed.

Lemma perm_inv_bounded : forall n f,
  perm_bdd n (perm_inv n f).
Proof.
  induction n.
  - easy.
  - intros.
    apply perm_inv_bounded_S.
Qed.

Lemma perm_inv_is_linv_of_injective : forall n f, 
  perm_inj n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros n f Hinj k Hk.
  induction n.
  - easy.
  - simpl.
    bdestruct (f n =? f k).
    + apply Hinj; lia.
    + assert (k <> n) by (intros Heq; subst; easy).
      apply IHn; [auto|].
      assert (k <> n) by (intros Heq; subst; easy).
      lia.
Qed.

Lemma perm_inv_is_rinv_of_surjective' : forall n f k,
  (exists l, l < n /\ f l = k) ->
  f (perm_inv n f k) = k.
Proof.
  intros n f k.
  induction n.
  - intros []; easy.
  - intros [l [Hl Hfl]].
    simpl.
    bdestruct (f n =? k); [easy|].
    apply IHn.
    exists l.
    split; [|easy].
    bdestruct (l =? n); [subst; easy|].
    lia.
Qed.

Lemma perm_inv_is_rinv_of_surjective : forall n f,
  perm_surj n f -> forall k, k < n -> 
  f (perm_inv n f k) = k.
Proof.
  intros n f Hsurj k Hk.
  apply perm_inv_is_rinv_of_surjective', Hsurj, Hk.
Qed.

Lemma perm_inv_is_linv_of_permutation : forall n f,
  permutation n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros n f Hperm.
  apply perm_inv_is_linv_of_injective, permutation_is_injective, Hperm.
Qed.

Lemma perm_inv_is_rinv_of_permutation : forall n f,
  permutation n f ->
  forall k, k < n -> f (perm_inv n f k) = k.
Proof.
  intros n f Hperm k Hk.
  apply perm_inv_is_rinv_of_surjective', (permutation_is_surjective _ _ Hperm _ Hk).
Qed.

Lemma perm_inv_is_inv_of_surjective_injective_bounded : forall n f,
  perm_surj n f -> perm_inj n f -> perm_bdd n f ->
  (forall k, k < n -> 
    f k < n /\ perm_inv n f k < n /\ perm_inv n f (f k) = k /\ f (perm_inv n f k) = k).
Proof.
  intros n f Hsurj Hinj Hbdd.
  intros k Hk; repeat split.
  - apply Hbdd, Hk.
  - apply perm_inv_bounded, Hk.
  - rewrite perm_inv_is_linv_of_injective; easy.
  - rewrite perm_inv_is_rinv_of_surjective'; [easy|].
    apply Hsurj; easy.
Qed.

Lemma permutation_iff_surjective : forall n f, 
  permutation n f <-> perm_surj n f.
Proof.
  split.
  - apply permutation_is_surjective.
  - intros Hsurj.
    exists (perm_inv n f).
    pose proof (injective_and_bounded_of_surjective n f Hsurj).
    apply perm_inv_is_inv_of_surjective_injective_bounded; easy.
Qed.

Lemma fswap_at_boundary_permutation : forall n f x,
  permutation (S n) f ->
  (x < S n)%nat -> f x = n ->
  permutation n (fswap f x n).
Proof.
  intros n f x.
  rewrite 2!permutation_iff_surjective.
  intros HsurjSn Hx Hfx.
  apply fswap_at_boundary_surjective; easy.
Qed.


(** Well-foundedness of permutations; f k = k for k not in [n]_0 *)
Definition WF_Perm (n : nat) (f : nat -> nat) := 
  forall k, n <= k -> f k = k.


Lemma monotonic_WF_Perm n m f : WF_Perm n f -> n <= m ->
  WF_Perm m f.
Proof.
  intros HWF Hnm k Hk.
  apply HWF; lia.
Qed.

Lemma compose_WF_Perm n f g : WF_Perm n f -> WF_Perm n g -> 
  WF_Perm n (f ∘ g)%prg.
Proof.
  unfold compose.
  intros Hf Hg k Hk.
  rewrite Hg, Hf; easy.
Qed.

Lemma linv_WF_of_WF {n} {f finv}
	(HfWF : WF_Perm n f) (Hinv : (finv ∘ f = idn)%prg) :
	WF_Perm n finv.
Proof.
	intros k Hk.
	rewrite <- (HfWF k Hk).
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv.
	rewrite Hinv, (HfWF k Hk).
	easy.
Qed.

Lemma bdd_of_WF_linv {n} {f finv}  
  (HWF: WF_Perm n f) (Hinv : (finv ∘ f = idn)%prg) : 
  perm_bdd n f.
Proof.
  intros k Hk.
  pose proof (linv_WF_of_WF HWF Hinv) as HWFinv.
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv. 
  bdestruct (f k <? n); [easy|].
  specialize (HWFinv (f k) H).
  lia.
Qed.

Lemma rinv_bdd_of_WF {n} {f finv} (Hinv : (f ∘ finv = idn)%prg)
  (HWF : WF_Perm n f) :
  perm_bdd n finv.
Proof.
  intros k Hk.
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv.
  bdestruct (finv k <? n).
  - easy.
  - specialize (HWF _ H).
    lia.
Qed.

Lemma WF_permutation_inverse_injective (f : nat->nat) (n:nat) {finv finv'}
  (Hf: permutation n f) (HfWF : WF_Perm n f)
  (Hfinv : (finv ∘ f = idn)%prg) (Hfinv' : (finv' ∘ f = idn)%prg) :
  finv = finv'.
Proof.
	apply functional_extensionality; intros k.
	pose proof (linv_WF_of_WF HfWF Hfinv) as HfinvWF.
	pose proof (linv_WF_of_WF HfWF Hfinv') as Hfinv'WF.
	bdestruct (n <=? k).
	- rewrite HfinvWF, Hfinv'WF; easy.
	- destruct Hf as [fi Hfi].
	  specialize (Hfi k H).
    unfold compose in Hfinv, Hfinv'.
	  apply (f_equal_inv (fi k)) in Hfinv, Hfinv'. 
	  replace (f (fi k)) with k in * by easy.
	  rewrite Hfinv, Hfinv'.
	  easy.
Qed.

Lemma permutation_monotonic_of_WF f m n : (m <= n)%nat -> 
  permutation m f -> WF_Perm m f -> 
  permutation n f.
Proof.
  intros Hmn [finv_m Hfinv_m] HWF.
  exists (fun k => if m <=? k then k else finv_m k).
  intros k Hk.
  bdestruct (m <=? k).
  - rewrite HWF; bdestruct_all; auto.
  - specialize (Hfinv_m _ H).
    repeat split; bdestruct_all; try easy; lia.
Qed.

(** vsum terms can be arbitrarily reordered *)
Lemma vsum_reorder : forall {d} n (v : nat -> Vector d) f,
  permutation n f ->
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [g Hg].
  destruct (Hg n) as [_ [H1 [_ H2]]]; try lia.
  rewrite (vsum_eq_up_to_fswap _ f _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  rewrite H2.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn.
  reflexivity.
  apply fswap_at_boundary_permutation; auto.
  exists g. auto.
Qed.

(** * Permutation matrices *)

Definition perm_mat n (p : nat -> nat) : Square n :=
  (fun x y => if (x =? p y) && (x <? n) && (y <? n) then C1 else C0).

Lemma perm_mat_WF : forall n p, WF_Matrix (perm_mat n p).
Proof.
  intros n p.
  unfold WF_Matrix, perm_mat. 
  intros x y [H | H].
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
Qed. 
#[export] Hint Resolve perm_mat_WF : wf_db.

Lemma perm_mat_unitary : forall n p, 
  permutation n p -> WF_Unitary (perm_mat n p).
Proof.
  intros n p [pinv Hp].
  split.
  apply perm_mat_WF.
  unfold Mmult, adjoint, perm_mat, I.
  prep_matrix_equality.
  destruct ((x =? y) && (x <? n)) eqn:H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  subst.
  apply big_sum_unique.
  exists (p y).
  destruct (Hp y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.  
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite andb_true_r in H.
  apply Nat.eqb_neq in H.
  assert (pinv (p x) = pinv (p y)) by auto.
  destruct (Hp x) as [_ [_ [H5 _]]]; auto.
  destruct (Hp y) as [_ [_ [H6 _]]]; auto.
  contradict H.
  rewrite <- H5, <- H6.
  assumption.
Qed.

Lemma perm_mat_Mmult : forall n f g,
  permutation n g ->
  perm_mat n f × perm_mat n g = perm_mat n (f ∘ g)%prg.
Proof.
  intros n f g [ginv Hgbij].
  unfold perm_mat, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? f (g y)) && (x <? n) && (y <? n)) eqn:H.
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt in H3.
  subst.
  apply big_sum_unique.
  exists (g y).
  destruct (Hgbij y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite 2 andb_true_r in H.
  apply Nat.eqb_neq in H.
  contradiction.
Qed.

Lemma perm_mat_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_mat n f = I n.
Proof.
  intros n f Hinv.
  unfold perm_mat, I.
  prep_matrix_equality.
  bdestruct_all; simpl; try lca.
  rewrite Hinv in H1 by assumption.
  contradiction.
  rewrite Hinv in H1 by assumption.
  contradiction.
Qed.

(** Given a permutation p over n qubits, construct a permutation over 2^n indices. *)
Definition qubit_perm_to_nat_perm n (p : nat -> nat) :=
  fun x:nat => funbool_to_nat n ((nat_to_funbool n x) ∘ p)%prg.

Lemma qubit_perm_to_nat_perm_bij : forall n p,
  permutation n p -> permutation (2^n) (qubit_perm_to_nat_perm n p).
Proof.
  intros n p [pinv Hp].
  unfold qubit_perm_to_nat_perm.
  exists (fun x => funbool_to_nat n ((nat_to_funbool n x) ∘ pinv)%prg).
  intros x Hx.
  repeat split.
  apply funbool_to_nat_bound.
  apply funbool_to_nat_bound.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [_ H]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [_ [? _]]; auto. }
  rewrite nat_to_funbool_inverse; auto.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [H _]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [? _]; auto. }
  rewrite nat_to_funbool_inverse; auto.
Qed.  

(** Transform a (0,...,n-1) permutation into a 2^n by 2^n matrix. *)
Definition perm_to_matrix n p :=
  perm_mat (2 ^ n) (qubit_perm_to_nat_perm n p).
 
Lemma perm_to_matrix_permutes_qubits : forall n p f, 
  permutation n p ->
  perm_to_matrix n p × f_to_vec n f = f_to_vec n (fun x => f (p x)).
Proof.
  intros n p f [pinv Hp].
  rewrite 2 basis_f_to_vec.
  unfold perm_to_matrix, perm_mat, qubit_perm_to_nat_perm.
  unfold basis_vector, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? funbool_to_nat n (fun x0 : nat => f (p x0))) && (y =? 0)) eqn:H.
  apply andb_prop in H as [H1 H2].
  rewrite Nat.eqb_eq in H1.
  rewrite Nat.eqb_eq in H2.
  apply big_sum_unique.
  exists (funbool_to_nat n f).
  split.
  apply funbool_to_nat_bound.
  split.
  erewrite funbool_to_nat_eq.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  specialize (funbool_to_nat_bound n f) as ?.
  specialize (funbool_to_nat_bound n (fun x0 : nat => f (p x0))) as ?.
  bdestruct_all; lca.
  intros z Hz H3.
  bdestructΩ (z =? funbool_to_nat n f).
  lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  rewrite andb_true_r in H.
  apply Nat.eqb_neq in H.
  subst z.
  erewrite funbool_to_nat_eq in H2.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  contradiction.
Qed.

Lemma perm_to_matrix_unitary : forall n p, 
  permutation n p ->
  WF_Unitary (perm_to_matrix n p).
Proof.
  intros.
  apply perm_mat_unitary.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma qubit_perm_to_nat_perm_compose : forall n f g,
  permutation n f ->
  (qubit_perm_to_nat_perm n f ∘ qubit_perm_to_nat_perm n g = 
    qubit_perm_to_nat_perm n (g ∘ f))%prg.
Proof.
  intros n f g [finv Hbij].
  unfold qubit_perm_to_nat_perm, compose.
  apply functional_extensionality.
  intro x.
  apply funbool_to_nat_eq.
  intros y Hy.
  rewrite funbool_to_nat_inverse.
  reflexivity.
  destruct (Hbij y) as [? _]; auto.
Qed.

Lemma perm_to_matrix_Mmult : forall n f g,
  permutation n f ->
  permutation n g ->
  perm_to_matrix n f × perm_to_matrix n g = perm_to_matrix n (g ∘ f)%prg.
Proof.
  intros. 
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult.
  rewrite qubit_perm_to_nat_perm_compose by assumption.
  reflexivity.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma perm_to_matrix_I : forall n f,
  permutation n f ->
  (forall x, x < n -> f x = x) ->
  perm_to_matrix n f = I (2 ^ n).
Proof.
  intros n f g Hbij. 
  unfold perm_to_matrix.
  apply perm_mat_I.
  intros x Hx.
  unfold qubit_perm_to_nat_perm, compose. 
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. rewrite Hbij by assumption. reflexivity. }
  apply nat_to_funbool_inverse.
  assumption.
Qed.

Lemma perm_to_matrix_WF : forall n p, WF_Matrix (perm_to_matrix n p).
Proof. intros. apply perm_mat_WF. Qed. 
#[export] Hint Resolve perm_to_matrix_WF : wf_db.
