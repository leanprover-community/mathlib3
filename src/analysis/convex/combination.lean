/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov
-/
import algebra.big_operators.order
import analysis.convex.hull
import linear_algebra.affine_space.basis

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `finset.center_mass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `finset.center_mass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/

open set function
open_locale big_operators classical pointwise

universes u u'
variables {R E F ι ι' : Type*} [linear_ordered_field R] [add_comm_group E] [add_comm_group F]
  [module R E] [module R F] {s : set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def finset.center_mass (t : finset ι) (w : ι → R) (z : ι → E) : E :=
(∑ i in t, w i)⁻¹ • (∑ i in t, w i • z i)

variables (i j : ι) (c : R) (t : finset ι) (w : ι → R) (z : ι → E)

open finset

lemma finset.center_mass_empty : (∅ : finset ι).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : finset ι).center_mass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

lemma finset.center_mass_insert (ha : i ∉ t) (hw : ∑ j in t, w j ≠ 0) :
  (insert i t).center_mass w z = (w i / (w i + ∑ j in t, w j)) • z i +
    ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul],
  congr' 2,
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]
end

lemma finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : finset ι).center_mass w z = z i :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
  t.center_mass w z = ∑ i in t, w i • z i :=
by simp only [finset.center_mass, hw, inv_one, one_smul]

lemma finset.center_mass_smul : t.center_mass w (λ i, c • z i) = c • t.center_mass w z :=
by simp only [finset.center_mass, finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma finset.center_mass_segment'
  (s : finset ι) (t : finset ι') (ws : ι → R) (zs : ι → E) (wt : ι' → R) (zt : ι' → E)
  (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : R) (hab : a + b = 1) :
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.disj_sum t).center_mass (sum.elim (λ i, a * ws i) (λ j, b * wt j)) (sum.elim zs zt) :=
begin
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt,
    smul_sum, smul_sum, ← finset.sum_sum_elim, finset.center_mass_eq_of_sum_1],
  { congr' with ⟨⟩; simp only [sum.elim_inl, sum.elim_inr, mul_smul] },
  { rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma finset.center_mass_segment
  (s : finset ι) (w₁ w₂ : ι → R) (z : ι → E)
  (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : R) (hab : a + b = 1) :
  a • s.center_mass w₁ z + b • s.center_mass w₂ z =
    s.center_mass (λ i, a * w₁ i + b * w₂ i) z :=
have hw : ∑ i in s, (a * w₁ i + b * w₂ i) = 1,
  by simp only [mul_sum.symm, sum_add_distrib, mul_one, *],
by simp only [finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

lemma finset.center_mass_ite_eq (hi : i ∈ t) :
  t.center_mass (λ j, if (i = j) then (1 : R) else 0) z = z i :=
begin
  rw [finset.center_mass_eq_of_sum_1],
  transitivity ∑ j in t, if (i = j) then z i else 0,
  { congr' with i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {t w}

lemma finset.center_mass_subset {t' : finset ι} (ht : t ⊆ t')
  (h : ∀ i ∈ t', i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
begin
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum],
  apply sum_subset ht,
  assume i hit' hit,
  rw [h i hit' hit, zero_smul, smul_zero]
end

lemma finset.center_mass_filter_ne_zero :
  (t.filter (λ i, w i ≠ 0)).center_mass w z = t.center_mass w z :=
finset.center_mass_subset z (filter_subset _ _) $ λ i hit hit',
  by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem (hs : convex R s) :
  (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.center_mass w z ∈ s :=
begin
  induction t using finset.induction with i t hi ht, { simp [lt_irrefl] },
  intros h₀ hpos hmem,
  have zi : z i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at hpos,
  by_cases hsum_t : ∑ j in t, w j = 0,
  { have ws : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wz : ∑ j in t, w j • z j = 0, from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zero],
    simp only [hsum_t, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact zi },
  { rw [finset.center_mass_insert _ _ _ hi hsum_t],
    refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

/-- A version of `convex.sum_mem` for `finsum`s. If `s` is a convex set, `w : ι → R` is a family of
nonnegative weights with sum one and `z : ι → E` is a family of elements of a module over `R` such
that `z i ∈ s` whenever `w i ≠ 0``, then the sum `∑ᶠ i, w i • z i` belongs to `s`. See also
`partition_of_unity.finsum_smul_mem_convex`. -/
lemma convex.finsum_mem {ι : Sort*} {w : ι → R} {z : ι → E} {s : set E}
  (hs : convex R s) (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ᶠ i, w i = 1) (hz : ∀ i, w i ≠ 0 → z i ∈ s) :
  ∑ᶠ i, w i • z i ∈ s :=
begin
  have hfin_w : (support (w ∘ plift.down)).finite,
  { by_contra H,
    rw [finsum, dif_neg H] at h₁,
    exact zero_ne_one h₁ },
  have hsub : support ((λ i, w i • z i) ∘ plift.down) ⊆ hfin_w.to_finset,
    from (support_smul_subset_left _ _).trans hfin_w.coe_to_finset.ge,
  rw [finsum_eq_sum_plift_of_support_subset hsub],
  refine hs.sum_mem (λ _ _, h₀ _) _ (λ i hi, hz _ _),
  { rwa [finsum, dif_pos hfin_w] at h₁ },
  { rwa [hfin_w.mem_to_finset] at hi }
end

lemma convex_iff_sum_mem :
  convex R s ↔
    (∀ (t : finset E) (w : E → R),
      (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → ∑ x in t, w x • x ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x hx y hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull R s :=
(convex_convex_hull R s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull R s $ hz i hi)

/-- A refinement of `finset.center_mass_mem_convex_hull` when the indexed family is a `finset` of
the space. -/
lemma finset.center_mass_id_mem_convex_hull (t : finset E) {w : E → R} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) :
  t.center_mass w id ∈ convex_hull R (t : set E) :=
t.center_mass_mem_convex_hull hw₀ hws (λ i, mem_coe.2)

lemma affine_combination_eq_center_mass {ι : Type*} {t : finset ι} {p : ι → E} {w : ι → R}
  (hw₂ : ∑ i in t, w i = 1) :
  affine_combination t p w = center_mass t w p :=
begin
  rw [affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
    finset.weighted_vsub_of_point_apply, vadd_eq_add, add_zero, t.center_mass_eq_of_sum_1 _ hw₂],
  simp_rw [vsub_eq_sub, sub_zero],
end

lemma affine_combination_mem_convex_hull
  {s : finset ι} {v : ι → E} {w : ι → R} (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1) :
  s.affine_combination v w ∈ convex_hull R (range v) :=
begin
  rw affine_combination_eq_center_mass hw₁,
  apply s.center_mass_mem_convex_hull hw₀,
  { simp [hw₁], },
  { simp, },
end

/-- The centroid can be regarded as a center of mass. -/
@[simp] lemma finset.centroid_eq_center_mass (s : finset ι) (hs : s.nonempty) (p : ι → E) :
  s.centroid R p = s.center_mass (s.centroid_weights R) p :=
affine_combination_eq_center_mass (s.sum_centroid_weights_eq_one_of_nonempty R hs)

lemma finset.centroid_mem_convex_hull (s : finset E) (hs : s.nonempty) :
  s.centroid R id ∈ convex_hull R (s : set E) :=
begin
  rw s.centroid_eq_center_mass hs,
  apply s.center_mass_id_mem_convex_hull,
  { simp only [inv_nonneg, implies_true_iff, nat.cast_nonneg, finset.centroid_weights_apply], },
  { have hs_card : (s.card : R) ≠ 0, { simp [finset.nonempty_iff_ne_empty.mp hs] },
    simp only [hs_card, finset.sum_const, nsmul_eq_mul, mul_inv_cancel, ne.def, not_false_iff,
      finset.centroid_weights_apply, zero_lt_one] }
end

lemma convex_hull_range_eq_exists_affine_combination (v : ι → E) :
  convex_hull R (range v) = { x | ∃ (s : finset ι) (w : ι → R)
    (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : s.sum w = 1), s.affine_combination v w = x } :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    obtain ⟨i, hi⟩ := set.mem_range.mp hx,
    refine ⟨{i}, function.const ι (1 : R), by simp, by simp, by simp [hi]⟩, },
  { rintro x ⟨s, w, hw₀, hw₁, rfl⟩ y ⟨s', w', hw₀', hw₁', rfl⟩ a b ha hb hab,
    let W : ι → R := λ i, (if i ∈ s then a * w i else 0) + (if i ∈ s' then b * w' i else 0),
    have hW₁ : (s ∪ s').sum W = 1,
    { rw [sum_add_distrib, ← sum_subset (subset_union_left s s'),
        ← sum_subset (subset_union_right s s'), sum_ite_of_true _ _ (λ i hi, hi),
        sum_ite_of_true _ _ (λ i hi, hi), ← mul_sum, ← mul_sum, hw₁, hw₁', ← add_mul, hab, mul_one];
      intros i hi hi';
      simp [hi'], },
    refine ⟨s ∪ s', W, _, hW₁, _⟩,
    { rintros i -,
      by_cases hi : i ∈ s;
      by_cases hi' : i ∈ s';
      simp [hi, hi', add_nonneg, mul_nonneg ha (hw₀ i _), mul_nonneg hb (hw₀' i _)], },
    { simp_rw [affine_combination_eq_linear_combination (s ∪ s') v _ hW₁,
        affine_combination_eq_linear_combination s v w hw₁,
        affine_combination_eq_linear_combination s' v w' hw₁', add_smul, sum_add_distrib],
      rw [← sum_subset (subset_union_left s s'), ← sum_subset (subset_union_right s s')],
      { simp only [ite_smul, sum_ite_of_true _ _ (λ i hi, hi), mul_smul, ← smul_sum], },
      { intros i hi hi', simp [hi'], },
      { intros i hi hi', simp [hi'], }, }, },
  { rintros x ⟨s, w, hw₀, hw₁, rfl⟩,
    exact affine_combination_mem_convex_hull hw₀ hw₁, },
end

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull R s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → R) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s),
    t.center_mass w z = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.center_mass, finset.sum_singleton, inv_one, one_smul] },
  { rintros x ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ y ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintros i hi,
      rw [finset.mem_disj_sum] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *], },
    { intros i hi,
      rw [finset.mem_disj_sum] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩; apply_rules [hzx, hzy] } },
  { rintros _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz }
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull R ↑s = {x : E | ∃ (w : E → R) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1),
    s.center_mass w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.center_mass_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintro x ⟨wx, hwx₀, hwx₁, rfl⟩ y ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab,
    rw [finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintros i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintros _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.center_mass_mem_convex_hull (λ x hx, hw₀ _ hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : s.finite) :
  convex_hull R s = {x : E | ∃ (w : E → R) (hw₀ : ∀ y ∈ s, 0 ≤ w y)
    (hw₁ : ∑ y in hs.to_finset, w y = 1), hs.to_finset.center_mass w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

/-- A weak version of Carathéodory's theorem. -/
lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull R s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull R ↑t :=
begin
  refine subset.antisymm _ _,
  { rw convex_hull_eq,
    rintros x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [coe_image, set.image_subset_iff],
      exact hz },
    { apply t.center_mass_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
  { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

lemma mk_mem_convex_hull_prod {t : set F} {x : E} {y : F} (hx : x ∈ convex_hull R s)
  (hy : y ∈ convex_hull R t) :
  (x, y) ∈ convex_hull R (s ×ˢ t) :=
begin
  rw convex_hull_eq at ⊢ hx hy,
  obtain ⟨ι, a, w, S, hw, hw', hS, hSp⟩ := hx,
  obtain ⟨κ, b, v, T, hv, hv', hT, hTp⟩ := hy,
  have h_sum : ∑ (i : ι × κ) in a ×ˢ b, w i.fst * v i.snd = 1,
  { rw [finset.sum_product, ← hw'],
    congr,
    ext i,
    have : ∑ (y : κ) in b, w i * v y = ∑ (y : κ) in b, v y * w i,
    { congr, ext, simp [mul_comm] },
    rw [this, ← finset.sum_mul, hv'],
    simp },
  refine ⟨ι × κ, a ×ˢ b, λ p, (w p.1) * (v p.2), λ p, (S p.1, T p.2),
    λ p hp, _, h_sum, λ p hp, _, _⟩,
  { rw mem_product at hp,
    exact mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2) },
  { rw mem_product at hp,
    exact ⟨hS p.1 hp.1, hT p.2 hp.2⟩ },
  ext,
  { rw [←hSp, finset.center_mass_eq_of_sum_1 _ _ hw', finset.center_mass_eq_of_sum_1 _ _ h_sum],
    simp_rw [prod.fst_sum, prod.smul_mk],
    rw finset.sum_product,
    congr,
    ext i,
    have : ∑ (j : κ) in b, (w i * v j) • S i = ∑ (j : κ) in b, v j • w i • S i,
    { congr, ext, rw [mul_smul, smul_comm] },
    rw [this, ←finset.sum_smul, hv', one_smul] },
  { rw [←hTp, finset.center_mass_eq_of_sum_1 _ _ hv', finset.center_mass_eq_of_sum_1 _ _ h_sum],
    simp_rw [prod.snd_sum, prod.smul_mk],
    rw [finset.sum_product, finset.sum_comm],
    congr,
    ext j,
    simp_rw mul_smul,
    rw [←finset.sum_smul, hw', one_smul] }
end

@[simp] lemma convex_hull_prod (s : set E) (t : set F) :
  convex_hull R (s ×ˢ t) = convex_hull R s ×ˢ convex_hull R t :=
subset.antisymm (convex_hull_min (prod_mono (subset_convex_hull _ _) $ subset_convex_hull _ _) $
  (convex_convex_hull _ _).prod $ convex_convex_hull _ _) $
    prod_subset_iff.2 $ λ x hx y, mk_mem_convex_hull_prod hx

lemma convex_hull_add (s t : set E) : convex_hull R (s + t) = convex_hull R s + convex_hull R t :=
by simp_rw [←image2_add, ←image_prod, is_linear_map.is_linear_map_add.convex_hull_image,
  convex_hull_prod]

lemma convex_hull_sub (s t : set E) : convex_hull R (s - t) = convex_hull R s - convex_hull R t :=
by simp_rw [sub_eq_add_neg, convex_hull_add, convex_hull_neg]

/-! ### `std_simplex` -/

variables (ι) [fintype ι] {f : ι → R}

/-- `std_simplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull R (range $ λ(i j:ι), if i = j then (1:R) else 0) = std_simplex R ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex R ι)) _,
  { rintros _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex R i },
  { rintros w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁],
    exact finset.univ.center_mass_mem_convex_hull (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : s.finite) :
  convex_hull R s = by haveI := hs.fintype; exact
    (⇑(∑ x : s, (@linear_map.proj R s _ (λ i, R) _ _ x).smul_right x.1)) '' (std_simplex R s) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← set.range_comp, (∘)],
  apply congr_arg,
  convert subtype.range_coe.symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex 𝕜 ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex R ι) (x) :
  f x ∈ Icc (0 : R) 1 :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩

/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
lemma convex_hull_affine_basis_eq_nonneg_barycentric {ι : Type*} (b : affine_basis ι R E) :
  convex_hull R (range b.points) = { x | ∀ i, 0 ≤ b.coord i x } :=
begin
  rw convex_hull_range_eq_exists_affine_combination,
  ext x,
  split,
  { rintros ⟨s, w, hw₀, hw₁, rfl⟩ i,
    by_cases hi : i ∈ s,
    { rw b.coord_apply_combination_of_mem hi hw₁,
      exact hw₀ i hi, },
    { rw b.coord_apply_combination_of_not_mem hi hw₁, }, },
  { intros hx,
    have hx' : x ∈ affine_span R (range b.points),
    { rw b.tot, exact affine_subspace.mem_top R E x, },
    obtain ⟨s, w, hw₁, rfl⟩ := (mem_affine_span_iff_eq_affine_combination R E).mp hx',
    refine ⟨s, w, _, hw₁, rfl⟩,
    intros i hi,
    specialize hx i,
    rw b.coord_apply_combination_of_mem hi hw₁ at hx,
    exact hx, },
end
