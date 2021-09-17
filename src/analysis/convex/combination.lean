/-
Copyright (c) 2019 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov
-/
import analysis.convex.basic

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `finset.linear_combination`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `finset.linear_combination` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.

## TODO

Change `finset.linear_combination : finset ι → (ι → E) → (ι → 𝕜) → E` to
`linear_combination : (ι → E) →ₗ[𝕜] (ι →₀ 𝕜) →ₗ[𝕜] E`. Same goes for `finset.affine_combination`.
-/

open set
open_locale big_operators classical

namespace finset

/-- Linear combination of a finite collection of points with prescribed weights. -/
def linear_combination {𝕜 E ι : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  (s : finset ι) (p : ι → E) (w : ι → 𝕜) : E :=
∑ i in s, w i • p i

section ordered_semiring
variables {𝕜 E ι ι' : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  (i j : ι) (c : 𝕜) (s : finset ι) (p : ι → E) (w : ι → 𝕜)

lemma linear_combination_def :
  s.linear_combination p w = ∑ i in s, w i • p i := rfl

lemma linear_combination_empty : (∅ : finset ι).linear_combination p w = 0 :=
by simp only [linear_combination, sum_empty, smul_zero]

lemma linear_combination_pair (hne : i ≠ j) :
  ({i, j} : finset ι).linear_combination p w = w i • p i + w j • p j :=
by rw [linear_combination, sum_pair hne]

variable {w}

lemma linear_combination_singleton :
  ({i} : finset ι).linear_combination p w = w i • p i :=
by rw [linear_combination, sum_singleton]

lemma linear_combination_insert (ha : i ∉ s) :
  (insert i s).linear_combination p w = w i • p i + s.linear_combination p w :=
by rw [linear_combination, linear_combination, sum_insert ha]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma linear_combination_segment' (s : finset ι) (t : finset ι') (ws : ι → 𝕜) (ps : ι → E)
  (wt : ι' → 𝕜) (pt : ι' → E) (a b : 𝕜) (hab : a + b = 1) :
  a • s.linear_combination ps ws + b • t.linear_combination pt wt =
    (s.map function.embedding.inl ∪ t.map function.embedding.inr).linear_combination
      (sum.elim ps pt)
      (sum.elim (λ i, a * ws i) (λ j, b * wt j)) :=
begin
  unfold linear_combination,
  rw [smul_sum, smul_sum, ← sum_sum_elim],
  { congr' with ⟨⟩; simp only [sum.elim_inl, sum.elim_inr, mul_smul] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma linear_combination_segment (s : finset ι) (w₁ w₂ : ι → 𝕜) (p : ι → E) (a b : 𝕜)
  (hab : a + b = 1) :
  a • s.linear_combination p w₁ + b • s.linear_combination p w₂ =
    s.linear_combination p (λ i, a * w₁ i + b * w₂ i) :=
begin
  unfold linear_combination,
  simp only [linear_combination_def, smul_sum, sum_add_distrib, add_smul, mul_smul, *],
end

lemma linear_combination_ite_eq (hi : i ∈ s) :
  s.linear_combination p (λ j, if (i = j) then 1 else 0) = p i :=
begin
  rw linear_combination,
  transitivity ∑ j in s, if (i = j) then p i else 0,
  { congr' with i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {s w}

lemma linear_combination_subset {t : finset ι} (ht : s ⊆ t)
  (h : ∀ i ∈ t, i ∉ s → w i = 0) :
  s.linear_combination p w = t.linear_combination p w :=
begin
  rw [linear_combination, linear_combination],
  exact sum_subset ht (λ i hit his, by rw [h i hit his, zero_smul]),
end

lemma linear_combination_filter_ne_zero :
  (s.filter (λ i, w i ≠ 0)).linear_combination p w = s.linear_combination p w :=
linear_combination_subset p (filter_subset _ _) $ λ i hit hit',
  by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variables {p} {t : set E}

end ordered_semiring

section ordered_comm_semiring
variables {𝕜 E ι ι' : Type*} [ordered_comm_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  (c : 𝕜) (s : finset ι) (p : ι → E) {w : ι → 𝕜}

lemma linear_combination_smul :
  s.linear_combination (λ i, c • p i) w = c • s.linear_combination p w :=
by simp_rw [linear_combination, smul_sum, smul_comm c]

end ordered_comm_semiring

section linear_ordered_field
variables {𝕜 E ι ι' : Type*} [linear_ordered_field 𝕜] [add_comm_monoid E] [module 𝕜 E]
  {s : set E} {t : finset ι} {p : ι → E} {w : ι → 𝕜}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.linear_combination_mem (ht : convex 𝕜 s) :
  (∀ i ∈ t, 0 ≤ w i) → (∑ i in t, w i = 1) → (∀ i ∈ t, p i ∈ s) → t.linear_combination p w ∈ s :=
begin
  induction t using finset.induction with i t hi ht, { simp [lt_irrefl] },
  intros h₀ h₁ hmem,
  have zi : p i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at h₁,
  rw linear_combination_insert _ _ _ hi,
  by_cases hsum_t : ∑ j in t, w j = 0,
  { have wt : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wp : t.linear_combination p w = 0, from sum_eq_zero (λ i hi, by simp [wt i hi]),
    rw [hsum_t, add_zero] at h₁,
    rw [wp, add_zero, h₁, one_smul],
    exact zi },
  { refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) h₁,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex 𝕜 s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hp : ∀ i ∈ t, p i ∈ s) :
  ∑ i in t, w i • p i ∈ s :=
by simpa only [h₁, linear_combination, inv_one, one_smul] using
  hs.linear_combination_mem h₀ (h₁.symm ▸ zero_lt_one) hz

lemma convex_iff_sum_mem :
  convex 𝕜 s ↔
    (∀ (t : finset E) (w : E → 𝕜),
      (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → ∑ x in t, w x • x ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x y hx hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if p = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

lemma finset.linear_combination_mem_convex_hull (t : finset ι) {w : ι → 𝕜} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : ∑ i in t, w i = 1) {p : ι → E} (hp : ∀ i ∈ t, p i ∈ s) :
  s.linear_combination p w ∈ convex_hull 𝕜 s :=
(convex_convex_hull 𝕜 s).linear_combination_mem hw₀ hws (λ i hi, subset_convex_hull 𝕜 s $ hp i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `p '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull 𝕜 s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → 𝕜) (p : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hp : ∀ i ∈ t, p i ∈ s),
    s.linear_combination p w = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.linear_combination, finset.sum_singleton, inv_one, one_smul] },
  { rintros x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.linear_combination_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintros i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩; apply_rules [hzx, hzy] } },
  { rintros _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact s.linear_combination_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hp }
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull 𝕜 ↑s = {x : E | ∃ (w : E → 𝕜) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1),
    s.linear_combination w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.linear_combination_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintros x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩
      a b ha hb hab,
    rw [finset.linear_combination_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintros i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintros _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.linear_combination_mem_convex_hull (λ x hx, hw₀ _ hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : finite s) :
  convex_hull 𝕜 s = {x : E | ∃ (w : E → 𝕜) (hw₀ : ∀ y ∈ s, 0 ≤ w y)
    (hw₁ : ∑ y in hs.to_finset, w y = 1), hs.to_finset.linear_combination w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

/-- A weak version of Carathéodory's theorem. -/
lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull 𝕜 s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull 𝕜 ↑t :=
begin
  refine subset.antisymm _ _,
  { rw convex_hull_eq,
    rintros x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [coe_image, set.image_subset_iff],
      exact hp },
    { apply s.linear_combination_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
   { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

/-! ### `std_simplex` -/

variables (ι) [fintype ι] {f : ι → 𝕜}

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull 𝕜 (range $ λ(i j:ι), if i = j then (1:𝕜) else 0) = std_simplex ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex ι)) _,
  { rintros _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex i },
  { rintros w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.linear_combination_eq_of_sum_1 _ hw₁],
    exact finset.univ.linear_combination_mem_convex_hull (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → 𝕜`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → 𝕜) →ₗ[𝕜] 𝕜` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : finite s) :
  convex_hull 𝕜 s = by haveI := hs.fintype; exact
    (⇑(∑ x : s, (@linear_map.proj 𝕜 s _ (λ i, 𝕜) _ _ x).smul_right x.1)) '' (std_simplex s) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← set.range_comp, (∘)],
  apply congr_arg,
  convert subtype.range_coe.symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex ι) (x) :
  f x ∈ Icc (0 : 𝕜) 1 :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩
