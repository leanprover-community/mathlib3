/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/

import number_theory.number_field.embeddings
import analysis.normed.group.basic

/-!
# Canonical embedding of a number field
The canonical embedding of a number field `K` of signature `(r₁, r_₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main Results
* `number_field.canonical_embedding.ring_of_integers.discrete`: the image of the ring of integers
  by the canonical embedding is discrete.

## Tags
number field, infinite places
-/

open_locale classical

section metric_space

-- TODO. Do without this or do the multiplicative version too
lemma add_group.discrete_of_finite_ball {α : Type*} [metric_space α] [add_group α]
  [has_continuous_add α] {r : ℝ} (hr : 0 < r) (h : (metric.ball (0 : α) r).finite) :
  discrete_topology α :=
begin
  rw discrete_topology_iff_open_singleton_zero,
  exact is_open_singleton_of_finite_mem_nhds 0 (metric.ball_mem_nhds _ hr) h,
end

end metric_space

section canonical_embedding

open number_field number_field.infinite_place

variables (K : Type*) [field K]

localized "notation `E` :=
  ({w : infinite_place K // is_real w} → ℝ) × ({w : infinite_place K // is_complex w} → ℂ)"
  in canonical_embedding

lemma number_field.canonical_embedding.nonempty [number_field K]: nontrivial E :=
begin
  obtain ⟨w⟩ := infinite_place.nonempty K,
  by_cases hw : is_real w,
  { convert nontrivial_prod_left,
    { convert @function.nontrivial _ _ _ real.nontrivial,
      use ⟨w, hw⟩, },
    exact nonempty_of_inhabited, },
 { convert nontrivial_prod_right,
   {  exact nonempty_of_inhabited, },
   {  convert @function.nontrivial _ _ _ complex.nontrivial,
      use ⟨w, not_is_real_iff_is_complex.mp hw⟩, }},
end

/-- The canonical embedding of a number field of signature `(s,t)` into `ℝ^s × ℂ^t`. -/
noncomputable def number_field.canonical_embedding : K →+* E :=
ring_hom.prod
  (pi.ring_hom (λ ⟨_, hw⟩, hw.embedding))
  (pi.ring_hom (λ ⟨w, _⟩, w.embedding))

namespace number_field.canonical_embedding

open number_field number_field.canonical_embedding

lemma injective [number_field K] :
  function.injective (number_field.canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  exact (number_field.canonical_embedding.nonempty K),
end

variable {K}

lemma apply_at_real_infinite_place {w : infinite_place K} (hw : is_real w) (x : K) :
  (number_field.canonical_embedding K x).1 ⟨w, hw⟩ = hw.embedding x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma apply_at_complex_infinite_place {w : infinite_place K} (hw : is_complex w) (x : K) :
  (number_field.canonical_embedding K x).2 ⟨w, hw⟩ = embedding w x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma nnnorm_eq [number_field K] (x : K) :
  ‖canonical_embedding K x‖₊ = finset.univ.sup (λ w : infinite_place K, ⟨w x, map_nonneg w x⟩) :=
begin
  rw [prod.nnnorm_def', pi.nnnorm_def, pi.nnnorm_def],
  rw ( _ : finset.univ = {w : infinite_place K | is_real w}.to_finset
    ∪ {w : infinite_place K | is_complex w}.to_finset),
  { rw [finset.sup_union, sup_eq_max],
    refine congr_arg2 _ _ _,
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K, is_real w))
        (λ w, (⟨w x, map_nonneg w x⟩ : nnreal))).symm using 2,
      ext w,
      rw [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk, real.norm_eq_abs,
        ← subtype.val_eq_coe, ← is_real.place_embedding w.2 x,
        number_field.place_apply],
      congr,
      simp_rw [← apply_at_real_infinite_place _ x, subtype.val_eq_coe, subtype.coe_eta], },
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K,
        is_complex w)) (λ w, (⟨w x, map_nonneg w x⟩ : nnreal))).symm using 2,
      ext w,
      rw [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk, complex.norm_eq_abs,
        ← subtype.val_eq_coe, ← congr_fun (congr_arg coe_fn (mk_embedding w.1)) x,
        infinite_place.coe_mk, number_field.place_apply],
      congr,
      rw [subtype.val_eq_coe, ← apply_at_complex_infinite_place w.prop x, subtype.coe_eta], }},
  { ext w,
    simp only [em (is_real w), set.mem_set_of_eq, finset.mem_union, set.mem_to_finset,
      finset.mem_univ, ←infinite_place.not_is_real_iff_is_complex], },
end

lemma le_of_le [number_field K] (x : K) (r : ℝ) :
  ‖(canonical_embedding K) x‖ ≤ r ↔ ∀ w : infinite_place K, w x ≤ r :=
begin
  obtain hr | hr := lt_or_le r 0,
  { split,
    { intro h,
      exfalso,
      exact (not_le.mpr (lt_of_le_of_lt h hr)) (norm_nonneg _), },
    { intro h,
      exfalso,
      obtain ⟨w⟩ := infinite_place.nonempty K,
      exact (not_le.mpr (lt_of_le_of_lt (h w) hr)) (map_nonneg w _), }},
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left],
    split; { exact λ h w, h w, }},
end

variable (K)

/-- The image of the ring of integers of `K` as a subring. -/
noncomputable def integer_lattice.subring : subring E :=
subring.map (canonical_embedding K) (ring_of_integers K).to_subring

localized "notation `Λ` := (integer_lattice.subring K)"
  in embeddings

lemma integer_lattice.inter_ball_finite [number_field K] (r : ℝ) :
  ((Λ : set E) ∩ (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { have heq : ∀ x : K, canonical_embedding K x ∈ (metric.closed_ball (0 : E) r) ↔
      ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r,
    { simp_rw [← place_apply, ← infinite_place.coe_mk, mem_closed_ball_zero_iff,
        le_of_le],
      exact λ x, le_iff_le x r, },
    convert set.finite.image (canonical_embedding K) (embeddings.finite_of_norm_le K ℂ r),
    ext, split,
    { rintros ⟨⟨x, ⟨hx1, rfl⟩⟩, hx2⟩,
      exact ⟨x, ⟨⟨hx1, (heq x).mp hx2⟩, rfl⟩⟩, },
    { rintros ⟨x, ⟨⟨ hx1, hx2⟩, rfl⟩⟩,
      exact ⟨⟨x, ⟨hx1, rfl⟩⟩, (heq x).mpr hx2⟩, }},
end

lemma integer_lattice.discrete [number_field K] : discrete_topology Λ :=
begin
  suffices : (metric.closed_ball (0 : Λ) 1).finite,
  { exact
    add_group.discrete_of_finite_ball (by norm_num) (this.subset metric.ball_subset_closed_ball), },
  refine set.finite.of_finite_image _ (subtype.coe_injective.inj_on _),
  rw (_ : coe '' (metric.closed_ball (0 : Λ) 1) = ((Λ : set E) ∩ (metric.closed_ball 0 1))),
  exact integer_lattice.inter_ball_finite K 1,
  ext, split,
  { rintros ⟨x, ⟨hx, rfl⟩⟩,
    exact ⟨subtype.mem x, hx⟩, },
  { rintros ⟨hx1, hx2⟩,
    use [x, hx1, ⟨hx2, rfl⟩], },
end

lemma integer_lattice.countable [number_field K] : countable Λ :=
begin
  suffices : (⋃ n : ℕ, ((Λ : set E) ∩ (metric.closed_ball 0 n))).countable,
  { refine set.countable.to_subtype (set.countable.mono _ this),
    rintros _ ⟨x, ⟨hx, rfl⟩⟩,
    rw set.mem_Union,
    use nat.ceil (‖canonical_embedding K x‖),
    exact ⟨⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.mpr (nat.le_ceil _)⟩, },
  { exact set.countable_Union (λ n, (integer_lattice.inter_ball_finite K n).countable), },
end


end number_field.canonical_embedding

end canonical_embedding
