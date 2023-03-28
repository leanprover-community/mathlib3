/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.embeddings

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of signature `(r₁, r₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main definitions and results

* `number_field.canonical_embedding.ring_of_integers.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

## Tags
number field, infinite places
-/

open_locale classical number_field

noncomputable theory

open number_field number_field.infinite_place module fintype finite_dimensional

variables (K : Type*) [field K]

namespace number_field.canonical_embedding

/-- The ambiant space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
@[reducible]
def space :=
  ({w : infinite_place K // is_real w} → ℝ) × ({w : infinite_place K // is_complex w} → ℂ)

instance : comm_ring (space K) := prod.comm_ring

instance : module ℝ (space K) := prod.module

lemma space_rank [number_field K] :
  finrank ℝ (space K) = finrank ℚ K :=
begin
  haveI : module.free ℝ ℂ := infer_instance,
  rw [module.free.finrank_prod, module.free.finrank_pi, module.free.finrank_pi_fintype,
    complex.finrank_real_complex, finset.sum_const, finset.card_univ, ← card_real_embeddings,
    algebra.id.smul_eq_mul, mul_comm, ← card_complex_embeddings, ← number_field.embeddings.card K ℂ,
    fintype.card_subtype_compl, nat.add_sub_of_le (fintype.card_subtype_le _)],
end

instance [number_field K] : nontrivial (space K) :=
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

/-- The canonical embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
def _root_.number_field.canonical_embedding : K →+* space K :=
ring_hom.prod
  (pi.ring_hom (λ w, w.prop.embedding))
  (pi.ring_hom (λ w, w.val.embedding))

lemma _root_.number_field.canonical_embedding_injective [number_field K] :
  function.injective (number_field.canonical_embedding K) := ring_hom.injective _

open number_field

variable {K}

@[simp]
lemma apply_at_real_infinite_place (w : {w : infinite_place K // is_real w}) (x : K) :
  (number_field.canonical_embedding K x).1 w = w.prop.embedding x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

@[simp]
lemma apply_at_complex_infinite_place (w : { w : infinite_place K // is_complex w}) (x : K) :
  (number_field.canonical_embedding K x).2 w = embedding w.val x :=
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
      simp only [apply_at_real_infinite_place, coe_nnnorm, real.norm_eq_abs,
        function.embedding.coe_subtype, subtype.coe_mk, is_real.abs_embedding_apply], },
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K,
        is_complex w)) (λ w, (⟨w x, map_nonneg w x⟩ : nnreal))).symm using 2,
      ext w,
      simp only [apply_at_complex_infinite_place, subtype.val_eq_coe, coe_nnnorm,
        complex.norm_eq_abs, function.embedding.coe_subtype, subtype.coe_mk, abs_embedding], }},
  { ext w,
    simp only [em (is_real w), set.mem_set_of_eq, finset.mem_union, set.mem_to_finset,
      finset.mem_univ, ←infinite_place.not_is_real_iff_is_complex], },
end

lemma le_of_le [number_field K] (x : K) (r : ℝ) :
  ‖canonical_embedding K x‖ ≤ r ↔ ∀ w : infinite_place K, w x ≤ r :=
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

variables (K)

/-- The image of `𝓞 K` as a subring of `ℝ^r₁ × ℂ^r₂`. -/
def integer_lattice : subring (space K) :=
subring.map (canonical_embedding K) (ring_hom.range (algebra_map (𝓞 K) K))

/-- The ring equiv between `𝓞 K` and the integer lattice. -/
def equiv_integer_lattice [number_field K] :
  𝓞 K ≃ₗ[ℤ] integer_lattice K :=
begin
  refine linear_equiv.of_bijective _ _,
  { refine linear_map.mk _ _ _,
    exact λ x, ⟨canonical_embedding K (algebra_map (𝓞 K) K x), algebra_map (𝓞 K) K x,
      by simp only [subring.mem_carrier, ring_hom.mem_range, exists_apply_eq_apply], rfl⟩,
    { intros _ _,
      simpa only [map_add], },
    { intros _ _,
      simpa only [zsmul_eq_mul, map_mul, map_int_cast], }},
  { split,
    { intros _ _ h,
      rw [linear_map.coe_mk, subtype.mk_eq_mk] at h,
      exact (is_fraction_ring.injective (𝓞 K) K) (canonical_embedding_injective K h), },
    { exact λ ⟨_, ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩⟩, ⟨a, rfl⟩, }}
end

lemma integer_lattice.inter_ball_finite [number_field K] (r : ℝ) :
  ((integer_lattice K : set (space K)) ∩ (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { have heq : ∀ x : K, canonical_embedding K x ∈ (metric.closed_ball (0 : (space K)) r) ↔
      ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r,
    { simp_rw [← place_apply, ← infinite_place.coe_mk, mem_closed_ball_zero_iff, le_of_le],
      exact λ x, le_iff_le x r, },
    convert set.finite.image (canonical_embedding K) (embeddings.finite_of_norm_le K ℂ r),
    ext, split,
    { rintros ⟨⟨_, ⟨⟨x, rfl⟩, rfl⟩⟩, hx2⟩,
      exact ⟨x, ⟨⟨set_like.coe_mem x, (heq x).mp hx2⟩, rfl⟩⟩, },
    { rintros ⟨x, ⟨⟨ hx1, hx2⟩, rfl⟩⟩,
      exact ⟨⟨x, ⟨⟨⟨x, hx1⟩, rfl⟩, rfl⟩⟩, (heq x).mpr hx2⟩, }},
end

instance [number_field K] : countable (integer_lattice K) :=
begin
  suffices : (⋃ n : ℕ, ((integer_lattice K : set (space K)) ∩ (metric.closed_ball 0 n))).countable,
  { refine set.countable.to_subtype (set.countable.mono _ this),
    rintros _ ⟨x, ⟨hx, rfl⟩⟩,
    rw set.mem_Union,
    use nat.ceil (‖canonical_embedding K x‖),
    exact ⟨⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.mpr (nat.le_ceil _)⟩, },
  { exact set.countable_Union (λ n, (integer_lattice.inter_ball_finite K n).countable), },
end

end number_field.canonical_embedding
