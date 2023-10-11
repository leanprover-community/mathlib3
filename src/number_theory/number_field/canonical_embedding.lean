/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.embeddings

/-!
# Canonical embedding of a number field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

noncomputable theory

open function finite_dimensional finset fintype number_field number_field.infinite_place metric
module
open_locale classical number_field

variables (K : Type*) [field K]

namespace number_field.canonical_embedding

-- The ambient space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`.
localized "notation `E` :=
  ({w : infinite_place K // is_real w} → ℝ) × ({w : infinite_place K // is_complex w} → ℂ)"
  in canonical_embedding

lemma space_rank [number_field K] :
  finrank ℝ E = finrank ℚ K :=
begin
  haveI : module.free ℝ ℂ := infer_instance,
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, complex.finrank_real_complex,
    finset.sum_const, finset.card_univ, ← card_real_embeddings, algebra.id.smul_eq_mul, mul_comm,
    ← card_complex_embeddings, ← number_field.embeddings.card K ℂ, fintype.card_subtype_compl,
    nat.add_sub_of_le (fintype.card_subtype_le _)],
end

lemma non_trivial_space [number_field K] : nontrivial E :=
begin
  obtain ⟨w⟩ := infinite_place.nonempty K,
  obtain hw | hw := w.is_real_or_is_complex,
  { haveI : nonempty {w : infinite_place K // is_real w} := ⟨⟨w, hw⟩⟩,
    exact nontrivial_prod_left },
  { haveI : nonempty {w : infinite_place K // is_complex w} := ⟨⟨w, hw⟩⟩,
    exact nontrivial_prod_right }
end

/-- The canonical embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
def _root_.number_field.canonical_embedding : K →+* E :=
ring_hom.prod (pi.ring_hom (λ w, w.prop.embedding)) (pi.ring_hom (λ w, w.val.embedding))

lemma _root_.number_field.canonical_embedding_injective [number_field K] :
  injective (number_field.canonical_embedding K) :=
  @ring_hom.injective _ _ _ _ (non_trivial_space K) _

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
    simp only [w.is_real_or_is_complex, set.mem_set_of_eq, finset.mem_union, set.mem_to_finset,
      finset.mem_univ], },
end

lemma norm_le_iff [number_field K] (x : K) (r : ℝ) :
  ‖canonical_embedding K x‖ ≤ r ↔ ∀ w : infinite_place K, w x ≤ r :=
begin
  obtain hr | hr := lt_or_le r 0,
  { obtain ⟨w⟩ := infinite_place.nonempty K,
    exact iff_of_false (hr.trans_le $ norm_nonneg _).not_le
      (λ h, hr.not_le $ (map_nonneg w _).trans $ h _) },
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left, ←nnreal.coe_le_coe, subtype.coe_mk] }
end

variables (K)

/-- The image of `𝓞 K` as a subring of `ℝ^r₁ × ℂ^r₂`. -/
def integer_lattice : subring E :=
(ring_hom.range (algebra_map (𝓞 K) K)).map (canonical_embedding K)

/-- The linear equiv between `𝓞 K` and the integer lattice. -/
def equiv_integer_lattice [number_field K] :
  𝓞 K ≃ₗ[ℤ] integer_lattice K :=
linear_equiv.of_bijective
  { to_fun := λ x, ⟨canonical_embedding K (algebra_map (𝓞 K) K x), algebra_map (𝓞 K) K x,
      by simp only [subring.mem_carrier, ring_hom.mem_range, exists_apply_eq_apply], rfl⟩,
    map_add' := λ x y, by simpa only [map_add],
    map_smul' := λ c x, by simpa only [zsmul_eq_mul, map_mul, map_int_cast] }
  begin
    refine ⟨λ _ _ h, _,  λ ⟨_, _, ⟨a, rfl⟩, rfl⟩, ⟨a, rfl⟩⟩,
    rw [linear_map.coe_mk, subtype.mk_eq_mk] at h,
    exact is_fraction_ring.injective (𝓞 K) K (canonical_embedding_injective K h),
  end

lemma integer_lattice.inter_ball_finite [number_field K] (r : ℝ) :
  ((integer_lattice K : set E) ∩ (closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  {  simp [closed_ball_eq_empty.2 hr] },
  have heq :
    ∀ x, canonical_embedding K x ∈ closed_ball (0 : E) r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r,
  { simp only [← place_apply, ← infinite_place.coe_mk, mem_closed_ball_zero_iff, norm_le_iff],
    exact λ x, le_iff_le x r, },
  convert (embeddings.finite_of_norm_le K ℂ r).image (canonical_embedding K),
  ext, split,
  { rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx2⟩,
    exact ⟨x, ⟨set_like.coe_mem x, (heq x).mp hx2⟩, rfl⟩, },
  { rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩,
    exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩, }
end

instance [number_field K] : countable (integer_lattice K) :=
begin
  have : (⋃ n : ℕ, ((integer_lattice K : set E) ∩ (closed_ball 0 n))).countable,
  { exact set.countable_Union (λ n, (integer_lattice.inter_ball_finite K n).countable) },
  refine (this.mono _).to_subtype,
  rintro _ ⟨x, hx, rfl⟩,
  rw set.mem_Union,
  exact ⟨⌈‖canonical_embedding K x‖⌉₊, ⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.2 (nat.le_ceil _)⟩,
end

end number_field.canonical_embedding
