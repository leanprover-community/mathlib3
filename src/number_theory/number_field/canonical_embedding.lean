/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.embeddings
import measure_theory.group.geometry_of_numbers
import ring_theory.discriminant
import algebra.module.zlattice

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
/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import number_theory.number_field.embeddings
import measure_theory.group.geometry_of_numbers
import ring_theory.discriminant
import algebra.module.zlattice

/-!
# Canonical embedding of a number field
The `canonical_embedding` of a number field `K` of signature `(r₁, r₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main definitions and results
* `number_field.canonical_embedding.ring_of_integers.inter_ball_finite`: the intersection of the
image of `𝓞 K` by `canonical_embedding` and any ball centered at `0` of finite radius is finite.
* `number_field.canonical_embedding.lattice_basis`:  a `ℝ`-basis of `ℝ^r₁ × ℂ^r₂` that is also
a `ℤ`-basis of the image of `𝓞 K` by `canonical_embedding`.
* `number_field.canonical_embedding.exists_ne_zero_mem_ring_of_integers_le`: for
`f : (infinite_place K) → nnreal` such that `prod_w f w` is large enough, returns `a : 𝓞 K` with
`a ≠ 0` and `∀ w : infinite_place K, w a < f w`.

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

lemma space_nontrivial [number_field K] : nontrivial (space K) :=
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
def _root_.number_field.canonical_embedding : K →+* (space K) :=
ring_hom.prod (pi.ring_hom (λ w, w.prop.embedding)) (pi.ring_hom (λ w, w.val.embedding))

lemma _root_.number_field.canonical_embedding_injective [number_field K] :
  function.injective (number_field.canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  exact (space_nontrivial K),
end

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
  𝓞 K ≃ₗ[ℤ] (integer_lattice K) :=
begin
  refine linear_equiv.of_bijective _ _,
  { refine linear_map.mk _ _ _,
    { exact λ x, ⟨canonical_embedding K (algebra_map (𝓞 K) K x), algebra_map (𝓞 K) K x,
      by simp only [subring.mem_carrier, ring_hom.mem_range, exists_apply_eq_apply], rfl⟩, } ,
    { intros _ _,
      simpa only [map_add], },
    { intros _ _,
      simpa only [zsmul_eq_mul, map_mul, map_int_cast], }},
  { split,
    { intros _ _ h,
      rw [linear_map.coe_mk, subtype.mk_eq_mk] at h,
      exact (is_fraction_ring.injective (𝓞 K) K) (canonical_embedding_injective K h), },
    { exact λ ⟨_, _, ⟨a, rfl⟩, rfl⟩, ⟨a, rfl⟩, }}
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
    { rintros ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx2⟩,
      exact ⟨x, ⟨⟨set_like.coe_mem x, (heq x).mp hx2⟩, rfl⟩⟩, },
    { rintros ⟨x, ⟨ hx1, hx2⟩, rfl⟩,
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩, }},
end

lemma integer_lattice.countable [number_field K] : countable (integer_lattice K) :=
begin
  suffices : (⋃ n : ℕ, ((integer_lattice K : set (space K)) ∩ (metric.closed_ball 0 n))).countable,
  { refine set.countable.to_subtype (set.countable.mono _ this),
    rintros _ ⟨x, ⟨hx, rfl⟩⟩,
    rw set.mem_Union,
    use nat.ceil (‖canonical_embedding K x‖),
    exact ⟨⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.mpr (nat.le_ceil _)⟩, },
  { exact set.countable_Union (λ n, (integer_lattice.inter_ball_finite K n).countable), },
end

section basis

open_locale complex_conjugate

variable (K)

/-- The embedding of `K` into `K →+* (K →+* ℂ) → ℂ` defined by sending `x : K` to the vector of its
image by all the complex embeddings of `K`. -/
def _root_.number_field.full_embedding : K →+* (K →+* ℂ) → ℂ :=
{ to_fun := λ x φ, φ x,
  map_zero' := funext (λ φ, map_zero φ),
  map_one' := funext (λ φ, map_one φ),
  map_add' := λ x y, funext (λ φ, map_add φ x y),
  map_mul' := λ x y, funext (λ φ, map_mul φ x y), }

/-- The map from `(K →+* ℂ) → ℂ` to `space K` that gives a commuting diagramm, see
`number_field.canonical_embedding.commutes`. -/
def comm_map : ((K →+* ℂ) → ℂ) →ₗ[ℝ] (space K):=
{ to_fun := λ e, ⟨λ w, (e w.val.embedding).re, λ w, (e w.val.embedding)⟩,
  map_smul' := λ _ _, by simp_rw [ring_hom.id_apply, prod.smul_mk, pi.smul_def, smul_eq_mul,
    complex.real_smul, complex.of_real_mul_re],
  map_add' := λ _ _, by simp only [subtype.val_eq_coe, pi.add_apply, complex.add_re, prod.mk_add_mk,
    pi.add_def, eq_self_iff_true], }

lemma _root_.number_field.full_embedding.conj_apply [number_field K] {x : (K →+* ℂ) → ℂ}
  (φ : K →+* ℂ) (hx : x ∈ submodule.span ℝ
    (set.range (λ i, number_field.full_embedding K (integral_basis K i)))) :
  x (complex_embedding.conjugate φ) = conj (x φ) :=
begin
  refine submodule.span_induction hx _ _ (λ _ _ hx hy, _) (λ _ _ hx, _),
  { rintros _ ⟨_, rfl⟩, refl, },
  { simp only [pi.zero_apply, map_zero], },
  { rw [pi.add_apply, pi.add_apply, map_add, hx, hy], },
  { rw [pi.smul_apply, pi.smul_apply, complex.real_smul, complex.real_smul, map_mul, hx,
      is_R_or_C.conj_of_real], }
end

open number_field

lemma comm_map_eq_zero [number_field K] {x : (K →+* ℂ) → ℂ}
  (hx : x ∈ submodule.span ℝ (set.range (λ i, full_embedding K (integral_basis K i))))
  (hc : comm_map K x = 0):
  x = 0 :=
begin
  ext1 φ,
  rw pi.zero_apply,
  by_cases hφ : complex_embedding.is_real φ,
  { rw (_ : x φ = (x φ).re),
    { convert congr_arg (coe : ℝ → ℂ)
        (congr_arg (λ x : (space K), x.1 ⟨mk φ, ⟨φ, hφ, rfl⟩⟩) hc),
      exact (complex_embeddings.is_real.embedding_mk hφ).symm, },
    { rw [eq_comm, ← complex.eq_conj_iff_re, ← full_embedding.conj_apply K _ hx,
        complex_embedding.is_real_iff.mp hφ], }},
  { have heqz := congr_arg (λ x : (space K), x.2 ⟨mk φ, ⟨φ, hφ, rfl⟩⟩) hc,
    by_cases h_same : φ = (infinite_place.mk φ).embedding,
    { convert heqz using 2, },
    { rw [ ← map_eq_zero_iff (star_ring_end ℂ) star_injective, ← full_embedding.conj_apply K _ hx],
      rw (_ : φ = complex_embedding.conjugate (infinite_place.mk φ).embedding),
      { convert heqz using 2,
        ext1 φ,
        simp only [complex_embedding.conjugate_coe_eq, star_ring_end_self_apply], },
      { rw eq_comm,
        refine (mk_eq_iff.mp _).resolve_left (ne_comm.mp h_same),
        exact mk_embedding _, }}},
end

lemma commutes (x : K) :
  comm_map K (full_embedding K x) = canonical_embedding K x :=
begin
  simp_rw [comm_map, full_embedding, canonical_embedding, subtype.val_eq_coe, ring_hom.coe_mk,
    linear_map.coe_mk, ring_hom.prod_apply, prod.mk.inj_iff],
  split,
  { ext w,
    simpa only [pi.ring_hom_apply, ← complex_embedding.is_real.coe_embedding_apply
      (is_real_iff.mp w.prop) x, complex.of_real_re], },
  { ext1 w,
    simp only [pi.ring_hom_apply], },
end

/-- A `ℝ`-basis of `(space K)` that is also a `ℤ`-basis of the `unit_lattice`. -/
def lattice_basis [number_field K] : basis (free.choose_basis_index ℤ (𝓞 K)) ℝ (space K) :=
begin
  let e : (K →+* ℂ) ≃ free.choose_basis_index ℤ (𝓞 K) :=
    equiv_of_card_eq ((embeddings.card K ℂ).trans (finrank_eq_card_basis (integral_basis K))),
  -- Assume that `full_embedding K (integral_basis K)` is `ℂ`-linear independent then we deduce
  -- using `comm_map_eq_zero` that `canonical_embedding K (integral_basis K)` is
  -- `ℂ`-linear independent and thus `ℤ`-linear independent and yields the desired basis.
  suffices : linear_independent ℂ (λ i, full_embedding K (integral_basis K (e i))),
  { replace := @linear_independent.restrict_scalars _ ℝ ℂ _ _ _ _ _ _ _ _ _
      (smul_left_injective ℝ one_ne_zero) this,
    replace : linear_independent ℝ (λ i, full_embedding K (integral_basis K i)),
    { refine (linear_independent_equiv' e.symm _).mpr this,
      ext1 φ,
      simp only [equiv.apply_symm_apply, function.comp_app], },
    replace : linear_independent ℝ (λ i, (comm_map K ∘ full_embedding K) (integral_basis K i)),
    { exact linear_independent.map this
        (linear_map.disjoint_ker.mpr (λ x hx hc, comm_map_eq_zero K hx hc)), },
    replace : linear_independent ℝ (λ i, canonical_embedding K (integral_basis K i)),
    { refine (linear_independent_equiv' (equiv.refl _) _).mp this,
      ext1 i,
      exact (commutes K (integral_basis K i)).symm, },
    refine basis_of_linear_independent_of_card_eq_finrank this _,
    rw [canonical_embedding.space_rank, ← free.finrank_eq_card_choose_basis_index,
      ← ring_of_integers.rank], },
  -- To prove that `full_embedding K (integral_basis K)` is `ℂ`-linear independent, we
  -- prove that the square of the determinant of its matrix on the standard basis of
  -- `((K →* ℂ) → ℂ)` is the discrimininant of the `ℚ`-algebra `K` and thus it is not zero.
  let B := pi.basis_fun ℂ (K →+* ℂ),
  let M := B.to_matrix (λ i, full_embedding K (integral_basis K (e i))),
  suffices : M.det ≠ 0,
  { rw [← is_unit_iff_ne_zero, ← basis.det_apply, ← is_basis_iff_det] at this,
    exact this.1, },
  let N := algebra.embeddings_matrix_reindex ℚ ℂ (λ i, integral_basis K (e i))
    ring_hom.equiv_rat_alg_hom,
  rw (_ : M = N.transpose),
  { rw [matrix.det_transpose, ← @pow_ne_zero_iff ℂ _ _ _ 2 (by norm_num)],
    convert (map_ne_zero_iff _ (algebra_map ℚ ℂ).injective).mpr
      (algebra.discr_not_zero_of_basis ℚ (integral_basis K)),
    rw ← algebra.discr_reindex ℚ (integral_basis K) e.symm,
    exact (algebra.discr_eq_det_embeddings_matrix_reindex_pow_two ℚ ℂ
      (λ i, integral_basis K (e i)) ring_hom.equiv_rat_alg_hom).symm, },
  { ext1 φ j,
    simpa only [M, N, basis.to_matrix_apply _ _ φ j, pi.basis_fun_repr], },
end

lemma lattice_basis_apply [number_field K] (i : free.choose_basis_index ℤ (𝓞 K)) :
  (lattice_basis K) i = (canonical_embedding K) (integral_basis K i) :=
by simp only [lattice_basis, coe_basis_of_linear_independent_of_card_eq_finrank]

lemma lattice_basis_span [number_field K] :
  (submodule.span ℤ (set.range (lattice_basis K)) : set (space K)) = integer_lattice K :=
begin
  rw (_ : set.range (lattice_basis K) =
    (canonical_embedding K).to_int_alg_hom.to_linear_map '' (set.range (integral_basis K))),
  { rw ← submodule.map_span,
    rw (_ : set.range (integral_basis K) =
      (algebra_map (𝓞 K) K).to_int_alg_hom.to_linear_map '' (set.range (ring_of_integers.basis K))),
    { rw [← submodule.map_span, (ring_of_integers.basis K).span_eq, submodule.map_coe,
        submodule.map_coe],
      ext, split,
      { rintro ⟨_, ⟨a, _, rfl⟩, rfl⟩,
        exact ⟨a, set.mem_range_self a, rfl⟩, },
      { rintro ⟨_, ⟨a, rfl⟩, rfl⟩,
        exact ⟨a, ⟨a, trivial, rfl⟩, rfl⟩, }},
    { rw ← set.range_comp,
      refine congr_arg _ _,
      ext, simpa only [integral_basis_apply, function.comp_app, alg_hom.to_linear_map_apply], }},
  { rw ← set.range_comp,
    refine congr_arg _ _,
    ext1, simpa only [lattice_basis_apply, integral_basis_apply, function.comp_app,
      alg_hom.to_linear_map_apply], },
end

end basis

section convex_body

open measure_theory

/-- The real part of the convex body defined by `f`, see `convex_body`. -/
def convex_body_real (f : infinite_place K → nnreal) : set ({w : infinite_place K // is_real w} → ℝ)
:= set.pi set.univ (λ w, metric.ball 0 (f w))

/-- The complex part of the convex body defined by `f`, see `convex_body`. -/
def convex_body_complex (f : infinite_place K → nnreal) :
  set ({w : infinite_place K // is_complex w} → ℂ) :=
set.pi set.univ (λ w, metric.ball 0 (f w))

/-- The convex body defined by `f`: the set of points `x : space K` such that `x w < f w` for all
infinite places `w`. -/
@[reducible]
def convex_body (f : infinite_place K → nnreal): set (space K) :=
(convex_body_real K f) ×ˢ (convex_body_complex K f)

lemma convex_body.symmetric (f : infinite_place K → nnreal) (x : space K)
  (hx : x ∈ (convex_body K f)) : -x ∈ (convex_body K f) :=
begin
  refine set.mem_prod.1 ⟨_, _⟩,
  { intros w _,
    simpa only [prod.fst_neg, pi.neg_apply, mem_ball_zero_iff, real.norm_eq_abs, abs_neg]
      using mem_ball_zero_iff.1 (hx.1 w (set.mem_univ _)), },
  { intros w _,
    simpa only [prod.snd_neg, pi.neg_apply, mem_ball_zero_iff, complex.norm_eq_abs,
      absolute_value.map_neg] using mem_ball_zero_iff.mp (hx.right w (set.mem_univ w)), }
end

lemma convex_body.convex (f : infinite_place K → nnreal) :
  convex ℝ (convex_body K f) :=
convex.prod (convex_pi (λ i _, (convex_ball 0 (f i)))) (convex_pi (λ i _, (convex_ball 0 (f i))))

lemma convex_body_mem (f : infinite_place K → nnreal) (x : K) :
  canonical_embedding K x ∈ (convex_body K f) ↔ ∀ w : infinite_place K, w x < f w :=
begin
  suffices : (∀ w : infinite_place K, w x < f w) ↔
    (∀ w : infinite_place K, w.is_real ∨ w.is_complex → w x < f w),
  { simp only [this, ball_or_left_distrib, set.mem_prod, convex_body_real, convex_body_complex,
    set.mem_univ_pi, apply_at_real_infinite_place, mem_ball_zero_iff, real.norm_eq_abs,
    is_real.abs_embedding_apply, subtype.forall, subtype.coe_mk, apply_at_complex_infinite_place,
    complex.norm_eq_abs, abs_embedding], },
  simp only [← infinite_place.not_is_real_iff_is_complex, em, forall_true_left],
end

variable [number_field K]

/-- The complex Haar measure giving measure 1 to the unit box in `ℂ ≃ ℝ × ℝ`. -/
@[reducible]
def unit_measure : measure (space K) :=
measure.prod (measure.pi (λ _, volume)) (measure.pi (λ _, complex.basis_one_I.add_haar))

instance : measure.is_add_haar_measure (unit_measure K) :=
begin
  haveI : measure.is_add_haar_measure complex.basis_one_I.add_haar := infer_instance,
  haveI : has_measurable_add ℂ := infer_instance,
  have : measure.is_add_haar_measure (measure.pi (λ w : { w : infinite_place K // is_complex w },
    complex.basis_one_I.add_haar)) := @measure.pi.is_add_haar_measure _ _ _ _ _ _ _ _ _ _,
  convert measure.prod.is_add_haar_measure _ _,
  any_goals { apply_instance, },
end

lemma convex_body_real.volume (f : infinite_place K → nnreal) :
  measure.pi (λ _, volume) (convex_body_real K f) =
    2 ^ card {w : infinite_place K // is_real w} *
    finset.univ.prod (λ w : {w : infinite_place K // is_real w}, f w) :=
by simp_rw [convex_body_real, measure.pi_pi, real.volume_ball,
  ennreal.of_real_mul (by norm_num : 0 ≤ (2 : ℝ)), ennreal.of_real_bit0, ennreal.of_real_one,
  ennreal.of_real_coe_nnreal, finset.prod_mul_distrib, finset.prod_const, finset.card_univ]

lemma convex_body_complex.volume (f : infinite_place K → nnreal) :
  (measure.pi (λ _, complex.basis_one_I.add_haar)) (convex_body_complex K f) =
  (complex.basis_one_I.add_haar) (metric.ball 0 1) ^
  card {w : infinite_place K // is_complex w} *
  finset.univ.prod (λ w : {w : infinite_place K // is_complex w}, (f w) ^ 2) :=
begin
  haveI : measure.is_add_haar_measure complex.basis_one_I.add_haar := infer_instance,
  haveI : has_measurable_add ℂ := infer_instance,
  haveI : measure.is_add_haar_measure (measure.pi (λ w : { w : infinite_place K // is_complex w },
    complex.basis_one_I.add_haar)) := @measure.pi.is_add_haar_measure _ _ _ _ _ _ _ _ _ _,
  rw [ convex_body_complex, measure.pi_pi],
  conv { to_lhs, congr, skip, funext,
    rw measure.add_haar_ball complex.basis_one_I.add_haar 0 (f i).prop,
    rw ennreal.of_real_pow (f i).prop, },
  simp_rw [finset.prod_mul_distrib, finset.prod_const, mul_comm, complex.finrank_real_complex,
    finset.card_univ, ennreal.of_real_coe_nnreal],
end

/-- The fudge factor that appears in the formula for the volume of `convex_body`.-/
def constant_volume : ennreal := 2 ^ card {w : infinite_place K // is_real w} *
  (complex.basis_one_I.add_haar) (metric.ball 0 1) ^ card {w : infinite_place K // is_complex w}

lemma constant_volume_pos : 0 < (constant_volume K) :=
begin
  refine ennreal.mul_pos (ne_zero.ne _) _,
  exact ennreal.pow_ne_zero (ne_of_gt (metric.measure_ball_pos _ _ (by norm_num))) _,
end

lemma constant_volume_lt_top : (constant_volume K) < ⊤ :=
begin
  refine ennreal.mul_lt_top _ _,
  { exact ne_of_lt (ennreal.pow_lt_top (lt_top_iff_ne_top.mpr ennreal.two_ne_top) _), },
  { exact ne_of_lt (ennreal.pow_lt_top measure_ball_lt_top _), },
end

lemma convex_body.volume (f : infinite_place K → nnreal) :
  (unit_measure K) (convex_body K f) = (constant_volume K) *
    finset.univ.prod (λ w : infinite_place K, (ite (w.is_real) (f w) (f w ^ 2))) :=
begin
  haveI : sigma_finite complex.basis_one_I.add_haar := infer_instance,
  haveI : sigma_finite (measure.pi (λ w : { w : infinite_place K // is_complex w},
    complex.basis_one_I.add_haar)) := infer_instance,
  rw [measure.prod_prod, convex_body_real.volume, constant_volume, mul_assoc, mul_assoc,
    ennreal.mul_eq_mul_left _ _],
  { rw [mul_comm, finset.prod_ite, convex_body_complex.volume, mul_assoc,
      ennreal.mul_eq_mul_left _ _],
    { rw mul_comm,
      refine congr_arg2 _ _ _;
      { rw eq_comm,
        refine finset.prod_subtype _ _ _,
        simp only [finset.mem_filter, finset.mem_univ, true_and, iff_self, forall_const,
          not_is_real_iff_is_complex], }},
    { exact ennreal.pow_ne_zero (ne_of_gt (metric.measure_ball_pos _ _ (by norm_num))) _, },
    { exact ne_of_lt (ennreal.pow_lt_top measure_ball_lt_top _), }},
  { exact ne_zero.ne _, },
  { exact ne_of_lt (ennreal.pow_lt_top (lt_top_iff_ne_top.mpr ennreal.two_ne_top) _), },
end

/-- The bound that appears in Minkowski theorem, see
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure`.-/
def minkowski_bound : ennreal := (unit_measure K) (zspan.fundamental_domain (lattice_basis K)) *
  2 ^ (finrank ℝ (space K))

lemma minkowski_bound_lt_top : minkowski_bound K < ⊤ :=
begin
  refine ennreal.mul_lt_top _ _,
  { exact ne_of_lt (zspan.fundamental_domain_metric_bounded (lattice_basis K)).measure_lt_top, },
  { exact ne_of_lt (ennreal.pow_lt_top (lt_top_iff_ne_top.mpr ennreal.two_ne_top) _), },
end

lemma exists_ne_zero_mem_ring_of_integers_lt {f : (infinite_place K) → nnreal}
  (hf : minkowski_bound K < (unit_measure K) (convex_body K f)) :
  ∃ (a : 𝓞 K), a ≠ 0 ∧ ∀ w : infinite_place K, w a < f w :=
begin
  haveI : countable (submodule.span ℤ (set.range (lattice_basis K))).to_add_subgroup,
  { change countable (submodule.span ℤ (set.range (lattice_basis K)) : set (space K)),
    rw lattice_basis_span,
    exact integer_lattice.countable K, },
  have h_funddomain := zspan.is_add_fundamental_domain (lattice_basis K) (unit_measure K),
  obtain ⟨⟨x, hx⟩, hnz, hmem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_funddomain hf (convex_body.symmetric K f) (convex_body.convex K f),
  rw [submodule.mem_to_add_subgroup, ← set_like.mem_coe, lattice_basis_span] at hx,
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx,
  refine ⟨a, _, by { rwa ← convex_body_mem, }⟩,
  contrapose! hnz,
  simp only [hnz, map_zero, submodule.mk_eq_zero],
end

end convex_body

end number_field.canonical_embedding
