/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import number_theory.number_field.basic
import analysis.complex.polynomial
import topology.instances.complex

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.range_eval_eq_root_set_minpoly`: let `x ∈ K` with `K` number field and
  let `A` be an algebraic closed field of char. 0, then the images of `x` by the embeddings of `K`
   in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings, places, infinite places
-/

open_locale classical

namespace number_field.embeddings

section fintype

open finite_dimensional

variables (K : Type*) [field K] [number_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

end fintype

section roots

open set polynomial

variables (K A : Type*) [field K] [number_field K]
  [field A] [algebra ℚ A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
lemma range_eval_eq_root_set_minpoly : range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert (number_field.is_algebraic K).range_eval_eq_root_set_minpoly A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

section bounded

open finite_dimensional polynomial set

variables {K : Type*} [field K] [number_field K]
variables {A : Type*} [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
  ‖(minpoly ℚ x).coeff i‖ ≤ (max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2) :=
begin
  have hx := is_separable.is_integral ℚ x,
  rw [← norm_algebra_map' A, ← coeff_map (algebra_map ℚ A)],
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx) (is_alg_closed.splits_codomain _)
    (minpoly.nat_degree_le hx) (λ z hz, _) i,
  classical, rw ← multiset.mem_to_finset at hz,
  obtain ⟨φ, rfl⟩ := (range_eval_eq_root_set_minpoly K A x).symm.subset hz,
  exact h φ,
end

variables (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
lemma finite_of_norm_le (B : ℝ) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.finite :=
begin
  let C := nat.ceil ((max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2)),
  have := bUnion_roots_finite (algebra_map ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C),
  refine this.subset (λ x hx, _), simp_rw mem_Union,
  have h_map_ℚ_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1,
  refine ⟨_, ⟨_, λ i, _⟩, mem_root_set.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩,
  { rw [← (minpoly.monic hx.1).nat_degree_map (algebra_map ℤ ℚ), ← h_map_ℚ_minpoly],
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower hx.1) },
  rw [mem_Icc, ← abs_le, ← @int.cast_le ℝ],
  refine (eq.trans_le _ $ coeff_bdd_of_norm_le hx.2 i).trans (nat.le_ceil _),
  rw [h_map_ℚ_minpoly, coeff_map, eq_int_cast, int.norm_cast_rat, int.norm_eq_abs, int.cast_abs],
end

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
lemma pow_eq_one_of_norm_eq_one {x : K}
  (hxi : is_integral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_norm_le K A (1:ℝ)),
  { replace habne := habne.lt_or_lt,
    have : _, swap, cases habne, swap,
    { revert a b, exact this },
    { exact this b a h.symm habne },
    refine λ a b h hlt, ⟨a - b, tsub_pos_of_lt hlt, _⟩,
    rw [← nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h,
    refine h.resolve_right (λ hp, _),
    specialize hx (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom,
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx, norm_num at hx },
  { exact λ a _, ⟨hxi.pow a, λ φ, by simp only [hx φ, norm_pow, one_pow, map_pow]⟩ },
end

end bounded

end number_field.embeddings

section place

variables {K : Type*} [field K] {A : Type*} [normed_division_ring A] [nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def number_field.place :
  absolute_value K ℝ := absolute_value.comp (is_absolute_value.to_absolute_value (norm : A → ℝ)) φ

lemma number_field.place.apply (x : K) :
  (number_field.place φ) x = norm(φ x) := by refl

end place

namespace number_field.complex_embedding

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
def conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ

@[simp]
lemma conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

lemma conjugate_conjugate_eq (φ : K →+* ℂ) :
  conjugate (conjugate φ) = φ := star_involutive φ

lemma place_conjugate_eq_place (φ : K →+* ℂ) (x : K) : place (conjugate φ) x = place φ x :=
by simp only [place.apply, norm_eq_abs, abs_conj, conjugate_coe_eq]

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
def is_real (φ : K →+* ℂ) : Prop := is_self_adjoint φ

lemma is_real_iff {φ : K →+* ℂ} : is_real φ ↔ conjugate φ = φ := is_self_adjoint_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def is_real.embedding {φ : K →+* ℂ} (hφ : is_real φ) : K →+* ℝ :=
{ to_fun := λ x, (φ x).re,
  map_one' := by simp only [map_one, one_re],
  map_mul' := by simp only [complex.eq_conj_iff_im.mp (ring_hom.congr_fun hφ _), map_mul, mul_re,
  mul_zero, tsub_zero, eq_self_iff_true, forall_const],
  map_zero' := by simp only [map_zero, zero_re],
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const], }

@[simp]
lemma real_embedding_eq_embedding {φ : K →+* ℂ} (hφ : is_real φ) (x : K) :
  (hφ.embedding x : ℂ) = φ x :=
begin
  ext, { refl, },
  { rw [of_real_im, eq_comm, ← complex.eq_conj_iff_im],
    rw is_real at hφ,
    exact ring_hom.congr_fun hφ x, },
end

lemma place_real_embedding_eq_place {φ : K →+* ℂ} (hφ : is_real φ) :
  place hφ.embedding = place φ :=
by { ext x, simp only [place.apply, real.norm_eq_abs, ←abs_of_real, norm_eq_abs,
  real_embedding_eq_embedding hφ x], }

lemma is_real_conjugate_iff {φ : K →+* ℂ} :
  is_real (conjugate φ) ↔ is_real φ := is_self_adjoint.star_iff

end number_field.complex_embedding

section infinite_place

open number_field

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def number_field.infinite_place := { w : absolute_value K ℝ  // ∃ φ : K →+* ℂ, place φ = w}

instance [number_field K] : nonempty (number_field.infinite_place K) :=
begin
  rsuffices ⟨φ⟩ : nonempty (K →+* ℂ), { use ⟨place φ, ⟨φ, rfl⟩⟩, },
  rw [← fintype.card_pos_iff, embeddings.card K ℂ],
  exact finite_dimensional.finrank_pos,
end

variables {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def number_field.infinite_place.mk (φ : K →+* ℂ) : number_field.infinite_place K :=
⟨place φ, ⟨φ, rfl⟩⟩

namespace number_field.infinite_place

open number_field

instance : has_coe_to_fun (infinite_place K) (λ _, K → ℝ) := { coe := λ w, w.1 }

lemma infinite_place_eq_place (φ : K →+* ℂ) (x : K) : (mk φ) x = (place φ) x := by refl

lemma apply (φ : K →+* ℂ) (x : K) : (mk φ) x = complex.abs (φ x) := by refl

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : infinite_place K) : K →+* ℂ := (w.2).some

lemma infinite_place_embedding_eq_infinite_place (w : infinite_place K) :
  mk (embedding w) = w :=
by { ext, exact congr_fun (congr_arg coe_fn (w.2).some_spec) x, }

lemma place_embedding_eq_infinite_place (w : infinite_place K) (x : K) :
    place (embedding w) x = w x :=
 begin
   rw ← infinite_place_eq_place,
   exact congr_fun (congr_arg coe_fn (infinite_place_embedding_eq_infinite_place w)) x,
 end

lemma nonneg (w : infinite_place K) (x : K) : 0 ≤ w x := w.1.nonneg _

lemma eq_zero (w : infinite_place K) (x : K)  : w x = 0 ↔ x = 0 := w.1.eq_zero

@[simp]
lemma map_zero (w : infinite_place K) : w 0 = 0 := w.1.map_zero

@[simp]
lemma map_one (w : infinite_place K) : w 1 = 1 := w.1.map_one

@[simp]
lemma map_mul (w : infinite_place K) (x y : K) : w (x * y) = (w x) * (w y) := w.1.map_mul _ _

lemma infinite_place_conjugate_eq_infinite_place (φ : K →+* ℂ) :
  mk (complex_embedding.conjugate φ) = mk φ :=
begin
  ext x,
  convert complex_embedding.place_conjugate_eq_place φ x,
end

lemma eq_iff {φ ψ : K →+* ℂ} :
  mk φ = mk ψ ↔ φ = ψ ∨ complex_embedding.conjugate φ = ψ :=
begin
  split,
  { -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using complex.uniform_continuous_ring_hom_eq_id_or_conj
    intro h₀,
    obtain ⟨j, hiφ⟩ := φ.injective.has_left_inverse ,
    let ι := ring_equiv.of_left_inverse hiφ,
    have hlip : lipschitz_with 1 (ring_hom.comp ψ ι.symm.to_ring_hom),
    { change lipschitz_with 1 (ψ ∘ ι.symm),
      apply lipschitz_with.of_dist_le_mul,
      intros x y,
      rw [nonneg.coe_one, one_mul, normed_field.dist_eq, ← map_sub, ← map_sub],
      apply le_of_eq,
      suffices : ‖φ ((ι.symm) (x - y))‖ = ‖ψ ((ι.symm) (x - y))‖,
      { rw [← this, ← ring_equiv.of_left_inverse_apply hiφ _ , ring_equiv.apply_symm_apply ι _],
        refl, },
      exact congr_fun (congr_arg coe_fn h₀) _, },
    cases (complex.uniform_continuous_ring_hom_eq_id_or_conj φ.field_range hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { exact congr_arg mk h, },
    { rw ← infinite_place_conjugate_eq_infinite_place,
      exact congr_arg mk h, }},
end

/-- An infinite place is real if it is defined by a real embedding. -/
def is_real (w : infinite_place K) : Prop :=
  ∃ φ : K →+* ℂ, complex_embedding.is_real φ ∧ mk φ = w

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def is_complex (w : infinite_place K) : Prop :=
  ∃ φ : K →+* ℂ, ¬ complex_embedding.is_real φ ∧ mk φ = w

lemma embedding_or_conjugate_eq_embedding_infinite_place (φ : K →+* ℂ) :
  φ = embedding (mk φ) ∨ complex_embedding.conjugate φ = embedding (mk φ)
  := by simp only [←eq_iff, infinite_place_embedding_eq_infinite_place]

lemma embedding_eq_embedding_infinite_place_real {φ : K →+* ℂ} (h : complex_embedding.is_real φ) :
  φ = embedding (mk φ) :=
begin
  convert embedding_or_conjugate_eq_embedding_infinite_place φ,
  simp only [complex_embedding.is_real_iff.mp h, or_self],
end

lemma infinite_place_is_real_iff {w : infinite_place K} :
  is_real w ↔ complex_embedding.is_real (embedding w) :=
begin
  split,
  { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
    rwa ← embedding_eq_embedding_infinite_place_real hφ, },
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma infinite_place_is_complex_iff {w : infinite_place K} :
  is_complex w  ↔ ¬ complex_embedding.is_real (embedding w) :=
begin
  split,
    { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
      contrapose hφ,
      cases eq_iff.mp (infinite_place_embedding_eq_infinite_place (mk φ)),
      { rwa ← h, },
      { rw ← complex_embedding.is_real_conjugate_iff at hφ,
        rwa ← h, }},
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma not_is_real_iff_is_complex {w : infinite_place K} :
  ¬ is_real w ↔ is_complex w :=
by rw [infinite_place_is_complex_iff, infinite_place_is_real_iff]

/-- For `w` a real infinite place, return the corresponding embedding as a morphism `K →+* ℝ`. -/
noncomputable def is_real.embedding {w : infinite_place K} (hw : is_real w) : K →+* ℝ :=
(infinite_place_is_real_iff.mp hw).embedding

lemma is_real.place_embedding_eq_infinite_place {w : infinite_place K} (hw : is_real w) (x : K):
  place (is_real.embedding hw) x = w x :=
begin
  rw [is_real.embedding, complex_embedding.place_real_embedding_eq_place],
  exact place_embedding_eq_infinite_place _ _,
end

variable [number_field K]
variable (K)

open fintype

noncomputable instance : fintype (infinite_place K) := set.fintype_range _

lemma card_real_embeddings_eq :
  card {φ : K →+* ℂ // complex_embedding.is_real φ} = card {w : infinite_place K // is_real w} :=
begin
  rw fintype.card_of_bijective (_ : function.bijective _),
  { exact λ φ, ⟨mk φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  split,
  { rintros ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h,
    rw [subtype.mk_eq_mk, eq_iff, subtype.coe_mk, subtype.coe_mk,
      complex_embedding.is_real_iff.mp hφ, or_self] at h,
    exact subtype.eq h, },
  { exact λ ⟨w, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩, ⟨⟨φ, hφ1⟩,
    by { simp only [hφ2, subtype.coe_mk], }⟩, }
end

lemma card_complex_embeddings_eq :
  card {φ : K →+* ℂ // ¬ complex_embedding.is_real φ} =
  2 * card {w : infinite_place K // is_complex w} :=
begin
  let f : {φ : K →+* ℂ // ¬ complex_embedding.is_real φ} → {w : infinite_place K // is_complex w},
  { exact λ φ, ⟨mk φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  suffices :  ∀ w : {w // is_complex w}, card {φ // f φ = w} = 2,
  { rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
    conv { to_rhs, congr, skip, funext, rw ← this x, rw fintype.card, },
    simp_rw finset.card_eq_sum_ones,
    exact (fintype.sum_fiberwise f (function.const _ 1)).symm, },
  { rintros ⟨⟨w, hw⟩, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩,
    rw [fintype.card, finset.card_eq_two],
    refine ⟨⟨⟨φ, hφ1⟩, _⟩, ⟨⟨complex_embedding.conjugate φ, _⟩, _⟩, ⟨_, _⟩⟩,
    { simpa only [f, hφ2], },
    { rwa iff.not complex_embedding.is_real_conjugate_iff, },
    { simp only [f, ←hφ2, infinite_place_conjugate_eq_infinite_place, subtype.coe_mk], },
    { rwa [ne.def, subtype.mk_eq_mk, subtype.mk_eq_mk, ← ne.def, ne_comm], },
    { ext ⟨⟨ψ, hψ1⟩, hψ2⟩,
      simpa only [finset.mem_univ, finset.mem_insert, finset.mem_singleton, true_iff,
        @eq_comm _ ψ _, ← eq_iff, hφ2] using subtype.mk_eq_mk.mp hψ2.symm, }},
end

end number_field.infinite_place

end infinite_place

section canonical_embedding

open number_field number_field.infinite_place

variables (K : Type*) [field K]

localized "notation `E` :=
  ({w : infinite_place K // is_real w} → ℝ) ×
  ({w : infinite_place K // is_complex w} → ℂ)"
  in embeddings

noncomputable def number_field.canonical_embedding : K →+* E :=
ring_hom.prod
  (pi.ring_hom (λ ⟨_, hw⟩, hw.embedding))
  (pi.ring_hom (λ ⟨w, _⟩, w.embedding))

namespace number_field.canonical_embedding

open number_field

variable [number_field K]

lemma injective :
  function.injective (number_field.canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  obtain ⟨w⟩ := infinite_place.nonempty K,
  by_cases hw : is_real w,
  { convert nontrivial_prod_left,
    { convert @function.nontrivial _ _ _ real.nontrivial,
      use ⟨w, hw⟩, },
    exact nonempty_of_inhabited, },
  { convert nontrivial_prod_right,
    { exact nonempty_of_inhabited, },
    { convert @function.nontrivial _ _ _ complex.nontrivial,
      use ⟨w, not_is_real_iff_is_complex.mp hw⟩, }},
end

variable {K}

lemma eval_at_real_infinite_place {w : infinite_place K} (hw : is_real w) (x : K) :
  (number_field.canonical_embedding K x).1 ⟨w, hw⟩ = hw.embedding x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma eval_at_complex_infinite_place {w : infinite_place K} (hw : is_complex w) (x : K) :
  (number_field.canonical_embedding K x).2 ⟨w, hw⟩ = embedding w x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma nnnorm_eq (x : K) :
  ‖(canonical_embedding K) x‖₊ = finset.univ.sup (λ w : infinite_place K, ⟨w x, nonneg w x⟩) :=
begin
  rw [prod.nnnorm_def', pi.nnnorm_def, pi.nnnorm_def],
  rw ( _ : finset.univ = {w : infinite_place K | is_real w}.to_finset
    ∪ {w : infinite_place K | is_complex w}.to_finset),
  { rw finset.sup_union,
    rw sup_eq_max,
    refine congr_arg2 _ _ _,
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K, is_real w))
        (λ w, (⟨w x, w.nonneg x⟩ : nnreal))).symm using 2,
      ext w,
      rw [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk, real.norm_eq_abs,
        ← subtype.val_eq_coe, ← is_real.place_embedding_eq_infinite_place w.2 x,
        number_field.place.apply],
      congr,
      simp_rw [← eval_at_real_infinite_place _ x, subtype.val_eq_coe, subtype.coe_eta], },
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K,
        is_complex w)) (λ w, (⟨w x, w.nonneg x⟩ : nnreal))).symm using 2,
      ext w,
      rw [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk, complex.norm_eq_abs,
        ← subtype.val_eq_coe, ← place_embedding_eq_infinite_place w.1 x, number_field.place.apply],
      congr,
      rw [subtype.val_eq_coe, ← eval_at_complex_infinite_place w.prop x, subtype.coe_eta], }},
  { ext w,
    simp only [em (is_real w), set.mem_set_of_eq, finset.mem_union, set.mem_to_finset,
      finset.mem_univ, ←infinite_place.not_is_real_iff_is_complex], },
end

lemma le_of_le (r : ℝ) (x : K) :
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
      exact (not_le.mpr (lt_of_le_of_lt (h w) hr)) (w.nonneg _), }},
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left],
    split; { exact λ h w, h w, }},
end

localized "notation `Λ` := ((canonical_embedding K) '' number_field.ring_of_integers K)"
  in embeddings

lemma ring_of_integers_inter_ball_finite (r : ℝ) : (Λ ∩ (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { suffices : metric.closed_ball (0 : E) r = ∅,
    { rw [this, set.inter_empty],
      exact set.finite_empty, },
    rwa metric.closed_ball_eq_empty, },
  { rw ← set.finite_coe_iff,
    let A := { x : K | is_integral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r},
    haveI : finite A := set.finite_coe_iff.mpr (embeddings.finite_of_norm_le K ℂ r),
    have hiff : ∀ x, x ∈ (ring_of_integers K) →
      (x ∈ A ↔ (canonical_embedding K x) ∈ (metric.closed_ball (0 : E) r)),
    { intros x hx,
      rw [metric.mem_closed_ball, dist_zero_right, le_of_le],
      suffices : (∀ (w : infinite_place K), w x ≤ r) ↔ (∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r),
      { simp only [this, (mem_ring_of_integers K x).mp hx, set.mem_set_of_eq, true_and], },
      simp_rw [← place.apply, ← infinite_place.infinite_place_eq_place],
      split,
      { exact λ hw φ, hw (mk φ), },
      { intros hφ w,
        specialize hφ (embedding w),
        rwa ← infinite_place_embedding_eq_infinite_place w, }},
    refine finite.of_surjective (λ x : A, ⟨canonical_embedding K x, ⟨⟨x, ⟨(x.2).1, rfl⟩⟩,
       (hiff x x.2.1).mp (subtype.mem x)⟩⟩) _,
    rintros ⟨y, ⟨⟨x, ⟨hx1, rfl⟩⟩, hx2⟩⟩,
    use x,
    { exact (hiff x hx1).mpr hx2, },
    { simp only [subtype.coe_mk, subtype.mk_eq_mk], }},
end

end number_field.canonical_embedding

end canonical_embedding
