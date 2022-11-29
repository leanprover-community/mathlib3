/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import number_theory.number_field.basic
import topology.algebra.polynomial
import number_theory.number_field.aux
import analysis.special_functions.log.basic

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
number field, embeddings
-/

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
  refine ⟨_, ⟨_, λ i, _⟩, (mem_root_set_iff (minpoly.ne_zero hx.1) x).2 (minpoly.aeval ℤ x)⟩,
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

section place

variables {A : Type*} [normed_division_ring A] {K : Type*} [field K] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def place : K → ℝ := norm ∘ φ

end place

section complex_embeddings

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
def conjugate (φ : K →+* ℂ) : K →+* ℂ := ring_hom.comp conj_ae.to_ring_equiv.to_ring_hom φ

lemma conjugate.coe_eq (φ : K →+* ℂ) : (conjugate φ : K → ℂ) = conj ∘ φ := rfl

lemma conjugate.place_eq (φ : K →+* ℂ) : place (conjugate φ) = place φ :=
by { ext1, simp only [place, conjugate.coe_eq, function.comp_app, norm_eq_abs, abs_conj] }

/-- Two complex embeddings define the same place iff they are equal or complex conjugate. -/
lemma infinite_place_eq_iff {φ ψ : K →+* ℂ} :
  place φ = place ψ ↔ φ = ψ ∨ conjugate φ = ψ :=
begin
  split,
  { intro h₀,
    obtain ⟨_, hiφ⟩ := φ.injective.has_left_inverse ,
    let ι := ring_equiv.of_left_inverse hiφ,
    have hlip : lipschitz_with 1 (ring_hom.comp ψ ι.symm.to_ring_hom),
    { change lipschitz_with 1 (ψ ∘ ι.symm),
      apply lipschitz_with.of_dist_le_mul,
      intros x y,
      rw [nonneg.coe_one, one_mul, normed_field.dist_eq, ← map_sub, ← map_sub],
      convert (le_of_eq (congr_fun h₀ (ι.symm (x - y))).symm) using 1,
      rw [place, function.comp_app, ← ring_equiv.of_left_inverse_apply hiφ _,
        ring_equiv.apply_symm_apply ι _],
      refl, },
    cases (φ.field_range.uniform_continuous_ring_hom_eq_id_or_conj hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { ext x, convert congr_arg complex.abs (ring_hom.congr_fun h x), },
    { ext x, rw [← h, conjugate.place_eq], }},
end

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
def is_real (φ : K →+* ℂ): Prop := conjugate φ = φ

/-- A embedding into `ℂ` is complex if it is not fixed by complex conjugation. -/
def is_complex (φ : K →+* ℂ): Prop := conjugate φ ≠ φ

/-- A real embedding as a ring hom `K →+* ℝ` . -/
def real_embedding {φ : K →+* ℂ} (hφ : is_real φ) : K →+* ℝ :=
{ to_fun := λ x, (φ x).re,
  map_one' := by simp only [map_one, one_re],
  map_mul' :=
  begin
    intros x y,
    have := λ z, eq_conj_iff_im.mp (ring_hom.congr_fun hφ z),
    simp only [this, mul_zero, map_mul, mul_re, tsub_zero],
  end,
  map_zero' := by simp only [map_zero, zero_re],
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const], }

lemma conjugate_conjugate (φ : K →+* ℂ) :
  conjugate (conjugate φ) = φ :=
  by { ext1, simp only [conjugate.coe_eq, function.comp_app, star_ring_end_self_apply], }

lemma conjugate.is_real_iff (φ : K →+* ℂ) :
  is_real (conjugate φ) ↔ is_real φ := by simp only [is_real, conjugate_conjugate, eq_comm]

lemma conjugate.is_complex_iff (φ : K →+* ℂ) :
  is_complex (conjugate φ) ↔ is_complex φ := by simp only [is_complex, conjugate_conjugate, ne_comm]

end complex_embeddings

end number_field.embeddings

section infinite_places

open number_field fintype number_field.embeddings subtype

-- TODO. figure out naming and order of results and variables...

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to an embedding into 'ℂ'. -/
def infinite_places := set.range (λ φ : K →+* ℂ, place φ)

variable {K}

/-- An infinite place is real if it is defined by a real embedding. -/
def place_is_real (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, is_real φ ∧ place φ = w

/-- An infinite place is complex if it is defined by a complex embedding. -/
def place_is_complex (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, is_complex φ ∧ place φ = w

variable [number_field K]
variable (K)

open_locale classical

noncomputable instance : fintype (infinite_places K) := set.fintype_range _

lemma card_real_embeddings_eq :
  card {φ : K →+* ℂ // is_real φ} = card {w : infinite_places K // place_is_real w} :=
begin
  rw fintype.card_of_bijective (_ : function.bijective _),
  exact λ φ, ⟨⟨place φ.val, ⟨φ, rfl⟩⟩, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩,
  split,
  { rintros ⟨_, hφ⟩ _ h,
    rw is_real at hφ,
    rwa [mk_eq_mk, mk_eq_mk, infinite_place_eq_iff, hφ, or_self, ← ext_iff_val] at h, },
  { exact λ ⟨_, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩, ⟨⟨φ, hφ1⟩, by { simp only [mk_eq_mk, hφ2, coe_eta], }⟩, },
end

lemma card_complex_embeddings_eq :
  card {φ : K →+* ℂ // is_complex φ} = 2 * card {w : infinite_places K // place_is_complex w} :=
begin
  let f : {φ : K →+* ℂ // is_complex φ} → {w : infinite_places K // place_is_complex w},
  { exact λ φ, ⟨⟨place φ.val, ⟨φ, rfl⟩⟩, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  suffices :  ∀ w : {w // place_is_complex w}, card {φ // f φ = w} = 2,
  { rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
    conv { to_rhs, congr, skip, funext, rw ← this x, rw fintype.card, },
    simp_rw finset.card_eq_sum_ones,
    exact (fintype.sum_fiberwise f (function.const _ 1)).symm, },
  { rintros ⟨⟨w, hw⟩, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩,
    rw [fintype.card, finset.card_eq_two],
    refine ⟨⟨⟨φ, hφ1⟩, _⟩, ⟨⟨conjugate φ, (conjugate.is_complex_iff φ).mpr hφ1⟩, _⟩, ⟨_, _⟩⟩,
    repeat { simp only [f, hφ2, coe_mk, conjugate.place_eq], },
    { exact subtype.ne_of_val_ne (ne_of_val_ne hφ1.symm), },
    ext ⟨⟨ψ, hψ1⟩, hψ2⟩,
    simpa only [finset.mem_univ, finset.mem_insert, finset.mem_singleton, true_iff,
      @eq_comm _ ψ _, ← infinite_place_eq_iff, hφ2, coe_mk]
      using subtype.mk_eq_mk.mp (subtype.mk_eq_mk.mp hψ2.symm), },
end

end infinite_places

section classical_embeddings

open number_field.embeddings

variables {K : Type*} [field K] (K)

example : K →+* ({φ : K →+* ℂ // is_real φ} → ℝ) :=
pi.ring_hom (λ ⟨_, hφ⟩, real_embedding hφ)

example : K →+* ({φ : K →+* ℂ // is_complex φ} → ℂ) :=
pi.ring_hom (λ ⟨φ, _⟩, φ)

def ring_embedding :
  K →+* ({φ : K →+* ℂ // is_real φ} → ℝ) × ({φ : K →+* ℂ // is_complex φ} → ℂ) :=
ring_hom.prod (pi.ring_hom (λ ⟨_, hφ⟩, real_embedding hφ))
  (pi.ring_hom (λ ⟨φ, _⟩, φ))

def log_embedding :
  Kˣ → (infinite_places K → ℝ) :=
begin
  exact λ x ⟨w, _⟩, w x,
end

end classical_embeddings
