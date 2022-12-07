/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import number_theory.number_field.basic
import topology.algebra.polynomial
import topology.instances.complex
import analysis.special_functions.log.basic
import analysis.complex.polynomial

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

lemma place.nonneg (x : K) : 0 ≤ place φ x := by simp only [place, norm_nonneg]

@[simp]
lemma place.eq_zero_iff (x : K) : place φ x = 0 ↔ x = 0 :=
by simp only [place, norm_eq_zero, map_eq_zero]

@[simp]
lemma place.map_zero : place φ 0 = 0 :=
by simp only [place, function.comp_app, map_zero, norm_zero]

@[simp]
lemma place.map_one : place φ 1 = 1 :=
by simp only [place, function.comp_app, map_one, norm_one]

@[simp]
lemma place.map_inv (x : K) : place φ (x⁻¹) = (place φ x)⁻¹ :=
by simp only [place, function.comp_app, norm_inv, map_inv₀]

@[simp]
lemma place.map_mul (x y : K) : place φ (x * y) = (place φ x) * (place φ y) :=
by simp only [place, function.comp_app, map_mul, norm_mul]

lemma place.add_le (x y : K) : place φ (x + y) ≤ (place φ x) + (place φ y) :=
by simpa only [place, function.comp_app, map_add] using norm_add_le _ _

end place

section complex_embeddings

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
def conjugate (φ : K →+* ℂ) : K →+* ℂ := ring_hom.comp conj_ae.to_ring_equiv.to_ring_hom φ

@[simp]
lemma conjugate_coe_eq (φ : K →+* ℂ) : (conjugate φ : K → ℂ) = conj ∘ φ := rfl

lemma conjugate_place_eq (φ : K →+* ℂ) : place (conjugate φ) = place φ :=
by { ext1, simp only [place, conjugate_coe_eq, function.comp_app, norm_eq_abs, abs_conj] }

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
    cases (complex.uniform_continuous_ring_hom_eq_id_or_conj φ.field_range hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { ext x, convert congr_arg complex.abs (ring_hom.congr_fun h x), },
    { ext x, rw [← h, conjugate_place_eq], }},
end

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
def is_real (φ : K →+* ℂ): Prop := conjugate φ = φ

/-- A embedding into `ℂ` is complex if it is not fixed by complex conjugation. -/
def is_complex (φ : K →+* ℂ): Prop := conjugate φ ≠ φ

lemma not_is_real_iff_is_complex {φ : K →+* ℂ} :
  ¬ is_real φ ↔ is_complex φ := by rw [is_real, is_complex]

/-- A real embedding as a ring hom `K →+* ℝ` . -/
def real_embedding {φ : K →+* ℂ} (hφ : is_real φ) : K →+* ℝ :=
{ to_fun := λ x, (φ x).re,
  map_one' := by simp only [map_one, one_re],
  map_mul' := by simp only [complex.eq_conj_iff_im.mp (ring_hom.congr_fun hφ _), map_mul, mul_re,
  mul_zero, tsub_zero, eq_self_iff_true, forall_const],
  map_zero' := by simp only [map_zero, zero_re],
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const], }

lemma real_embedding_eq_embedding {φ : K →+* ℂ} (hφ : is_real φ) (x : K) :
  (real_embedding hφ x : ℂ) = φ x :=
begin
  ext, { refl, },
  { rw [of_real_im, eq_comm, ← complex.eq_conj_iff_im],
    rw is_real at hφ,
    exact ring_hom.congr_fun hφ x, },
end

lemma place_real_embedding_eq_place {φ : K →+* ℂ} (hφ : is_real φ) :
  place (real_embedding hφ) = place φ :=
by { ext x, simp only [place, function.comp_apply, complex.norm_eq_abs, real.norm_eq_abs,
  ← real_embedding_eq_embedding hφ x, abs_of_real] }

lemma conjugate_conjugate (φ : K →+* ℂ) :
  conjugate (conjugate φ) = φ :=
  by { ext1, simp only [conjugate_coe_eq, function.comp_app, star_ring_end_self_apply], }

lemma conjugate_is_real_iff (φ : K →+* ℂ) :
  is_real (conjugate φ) ↔ is_real φ := by simp only [is_real, conjugate_conjugate, eq_comm]

lemma conjugate_is_complex_iff (φ : K →+* ℂ) :
  is_complex (conjugate φ) ↔ is_complex φ := by simp only [is_complex, conjugate_conjugate, ne_comm]

end complex_embeddings

end number_field.embeddings

section infinite_places

open number_field

-- TODO. figure out naming and order of results and variables and which are useful...

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to an embedding into 'ℂ'. -/
def number_field.infinite_places := set.range (λ φ : K →+* ℂ, embeddings.place φ)

namespace number_field.infinite_places
open number_field fintype

instance : has_coe_to_fun (infinite_places K) (λ _, K → ℝ) := { coe := λ w, w.1 }

--- Golf
lemma nonempty [number_field K] : nonempty (infinite_places K) :=
begin
  have t1 := embeddings.card K ℂ,
  have t2 : 0 < finite_dimensional.finrank ℚ K, { exact finite_dimensional.finrank_pos, },
  rw ← t1 at t2,
  rw fintype.card at t2,
  rw finset.card_pos at t2,
  obtain ⟨φ, _⟩ := t2,
  use ⟨embeddings.place φ, ⟨φ, rfl⟩⟩,
end

variable {K}

@[simp]
lemma coe_to_fun (w : infinite_places K) (x : K) : (w : K → ℝ) x = w.1 x := by refl

/-- Return the infinite place defined by an embedding `φ`. -/
noncomputable def place (φ : K →+* ℂ) : infinite_places K :=
⟨embeddings.place φ, ⟨φ, rfl⟩⟩

lemma infinite_place_eq_place {φ : K →+* ℂ} :
  (place φ : K → ℝ) = embeddings.place φ := by refl

/-- Give an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : infinite_places K) : K →+* ℂ := Exists.some w.2

lemma place_embedding_eq (w : infinite_places K) : embeddings.place (embedding w) = (w : K → ℝ) :=
Exists.some_spec w.2

lemma infinite_place_embedding_eq (w : infinite_places K) (x : K) : place (embedding w) x = w x :=
by { exact congr_fun (place_embedding_eq w) x, }

@[simp]
lemma eq_zero_iff (w : infinite_places K) (x : K)  : w x = 0 ↔ x = 0 :=
by simp only [← place_embedding_eq, embeddings.place.eq_zero_iff]

@[simp]
lemma map_zero (w : infinite_places K) : w 0 = 0 :=
by simp only [← place_embedding_eq, embeddings.place.map_zero]

@[simp]
lemma map_one (w : infinite_places K) : w 1 = 1 :=
by simp only [← place_embedding_eq, embeddings.place.map_one]

@[simp]
lemma map_inv (w : infinite_places K) (x : K) : w (x⁻¹) = (w x)⁻¹ :=
by simp only [← place_embedding_eq, embeddings.place.map_inv]

@[simp]
lemma map_mul (w : infinite_places K) (x y : K) : w (x * y) = (w x) * (w y) :=
by simp only [← place_embedding_eq, embeddings.place.map_mul]

/-- An infinite place is real if it is defined by a real embedding. -/
def is_real (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, embeddings.is_real φ ∧ embeddings.place φ = w

/-- An infinite place is complex if it is defined by a complex embedding. -/
def is_complex (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, embeddings.is_complex φ ∧ embeddings.place φ = w

lemma embedding_or_conjugate_eq_embedding_place (φ : K →+* ℂ) :
  φ = embedding (place φ) ∨ embeddings.conjugate φ = embedding (place φ) :=
by simpa only [← embeddings.infinite_place_eq_iff, place_embedding_eq]

lemma embedding_eq_embedding_place_real {φ : K →+* ℂ} (h : embeddings.is_real φ) :
  φ = embedding (place φ) :=
begin
  rw embeddings.is_real at h,
  convert embedding_or_conjugate_eq_embedding_place φ,
  simp only [h, or_self],
end

lemma embedding_is_real_iff_place_is_real {w : infinite_places K} :
  embeddings.is_real (embedding w) ↔ is_real w :=
begin
  split,
  { exact λ h, ⟨embedding w, h, place_embedding_eq w⟩, },
  { rintro ⟨_, ⟨h1, h2⟩⟩,
--    have := infinite_place_eq_place,
    -- rwa [←  infinite_place_eq_place.mp h2, ← embedding_eq_embedding_place_real h1],
    sorry,
    }
end

lemma embedding_is_complex_iff_place_is_complex {w : infinite_places K} :
  embeddings.is_complex (embedding w) ↔ is_complex w :=
begin
  split,
  { exact λ h, ⟨embedding w, h, place_embedding_eq w⟩, },
  { rintro ⟨φ, ⟨hφ1, hφ2⟩⟩,
    sorry,
    --  rw [← iff_place.mpr hφ2],
    -- cases embedding_or_conjugate_eq_embedding_place φ,
    -- { rwa ← h, },
    -- { rwa [← h, embeddings.conjugate_is_complex_iff], }
    }
end

lemma not_is_real_iff_is_complex {w : infinite_places K} :
  ¬ is_real w ↔ is_complex w :=
begin
  rw [← embedding_is_real_iff_place_is_real, ← embedding_is_complex_iff_place_is_complex],
  exact embeddings.not_is_real_iff_is_complex,
end

variable [number_field K]
variable (K)

noncomputable instance : fintype (infinite_places K) := set.fintype_range _

lemma card_real_embeddings_eq :
  card {φ : K →+* ℂ // embeddings.is_real φ} = card {w : infinite_places K // is_real w} :=
begin
  rw fintype.card_of_bijective (_ : function.bijective _),
  exact λ φ, ⟨⟨embeddings.place φ.val, ⟨φ, rfl⟩⟩, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩,
  split,
  { rintros ⟨_, hφ⟩ _ h,
    rw embeddings.is_real at hφ,
    rwa [subtype.mk_eq_mk, subtype.mk_eq_mk, embeddings.infinite_place_eq_iff, hφ, or_self,
      ← subtype.ext_iff_val] at h, },
  { exact λ ⟨w, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩, ⟨⟨φ, hφ1⟩,
    by { simpa only [subtype.mk_eq_mk, subtype.ext_iff, hφ1, hφ2, subtype.coe_mk], }⟩, }
end

lemma card_complex_embeddings_eq :
  card {φ : K →+* ℂ // embeddings.is_complex φ} = 2 * card {w : infinite_places K // is_complex w}
  :=
begin
  let f : {φ : K →+* ℂ // embeddings.is_complex φ} → {w : infinite_places K // is_complex w},
  { exact λ φ, ⟨⟨embeddings.place φ.val, ⟨φ, rfl⟩⟩, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  suffices :  ∀ w : {w // is_complex w}, card {φ // f φ = w} = 2,
  { rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
    conv { to_rhs, congr, skip, funext, rw ← this x, rw fintype.card, },
    simp_rw finset.card_eq_sum_ones,
    exact (fintype.sum_fiberwise f (function.const _ 1)).symm, },
  { rintros ⟨⟨w, hw⟩, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩,
    rw [fintype.card, finset.card_eq_two],
    refine ⟨⟨⟨φ, hφ1⟩, _⟩, ⟨⟨embeddings.conjugate φ,
      (embeddings.conjugate_is_complex_iff φ).mpr hφ1⟩, _⟩, ⟨_, _⟩⟩,
    { simpa only [f, hφ2], },
    { simpa only [f, hφ2, embeddings.conjugate_place_eq], },
    { exact subtype.ne_of_val_ne (subtype.ne_of_val_ne hφ1.symm), },
    ext ⟨⟨ψ, hψ1⟩, hψ2⟩,
    simpa only [finset.mem_univ, finset.mem_insert, finset.mem_singleton, true_iff,
      @eq_comm _ ψ _, ← embeddings.infinite_place_eq_iff, hφ2]
      using subtype.mk_eq_mk.mp (subtype.mk_eq_mk.mp hψ2.symm), },
end

end number_field.infinite_places

end infinite_places

section classical_embeddings

open_locale nnreal

open number_field

variables (K : Type*) [field K]

noncomputable def log_embedding : Kˣ → (infinite_places K → ℝ) := λ x w, real.log (w x)

lemma log_embedding.map_one :
  log_embedding K 1 = 0 :=
by simpa only [log_embedding, infinite_places.map_one, real.log_one, units.coe_one]

lemma log_embedding.map_inv (x : Kˣ) :
  log_embedding K x⁻¹ = - log_embedding K x :=
by simpa only [log_embedding, infinite_places.map_inv, real.log_inv, units.coe_inv]

lemma log_embedding.map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, infinite_places.map_mul, real.log_mul, units.coe_mul, ne.def,
  infinite_places.eq_zero_iff, units.ne_zero, not_false_iff]

noncomputable def canonical_embedding :
  K →+* ({w // infinite_places.is_real w} → ℝ) × ({w // infinite_places.is_complex w} → ℂ) :=
ring_hom.prod
  (pi.ring_hom (λ ⟨_, hw⟩,
    embeddings.real_embedding (infinite_places.embedding_is_real_iff_place_is_real.mpr hw)))
  (pi.ring_hom (λ ⟨w, _⟩, infinite_places.embedding w))

localized "notation `E` :=
  ({w : infinite_places K // infinite_places.is_real w} → ℝ) ×
  ({w : infinite_places K // infinite_places.is_complex w} → ℂ)"
  in embeddings

variables [number_field K]

lemma canonical_embedding_injective :
  function.injective (canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  use [0, 1],
  obtain ⟨w⟩ := infinite_places.nonempty K,
  intro h,
  by_cases hw : infinite_places.is_real w,
  { have := congr_arg (λ x : E, x.1) h,
    have t1 := congr_fun this ⟨w, hw⟩,
    exact zero_ne_one t1, },
  { replace hw := infinite_places.not_is_real_iff_is_complex.mp hw,
    have := congr_arg (λ x : E, x.2) h,
    have t1 := congr_fun this ⟨w, hw⟩,
    exact zero_ne_one t1, }
end

lemma canonical_embedding_eval_real
  {w : infinite_places K} (hw : infinite_places.is_real w) (x : K) :
  ‖((canonical_embedding K) x).1 ⟨w, hw⟩‖ = w x :=
begin
  have t2 := infinite_places.infinite_place_embedding_eq w x,
  rw ← t2,
  rw ← infinite_places.embedding_is_real_iff_place_is_real at hw,
  have t1 := embeddings.place_real_embedding_eq_place hw,
  rw infinite_places.infinite_place_eq_place,
  rw ← t1,
  refl,
end

lemma canonical_embedding_eval_complex
  {w : infinite_places K} (hw : infinite_places.is_complex w) (x : K) :
  ‖((canonical_embedding K) x).2 ⟨w, hw⟩‖ = w x :=
begin
  have t2 := infinite_places.infinite_place_embedding_eq w x,
  rw ← t2,
  refl,
end

lemma canonical_embedding.le_of_le {B : ℝ} {x : K} :
  ‖canonical_embedding K x‖ ≤ B ↔ ∀ w : infinite_places K, w x ≤ B :=
begin
  by_cases hB : 0 ≤ B,
  { lift B to ℝ≥0 using hB,
    rw prod.norm_def,
    rw pi.norm_def,
    rw pi.norm_def,
    rw max_le_iff,
    simp_rw nnreal.coe_le_coe,
    simp_rw finset.sup_le_iff,
    simp only [finset.mem_univ, forall_true_left],
    split,
    { intros h w,
      by_cases hw : infinite_places.is_real w,
      { have t1 := canonical_embedding_eval_real K hw x,
        rw ← t1,
        exact h.1 ⟨w , hw⟩, },
      { rw infinite_places.not_is_real_iff_is_complex at hw,
        have t2 := canonical_embedding_eval_complex K hw x,
        rw ← t2,
        exact h.2 ⟨w , hw⟩, }},
    { intro h,
      split,
      { rintros ⟨w, hw⟩,
        specialize h w,
        have t1 := canonical_embedding_eval_real K hw x,
        rw ← t1 at h,
        simp_rw ← nnreal.coe_le_coe,
        exact h, },
      { rintros ⟨w, hw⟩,
        specialize h w,
        have t1 := canonical_embedding_eval_complex K hw x,
        rw ← t1 at h,
        simp_rw ← nnreal.coe_le_coe,
        exact h, }}},
  { sorry, },
end

example (B : set E) (hB0 : (0 : E) ∈ B) (hB : metric.bounded B) :
  (B ∩ ((canonical_embedding K) '' number_field.ring_of_integers K)).finite :=
begin
  obtain ⟨C, hC⟩ := hB,
  obtain hCpos | hCpos := lt_or_le C 0,
  { suffices : B = ∅,
    { exact set.finite.inf_of_left (by simp only [this, set.finite_empty]) _},
    refine set.ext _,

    sorry,
     },


  { specialize hC 0 hB0,
    rw ← set.finite_coe_iff,
    let A := { x : K | is_integral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ C},
    refine finite.of_surjective _ _,
    use A,
    { have := embeddings.finite_of_norm_le K ℂ C,
      rw set.finite_coe_iff,
      convert this, },
    { rintros ⟨a, ⟨ha1, ha2⟩⟩,
      let x := canonical_embedding K a,
      by_cases h : x ∈ B,
      { use x,
        refine ⟨h, _⟩,
        use a,
        split,
        rw ← number_field.mem_ring_of_integers at ha1,
        exact ha1,
        simp only [x], },
      { use 0,
        refine ⟨_, _⟩,
        exact hB0,
        use 0,
        simp only [number_field.mem_ring_of_integers, is_integral_zero, set_like.mem_coe,
          map_zero, eq_self_iff_true, and_self], },
    },
    { rintros ⟨x, ⟨hx1, hx2⟩⟩,
      by_cases h : x = 0,
      { use 0,
        split,
        { simp only [number_field.mem_ring_of_integers, is_integral_zero], },
        { intro w,
          simp only [*, map_zero, complex.norm_eq_abs],
          },
        { dsimp only,
          simp only [*, map_zero, dif_pos], }},
      { obtain ⟨a, ⟨ha, rfl⟩⟩ := hx2,
        use a,
        split,
        { exact ha, },
        { specialize hC (canonical_embedding K a) hx1,
          have := dist_zero_right (canonical_embedding K a),
          rw dist_comm at hC,
          rw this at hC,
          rw canonical_embedding.le_of_le at hC,
          intro φ,
          specialize hC (infinite_places.place φ),
          exact hC,

           },
        { dsimp [*, dist_zero_right, set_like.mem_coe, map_zero, eq_self_iff_true, and_self],
          simp only [*, dif_pos], }}}},
end

end classical_embeddings

section lattice

variables (K : Type*) [field K] [number_field K]

localized "notation `Λ` := (canonical_embedding K) '' (number_field.ring_of_integers K)"
in embeddings

end lattice
