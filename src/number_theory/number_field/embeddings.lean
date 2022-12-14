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

variables {A : Type*} [normed_division_ring A] {K : Type*} [field K] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def number_field.place : absolute_value K ℝ :=
{ to_fun := norm ∘ φ,
  map_mul' := by simp only [function.comp_app, map_mul, norm_mul, eq_self_iff_true, forall_const],
  nonneg' := by simp only [norm_nonneg, forall_const],
  eq_zero' := by simp only [norm_eq_zero, map_eq_zero, forall_const, iff_self],
  add_le' := by simp only [function.comp_app, map_add, norm_add_le, forall_const], }

lemma number_field.norm_eq_place (x : K) : ‖φ x‖ = number_field.place φ x := by refl

end place

namespace number_field.complex_embeddings

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

instance {R S : Type*} [non_assoc_semiring S] [comm_semiring R] [star_ring R] :
  has_involutive_star (S →+* R) :=
{ to_has_star := { star := λ f, ring_hom.comp (star_ring_end R) f },
  star_involutive :=
    by { intro _, ext, simp only [ring_hom.coe_comp, function.comp_app, star_ring_end_self_apply] }}

/-- The conjugate of a complex embedding as a complex embedding. -/
def conjugate (φ : K →+* ℂ) : K →+* ℂ := ring_hom.has_involutive_star.star φ

@[simp]
lemma conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

lemma conjugate_conjugate_eq (φ : K →+* ℂ) :
  conjugate (conjugate φ) = φ := has_involutive_star.star_involutive φ

lemma place_conjugate_eq_place (φ : K →+* ℂ) (x : K) : place (conjugate φ) x = place φ x :=
by { simp only [place, conjugate_coe_eq, absolute_value.coe_mk, mul_hom.coe_mk, function.comp_app,
  norm_eq_abs, abs_conj] }

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
by { ext x, simp only [place, function.comp_apply, complex.norm_eq_abs, real.norm_eq_abs,
  ← real_embedding_eq_embedding hφ x, abs_of_real, absolute_value.coe_mk, mul_hom.coe_mk], }

lemma is_real_conjugate_iff {φ : K →+* ℂ} :
  is_real (conjugate φ) ↔ is_real φ := is_self_adjoint.star_iff

end number_field.complex_embeddings

section infinite_places

open number_field

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def number_field.infinite_places := { w : absolute_value K ℝ  // ∃ φ : K →+* ℂ, place φ = w}

instance [number_field K] : nonempty (number_field.infinite_places K) :=
begin
  rsuffices ⟨φ⟩ : nonempty (K →+* ℂ), { use ⟨place φ, ⟨φ, rfl⟩⟩, },
  rw [← fintype.card_pos_iff, embeddings.card K ℂ],
  exact finite_dimensional.finrank_pos,
end

variables {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def number_field.infinite_place (φ : K →+* ℂ) : number_field.infinite_places K :=
⟨place φ, ⟨φ, rfl⟩⟩

namespace number_field.infinite_places

open number_field

instance : has_coe_to_fun (infinite_places K) (λ _, K → ℝ) := { coe := λ w, w.1 }

lemma infinite_place_eq_place (φ : K →+* ℂ) (x : K) :
  (infinite_place φ) x = (place φ) x := by refl

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : infinite_places K) : K →+* ℂ := (w.2).some

lemma infinite_place_embedding_eq_infinite_place (w : infinite_places K) :
  infinite_place (embedding w) = w :=
by { ext, exact congr_fun (congr_arg coe_fn (w.2).some_spec) x, }

lemma place_embedding_eq_infinite_place (w : infinite_places K) (x : K) :
   place (embedding w) x = w x :=
begin
  rw ← infinite_place_eq_place,
  exact congr_fun (congr_arg coe_fn (infinite_place_embedding_eq_infinite_place w)) x,
end

lemma nonneg (w : infinite_places K) (x : K) : 0 ≤ w x := w.1.nonneg _

lemma eq_zero (w : infinite_places K) (x : K)  : w x = 0 ↔ x = 0 := w.1.eq_zero

@[simp]
lemma map_zero (w : infinite_places K) : w 0 = 0 := w.1.map_zero

@[simp]
lemma map_one (w : infinite_places K) : w 1 = 1 := w.1.map_one

@[simp]
lemma map_mul (w : infinite_places K) (x y : K) : w (x * y) = (w x) * (w y) := w.1.map_mul _ _

lemma infinite_place_conjugate_eq_infinite_place (φ : K →+* ℂ) :
  infinite_place (complex_embeddings.conjugate φ) = infinite_place φ :=
begin
  ext x,
  convert complex_embeddings.place_conjugate_eq_place φ x,
end

lemma eq_iff {φ ψ : K →+* ℂ} :
  infinite_place φ = infinite_place ψ ↔ φ = ψ ∨ complex_embeddings.conjugate φ = ψ :=
begin
  split,
  { -- The proof goes as follows: Prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform
    -- continuous, thus it is either the inclusion or the complex conjugation.
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
      exact congr_fun (congr_arg (λ  w : infinite_places K, (w : K → ℝ)) h₀) _, },
    cases (complex.uniform_continuous_ring_hom_eq_id_or_conj φ.field_range hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { exact congr_arg infinite_place h, },
    { rw ← infinite_place_conjugate_eq_infinite_place,
      exact congr_arg infinite_place h, }},
end

/-- An infinite place is real if it is defined by a real embedding. -/
def is_real (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, complex_embeddings.is_real φ ∧ infinite_place φ = w

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def is_complex (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, ¬ complex_embeddings.is_real φ ∧ infinite_place φ = w

lemma embedding_or_conjugate_eq_embedding_place (φ : K →+* ℂ) :
  φ = embedding (infinite_place φ) ∨ complex_embeddings.conjugate φ = embedding (infinite_place φ)
  := by simp only [← eq_iff, infinite_place_embedding_eq_infinite_place]

lemma embedding_eq_embedding_infinite_place_real {φ : K →+* ℂ} (h : complex_embeddings.is_real φ) :
  φ = embedding (infinite_place φ) :=
begin
  convert embedding_or_conjugate_eq_embedding_place φ,
  simp [complex_embeddings.is_real_iff.mp h, or_self],
end

lemma infinite_place_is_real_iff {w : infinite_places K} :
  is_real w ↔ complex_embeddings.is_real (embedding w) :=
begin
  split,
  { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
    rwa ← embedding_eq_embedding_infinite_place_real hφ, },
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma infinite_place_is_complex_iff {w : infinite_places K} :
  is_complex w  ↔ ¬ complex_embeddings.is_real (embedding w) :=
begin
  split,
    { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
      contrapose! hφ,
      cases eq_iff.mp (infinite_place_embedding_eq_infinite_place (infinite_place φ)),
      { rwa ← h, },
      { rw ← complex_embeddings.is_real_conjugate_iff at hφ,
        rwa ← h, }},
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma not_is_real_iff_is_complex {w : infinite_places K} :
  ¬ is_real w ↔ is_complex w :=
by rw [infinite_place_is_complex_iff, infinite_place_is_real_iff]

/-- For `w` a real infinite place, return the corresponding embedding as a morphism `K →+* ℝ`. -/
noncomputable def is_real.embedding {w : infinite_places K} (hw : is_real w) : K →+* ℝ :=
(infinite_place_is_real_iff.mp hw).embedding

lemma is_real.place_embedding_eq_infinite_place {w : infinite_places K} (hw : is_real w) (x : K):
  place (is_real.embedding hw) x = w x :=
begin
  rw [is_real.embedding, complex_embeddings.place_real_embedding_eq_place],
  exact place_embedding_eq_infinite_place _ _,
end

variable [number_field K]
variable (K)

open fintype

noncomputable instance : fintype (infinite_places K) := set.fintype_range _

lemma card_real_embeddings_eq :
  card {φ : K →+* ℂ // complex_embeddings.is_real φ} = card {w : infinite_places K // is_real w} :=
begin
  rw fintype.card_of_bijective (_ : function.bijective _),
  { exact λ φ, ⟨infinite_place φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  split,
  { rintros ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h,
    rw [subtype.mk_eq_mk, eq_iff, subtype.coe_mk, subtype.coe_mk,
      complex_embeddings.is_real_iff.mp hφ, or_self] at h,
    exact subtype.eq h, },
  { exact λ ⟨w, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩, ⟨⟨φ, hφ1⟩,
    by { simp only [hφ2, subtype.coe_mk], }⟩, }
end

lemma card_complex_embeddings_eq :
  card {φ : K →+* ℂ // ¬ complex_embeddings.is_real φ} =
  2 * card {w : infinite_places K // is_complex w} :=
begin
  let f : {φ : K →+* ℂ // ¬ complex_embeddings.is_real φ} → {w : infinite_places K // is_complex w},
  { exact λ φ, ⟨infinite_place φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  suffices :  ∀ w : {w // is_complex w}, card {φ // f φ = w} = 2,
  { rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
    conv { to_rhs, congr, skip, funext, rw ← this x, rw fintype.card, },
    simp_rw finset.card_eq_sum_ones,
    exact (fintype.sum_fiberwise f (function.const _ 1)).symm, },
  { rintros ⟨⟨w, hw⟩, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩,
    rw [fintype.card, finset.card_eq_two],
    refine ⟨⟨⟨φ, hφ1⟩, _⟩, ⟨⟨complex_embeddings.conjugate φ, _⟩, _⟩, ⟨_, _⟩⟩,
    { simpa only [f, hφ2], },
    { rwa iff.not complex_embeddings.is_real_conjugate_iff, },
    { simp only [f, ←hφ2, infinite_place_conjugate_eq_infinite_place, subtype.coe_mk], },
    { rwa [ne.def, subtype.mk_eq_mk, subtype.mk_eq_mk, ← ne.def, ne_comm], },
    ext ⟨⟨ψ, hψ1⟩, hψ2⟩,
    simpa only [finset.mem_univ, finset.mem_insert, finset.mem_singleton, true_iff, @eq_comm _ ψ _,
      ← eq_iff, hφ2] using subtype.mk_eq_mk.mp hψ2.symm, },
end

end number_field.infinite_places

end infinite_places

section canonical_embedding

open number_field number_field.infinite_places

variables (K : Type*) [field K]

-- TODO. see if you can remove that
localized "notation `E` :=
  ({w : infinite_places K // is_real w} → ℝ) ×
  ({w : infinite_places K // is_complex w} → ℂ)"
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
  obtain ⟨w⟩ := infinite_places.nonempty K,
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

lemma eval_at_real_infinite_place {w : infinite_places K} (hw : is_real w) (x : K) :
  (number_field.canonical_embedding K x).1 ⟨w, hw⟩ = hw.embedding x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma eval_at_complex_infinite_place {w : infinite_places K} (hw : is_complex w) (x : K) :
  (number_field.canonical_embedding K x).2 ⟨w, hw⟩ = embedding w x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma nnnorm_at_infinite_place (w : infinite_places K) (x : K) :
  ‖(canonical_embedding K) x‖₊ = finset.univ.sup (λ w : infinite_places K, ⟨w x, nonneg w x⟩) :=
begin
  rw prod.nnnorm_def',
  rw pi.nnnorm_def,
  rw pi.nnnorm_def,
  have := λ w : { w : infinite_places K // w.is_real }, eval_at_real_infinite_place w.prop x,
  simp_rw subtype.coe_eta at this,
  simp_rw this,
  have := λ w : { w : infinite_places K // w.is_complex }, eval_at_complex_infinite_place w.prop x,
  simp_rw subtype.coe_eta at this,
  simp_rw this,

  have : {w : infinite_places K | is_real w}.to_finset ∪
    {w : infinite_places K | is_complex w}.to_finset = finset.univ,
  { ext w,
    split,
    { simp only [finset.mem_univ, implies_true_iff], },
    { intro _,
      by_cases hw : is_real w,
      { refine finset.mem_union_left _ _,
        rw set.mem_to_finset,
        rwa set.mem_set_of_eq, },
      { refine finset.mem_union_right _ _,
        rw set.mem_to_finset,
        rw set.mem_set_of_eq,
        rwa ← not_is_real_iff_is_complex, },
    },
  },

  rw ← this,
  rw finset.sup_union,
  rw sup_eq_max,


  refine congr_arg2 _ _ _,

  { let f := function.embedding.subtype (λ w : infinite_places K, is_real w),
    convert (finset.univ.sup_map f (λ (w : infinite_places K), (⟨w x, w.nonneg x⟩ : nnreal))).symm,
    ext w,
    simp only [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk],
    rw number_field.norm_eq_place,
    rw is_real.place_embedding_eq_infinite_place, },
  { let f := function.embedding.subtype (λ w : infinite_places K, is_complex w),
    convert (finset.univ.sup_map f (λ (w : infinite_places K), (⟨w x, w.nonneg x⟩ : nnreal))).symm,
    ext w,
    simp only [function.embedding.coe_subtype, coe_nnnorm, subtype.coe_mk],
    rw number_field.norm_eq_place,
    rw place_embedding_eq_infinite_place,
  }
end

lemma le_of_le {B : ℝ} {x : K} :
  ‖(canonical_embedding K) x‖ ≤ B ↔ ∀ w : infinite_places K, w x ≤ B :=
begin
  obtain hB | hB := lt_or_le B 0,
  { obtain ⟨w⟩ := infinite_places.nonempty K,
    split,
    { intro h,
      have : 0 ≤ ‖(canonical_embedding K) x‖ := norm_nonneg _,
      exfalso,
      linarith, },
    { intro h,
      have := infinite_places.nonneg w x,
      specialize h w,
      exfalso,
      linarith, }},
  { have := λ w : infinite_places K, nnnorm_at_infinite_place w x,
    lift B to nnreal using hB,
    rw ← coe_nnnorm,
    simp only [*, forall_const, finset.mem_univ, nnreal.coe_le_coe, finset.sup_le_iff] at *,
    refl, }
end

example (B : set E) (hB0 : (0 : E) ∈ B) (hB : metric.bounded B) :
  (B ∩ ((canonical_embedding K) '' number_field.ring_of_integers K)).finite :=
begin
  obtain ⟨C, hC⟩ := hB,
  obtain hCpos | hCpos := lt_or_le C 0,
  { suffices : B = ∅,
    { exact set.finite.inf_of_left (by simp only [this, set.finite_empty]) _},
    refine set.ext _,
    simp only [set.mem_empty_iff_false, iff_false],
    intros x hx,
    specialize hC 0 hB0 x hx,
    have := le_trans dist_nonneg hC,
    linarith, },
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
          eq_self_iff_true, and_self, _root_.map_zero], },
    },
    { rintros ⟨x, ⟨hx1, hx2⟩⟩,
      by_cases h : x = 0,
      { use 0,
        split,
        { simp only [number_field.mem_ring_of_integers, is_integral_zero], },
        { intro w,
          simp only [*, complex.norm_eq_abs, _root_.map_zero],
          },
        { dsimp,
          simp [*, _root_.map_zero, dif_pos], }},
      { obtain ⟨a, ⟨ha, rfl⟩⟩ := hx2,
        use a,
        split,
        { exact ha, },
        { specialize hC (canonical_embedding K a) hx1,
          have := dist_zero_right (canonical_embedding K a),
          rw dist_comm at hC,
          rw this at hC,
          rw le_of_le at hC,
          intro φ,
          specialize hC (infinite_place φ),
          exact hC,

           },
        { dsimp [*, dist_zero_right, set_like.mem_coe, _root_.map_zero, eq_self_iff_true, and_self],
          simp only [*, dif_pos], }}}},
end

end number_field.canonical_embedding

end canonical_embedding
