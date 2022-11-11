/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import analysis.normed_space.star.gelfand_duality
import topology.algebra.star_subalgebra

open_locale pointwise ennreal nnreal complex_order

open weak_dual weak_dual.character_space elemental_star_algebra

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables (a : A) [is_star_normal a] (S : star_subalgebra ℂ A)

noncomputable instance : normed_comm_ring (elemental_star_algebra ℂ a) :=
{ mul_comm := mul_comm, .. subring_class.to_normed_ring (elemental_star_algebra ℂ a) }

/- This lemma is used in the proof of `star_subalgebra.is_unit_of_is_unit_of_is_star_normal`,
which in turn is the key to spectral permanence `star_subalgebra.spectrum_eq`, which is itself
necessary for the continuous functional calculus. Using the continuous functional calculus, this
lemma can be superseded by one that omits the `is_star_normal` hypothesis. -/
lemma spectrum_star_mul_self_of_is_star_normal :
  spectrum ℂ (star a * a) ⊆ set.Icc (0 : ℂ) (∥star a * a∥) :=
begin
  -- this instance should be found automatically, but without providing it Lean goes on a wild
  -- goose chase when trying to apply `spectrum.gelfand_transform_eq`.
  letI := star_subalgebra.to_normed_algebra (elemental_star_algebra ℂ a),
  unfreezingI { rcases subsingleton_or_nontrivial A },
  { simp only [spectrum.of_subsingleton, set.empty_subset] },
  { set a' : elemental_star_algebra ℂ a := ⟨a, self_mem ℂ a⟩,
    refine (spectrum.subset_star_subalgebra (star a' * a')).trans _,
    rw [←spectrum.gelfand_transform_eq (star a' * a'), continuous_map.spectrum_eq_range],
    rintro - ⟨φ, rfl⟩,
    rw [gelfand_transform_apply_apply ℂ _ (star a' * a') φ, map_mul φ, map_star φ],
    rw [←star_ring_end_apply, mul_comm],
    rw [is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def', sq, ←cstar_ring.norm_star_mul_self, ←map_star,
      ←map_mul],
    exact ⟨complex.zero_le_real.2 (norm_nonneg _),
      complex.real_le_real.2 (alg_hom.norm_apply_le_self φ (star a' * a'))⟩, }
end

variables {a}

/-- This is the key lemma on the way to establishing spectral permanence for C⋆-algebras, which is
established in `star_subalgebra.spectrum_eq`. This lemma is superseded by
`star_subalgebra.coe_is_unit`, which does not require an `is_star_normal` hypothesis and holds for
any closed star subalgebra. -/
lemma is_unit_of_is_unit_of_is_star_normal (h : is_unit a) :
  is_unit (⟨a, self_mem ℂ a⟩ : elemental_star_algebra ℂ a) :=
begin
  nontriviality A,
  set a' : elemental_star_algebra ℂ a := ⟨a, self_mem ℂ a⟩,
  suffices : is_unit (star a' * a'),
  { exact (is_unit.mul_iff.1 this).2 },
  replace h := (show commute (star a) a, from star_comm_self' a).is_unit_mul_iff.2 ⟨h.star, h⟩,
  have h₁ : (∥star a * a∥₊ : ℂ) ≠ 0,
  { simpa only [coe_nnnorm, coe_coe, complex.of_real_eq_zero, ne.def]
    using norm_ne_zero_iff.2 h.ne_zero },
  set u : units (elemental_star_algebra ℂ a) :=
    units.map (algebra_map ℂ (elemental_star_algebra ℂ a)).to_monoid_hom (units.mk0 _ h₁),
  refine ⟨u.unit_of_nearby _ _, rfl⟩,
  simp only [complex.abs_of_real, map_inv₀, units.coe_map, units.coe_inv, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, units.coe_mk0, units.coe_map_inv, norm_algebra_map', coe_nnnorm,
    inv_inv, complex.norm_eq_abs, abs_norm_eq_norm, subtype.val_eq_coe, coe_coe],
  have h₂ : ∀ z ∈ spectrum ℂ (algebra_map ℂ A (∥star a * a∥) - star a * a), ∥z∥₊ < ∥star a * a∥₊,
  { intros z hz,
    rw [←spectrum.singleton_sub_eq, set.singleton_sub] at hz,
    have h₃ : z ∈ set.Icc (0 : ℂ) (∥star a * a∥),
    { replace hz := set.image_subset _ (spectrum_star_mul_self_of_is_star_normal a) hz,
      rwa [set.image_const_sub_Icc, sub_self, sub_zero] at hz },
    refine lt_of_le_of_ne (complex.real_le_real.1 $ complex.eq_coe_norm_of_nonneg h₃.1 ▸ h₃.2) _,
    { intros hz',
      replace hz' := congr_arg (λ (x : ℝ≥0), ((x : ℝ) : ℂ)) hz',
      simp only [coe_nnnorm] at hz',
      rw ←complex.eq_coe_norm_of_nonneg h₃.1 at hz',
      obtain ⟨w, hw₁, hw₂⟩ := hz,
      refine (spectrum.zero_not_mem_iff ℂ).mpr h _,
      rw [hz', sub_eq_self] at hw₂,
      rwa hw₂ at hw₁ } },
  { exact ennreal.coe_lt_coe.1
    (calc (∥star a' * a' - algebra_map ℂ _ (∥star a * a∥)∥₊ : ℝ≥0∞)
        = ∥algebra_map ℂ A (∥star a * a∥) - star a * a∥₊ : by { rw [←nnnorm_neg, neg_sub], refl }
    ... = spectral_radius ℂ (algebra_map ℂ A (∥star a * a∥) - star a * a)
        : begin
            refine (is_self_adjoint.spectral_radius_eq_nnnorm _).symm,
            rw [is_self_adjoint, star_sub, star_mul, star_star, ←algebra_map_star_comm,
              is_R_or_C.star_def, is_R_or_C.conj_of_real],
          end
    ... < ∥star a * a∥₊ : spectrum.spectral_radius_lt_of_forall_lt _ h₂ ) },
end

/-- For `a : A` which is invertible in `A`, the inverse lies in any unital C⋆-subalgebra `S`
containing `a`. -/
lemma is_unit_coe_inv_mem {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) {x : A}
  (h : is_unit x) (hxS : x ∈ S) : ↑h.unit⁻¹ ∈ S :=
begin
  have hx := h.star.mul h,
  suffices this : (↑hx.unit⁻¹ : A) ∈ S,
  { rw [←one_mul (↑h.unit⁻¹ : A), ←hx.unit.inv_mul, mul_assoc, is_unit.unit_spec, mul_assoc,
      h.mul_coe_inv, mul_one],
    exact mul_mem this (star_mem hxS) },
  refine le_of_is_closed_of_mem ℂ hS (mul_mem (star_mem hxS) hxS) _,
  haveI := (is_self_adjoint.star_mul_self x).is_star_normal,
  have hx' := is_unit_of_is_unit_of_is_star_normal hx,
  convert (↑hx'.unit⁻¹ : elemental_star_algebra ℂ (star x * x)).prop using 1,
  exact left_inv_eq_right_inv hx.unit.inv_mul (congr_arg coe hx'.unit.mul_inv),
end

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
lemma coe_is_unit {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) {x : S} :
  is_unit (x : A) ↔ is_unit x :=
begin
  refine ⟨λ hx, ⟨⟨x, ⟨(↑hx.unit⁻¹ : A), is_unit_coe_inv_mem hS hx x.prop⟩, _, _⟩, rfl⟩,
    λ hx, hx.map S.subtype⟩,
  exacts [subtype.coe_injective hx.mul_coe_inv, subtype.coe_injective hx.coe_inv_mul],
end

/-- **Spectral permanence**. The spectrum of an element is invariant of the `star_subalgebra` in
which it is contained. -/
lemma spectrum_eq {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) (x : S) :
  spectrum ℂ x = spectrum ℂ (x : A) :=
set.ext $ λ _, not_iff_not.2 (coe_is_unit hS).symm

variables (a)


-- without these instances Lean times out
noncomputable instance : normed_algebra ℂ (elemental_star_algebra ℂ a) :=
star_subalgebra.to_normed_algebra (elemental_star_algebra ℂ a)

noncomputable instance : module ℂ (elemental_star_algebra ℂ a) :=
normed_space.to_module

/-- The natrual map from `character_space ℂ (elemental_star_algebra ℂ a)` to `spectrum ℂ a` given
by evaluating `φ` at `a`. This is essentially just evaluation of the `gelfand_transform` of `a`,
but because we want something in `spectrum ℂ a`, as opposed to
`spectrum ℂ ⟨a, elemental_star_algebra.self_mem ℂ a⟩` there is slightly more work to do. -/
@[simps]
noncomputable def elemental_star_algebra.character_space_to_spectrum :
  C(character_space ℂ (elemental_star_algebra ℂ a), spectrum ℂ a) :=
{ to_fun := λ φ,
  { val := φ ⟨a, self_mem ℂ a⟩,
    property := by simpa only [spectrum_eq (elemental_star_algebra.is_closed ℂ a) ⟨a, self_mem ℂ a⟩]
      using alg_hom.apply_mem_spectrum φ (⟨a, self_mem ℂ a⟩) },
  continuous_to_fun := continuous_induced_rng.2 (map_continuous $
    gelfand_transform ℂ (elemental_star_algebra ℂ a) ⟨a, self_mem ℂ a⟩) }

lemma elemental_star_algebra.character_space_to_spectrum_bijective :
  function.bijective (elemental_star_algebra.character_space_to_spectrum a) :=
begin
  refine ⟨λ φ ψ h, star_alg_hom_class_ext ℂ (map_continuous φ) (map_continuous ψ)
    (by simpa only [elemental_star_algebra.character_space_to_spectrum, subtype.mk_eq_mk,
      continuous_map.coe_mk] using h), _⟩,
  rintros ⟨z, hz⟩,
  set a' : elemental_star_algebra ℂ a := ⟨a, self_mem ℂ a⟩,
  rw [(show a = a', from rfl), ←spectrum_eq (elemental_star_algebra.is_closed ℂ a) a',
    ←spectrum.gelfand_transform_eq a', continuous_map.spectrum_eq_range] at hz,
  obtain ⟨φ, rfl⟩ := hz,
  exact ⟨φ, rfl⟩,
end

/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
noncomputable def character_space_elemental_algebra_homeo :
  character_space ℂ (elemental_star_algebra ℂ a) ≃ₜ spectrum ℂ a :=
@continuous.homeo_of_equiv_compact_to_t2 _ _ _ _ _ _
  (equiv.of_bijective (elemental_star_algebra.character_space_to_spectrum a)
    (elemental_star_algebra.character_space_to_spectrum_bijective a))
    (map_continuous $ elemental_star_algebra.character_space_to_spectrum a)

/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `star_alg_equiv` from the complex-valued continuous
funcitons on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(continuous_map.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuous_functional_calculus_map_id`. As such it extends the polynomial functional calculus. -/
noncomputable def continuous_functional_calculus :
  C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a :=
((character_space_elemental_algebra_homeo a).comp_star_alg_equiv' ℂ ℂ).trans
  (gelfand_star_transform (elemental_star_algebra ℂ a)).symm

lemma continuous_functional_calculus_map_id :
  continuous_functional_calculus a ((continuous_map.id ℂ).restrict (spectrum ℂ a)) =
    ⟨a, self_mem ℂ a⟩ :=
star_alg_equiv.symm_apply_apply _ _
