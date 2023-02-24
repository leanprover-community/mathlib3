/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import analysis.normed_space.star.gelfand_duality
import topology.algebra.star_subalgebra

/-! # Continuous functional calculus

In this file we construct the `continuous_functional_calculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a` which sends the (restriction of) the
identity map `continuous_map.id ℂ` to the (unique) preimage of `a` under the coercion of
`elemental_star_algebra ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `polynomial.aeval`).

For any continuous function `f : spectrum ℂ a →  ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

This file also includes a proof of the **spectral permanence** theorem for (unital) C⋆-algebras
(see `star_subalgebra.spectrum_eq`)

## Main definitions

* `continuous_functional_calculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a`: this
  is the composition of the inverse of the `gelfand_star_transform` with the natural isomorphism
  induced by the homeomorphism `elemental_star_algebra.character_space_homeo`.
* `elemental_star_algebra.character_space_homeo :
  `character_space ℂ (elemental_star_algebra ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.

## Main statements

* `star_subalgebra.coe_is_unit`: for `x : S` in a C⋆-subalgebra `S` of `A`, then `↑x : A` is a unit
  if and only if `x` is a unit.
* `star_subalgebra.spectrum_eq`: **spectral_permanence** for `x : S`, where `S` is a C⋆-subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## Notes

The result we have established here is the strongest possible, but it is likely not the version
which will be most useful in practice. Future work will include developing an appropriate API for
the continuous functional calculus (including one for real-valued functions with real argument that
applies to self-adjoint elements of the algebra). -/

open_locale pointwise ennreal nnreal complex_order

open weak_dual weak_dual.character_space elemental_star_algebra

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]

instance {R A : Type*} [comm_ring R] [star_ring R] [normed_ring A] [algebra R A] [star_ring A]
  [has_continuous_star A] [star_module R A] (a : A) [is_star_normal a] :
  normed_comm_ring (elemental_star_algebra R a) :=
{ mul_comm := mul_comm, .. subring_class.to_normed_ring (elemental_star_algebra R a) }

instance {R A : Type*} [normed_field R] [star_ring R] [normed_ring A] [normed_algebra R A]
  [star_ring A] [has_continuous_star A] [star_module R A] (a : A) :
  normed_algebra R (elemental_star_algebra R a) :=
star_subalgebra.to_normed_algebra (elemental_star_algebra R a)

instance {R A : Type*} [normed_field R] [star_ring R] [normed_ring A] [normed_algebra R A]
  [star_ring A] [has_continuous_star A] [star_module R A] (a : A) :
  normed_space R (elemental_star_algebra R a) :=
normed_algebra.to_normed_space _

-- without this instance type class search causes timeouts
noncomputable instance elemental_star_algebra.complex.normed_algebra (a : A) :
  normed_algebra ℂ (elemental_star_algebra ℂ a) :=
infer_instance

variables [complete_space A] (a : A) [is_star_normal a] (S : star_subalgebra ℂ A)

/-- This lemma is used in the proof of `star_subalgebra.is_unit_of_is_unit_of_is_star_normal`,
which in turn is the key to spectral permanence `star_subalgebra.spectrum_eq`, which is itself
necessary for the continuous functional calculus. Using the continuous functional calculus, this
lemma can be superseded by one that omits the `is_star_normal` hypothesis. -/
lemma spectrum_star_mul_self_of_is_star_normal :
  spectrum ℂ (star a * a) ⊆ set.Icc (0 : ℂ) (‖star a * a‖) :=
begin
  -- this instance should be found automatically, but without providing it Lean goes on a wild
  -- goose chase when trying to apply `spectrum.gelfand_transform_eq`.
  letI := elemental_star_algebra.complex.normed_algebra a,
  unfreezingI { rcases subsingleton_or_nontrivial A },
  { simp only [spectrum.of_subsingleton, set.empty_subset] },
  { set a' : elemental_star_algebra ℂ a := ⟨a, self_mem ℂ a⟩,
    refine (spectrum.subset_star_subalgebra (star a' * a')).trans _,
    rw [←spectrum.gelfand_transform_eq (star a' * a'), continuous_map.spectrum_eq_range],
    rintro - ⟨φ, rfl⟩,
    rw [gelfand_transform_apply_apply ℂ _ (star a' * a') φ, map_mul φ, map_star φ],
    rw [complex.eq_coe_norm_of_nonneg star_mul_self_nonneg, ←map_star, ←map_mul],
    exact ⟨complex.zero_le_real.2 (norm_nonneg _),
      complex.real_le_real.2 (alg_hom.norm_apply_le_self φ (star a' * a'))⟩, }
end

variables {a}

/-- This is the key lemma on the way to establishing spectral permanence for C⋆-algebras, which is
established in `star_subalgebra.spectrum_eq`. This lemma is superseded by
`star_subalgebra.coe_is_unit`, which does not require an `is_star_normal` hypothesis and holds for
any closed star subalgebra. -/
lemma elemental_star_algebra.is_unit_of_is_unit_of_is_star_normal (h : is_unit a) :
  is_unit (⟨a, self_mem ℂ a⟩ : elemental_star_algebra ℂ a) :=
begin
  /- Sketch of proof: Because `a` is normal, it suffices to prove that `star a * a` is invertible
  in `elemental_star_algebra ℂ a`. For this it suffices to prove that it is sufficiently close to a
  unit, namely `algebra_map ℂ _ ‖star a * a‖`, and in this case the required distance is
  `‖star a * a‖`. So one must show `‖star a * a - algebra_map ℂ _ ‖star a * a‖‖ < ‖star a * a‖`.
  Since `star a * a - algebra_map ℂ _ ‖star a * a‖` is selfadjoint, by a corollary of Gelfand's
  formula for the spectral radius (`is_self_adjoint.spectral_radius_eq_nnnorm`) its norm is the
  supremum of the norms of elements in its spectrum (we may use the spectrum in `A` here because
  the norm in `A` and the norm in the subalgebra coincide).

  By `spectrum_star_mul_self_of_is_star_normal`, the spectrum (in the algebra `A`) of `star a * a`
  is contained in the interval `[0, ‖star a * a‖]`, and since `a` (and hence `star a * a`) is
  invertible in `A`, we may omit `0` from this interval. Therefore, by basic spectral mapping
  properties, the spectrum (in the algebra `A`) of `star a * a - algebra_map ℂ _ ‖star a * a‖` is
  contained in `[0, ‖star a * a‖)`. The supremum of the (norms of) elements of the spectrum must be
  *strictly* less that `‖star a * a‖` because the spectrum is compact, which completes the proof. -/

  /- We may assume `A` is nontrivial. It suffices to show that `star a * a` is invertible in the
  commutative (because `a` is normal) ring `elemental_star_algebra ℂ a`. Indeed, by commutativity,
  if `star a * a` is invertible, then so is `a`. -/
  nontriviality A,
  set a' : elemental_star_algebra ℂ a := ⟨a, self_mem ℂ a⟩,
  suffices : is_unit (star a' * a'), from (is_unit.mul_iff.1 this).2,
  replace h := (show commute (star a) a, from star_comm_self' a).is_unit_mul_iff.2 ⟨h.star, h⟩,
  /- Since `a` is invertible, `‖star a * a‖ ≠ 0`, so `‖star a * a‖ • 1` is invertible in
  `elemental_star_algebra ℂ a`, and so it suffices to show that the distance between this unit and
  `star a * a` is less than `‖star a * a‖`. -/
  have h₁ : (‖star a * a‖ : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr (norm_ne_zero_iff.mpr h.ne_zero),
  set u : units (elemental_star_algebra ℂ a) :=
    units.map (algebra_map ℂ (elemental_star_algebra ℂ a)).to_monoid_hom (units.mk0 _ h₁),
  refine ⟨u.unit_of_nearby _ _, rfl⟩,
  simp only [complex.abs_of_real, map_inv₀, units.coe_map, units.coe_inv, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, units.coe_mk0, units.coe_map_inv, norm_algebra_map',
    inv_inv, complex.norm_eq_abs, abs_norm_eq_norm, subtype.val_eq_coe, coe_coe],
  /- Since `a` is invertible, by `spectrum_star_mul_self_of_is_star_normal`, the spectrum (in `A`)
  of `star a * a` is contained in the half-open interval `(0, ‖star a * a‖]`. Therefore, by basic
  spectral mapping properties, the spectrum of `‖star a * a‖ • 1 - star a * a` is contained in
  `[0, ‖star a * a‖)`. -/
  have h₂ : ∀ z ∈ spectrum ℂ (algebra_map ℂ A (‖star a * a‖) - star a * a), ‖z‖₊ < ‖star a * a‖₊,
  { intros z hz,
    rw [←spectrum.singleton_sub_eq, set.singleton_sub] at hz,
    have h₃ : z ∈ set.Icc (0 : ℂ) (‖star a * a‖),
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
  /- The norm of `‖star a * a‖ • 1 - star a * a` in the subalgebra and in `A` coincide. In `A`,
  because this element is selfadjoint, by `is_self_adjoint.spectral_radius_eq_nnnorm`, its norm is
  the supremum of the norms of the elements of the spectrum, which is strictly less than
  `‖star a * a‖` by `h₂` and because the spectrum is compact. -/
  exact ennreal.coe_lt_coe.1
  (calc (‖star a' * a' - algebra_map ℂ _ (‖star a * a‖)‖₊ : ℝ≥0∞)
      = ‖algebra_map ℂ A (‖star a * a‖) - star a * a‖₊ : by { rw [←nnnorm_neg, neg_sub], refl }
  ... = spectral_radius ℂ (algebra_map ℂ A (‖star a * a‖) - star a * a)
      : begin
          refine (is_self_adjoint.spectral_radius_eq_nnnorm _).symm,
          rw [is_self_adjoint, star_sub, star_mul, star_star, ←algebra_map_star_comm,
            is_R_or_C.star_def, is_R_or_C.conj_of_real],
        end
  ... < ‖star a * a‖₊ : spectrum.spectral_radius_lt_of_forall_lt _ h₂ ),
end

/-- For `x : A` which is invertible in `A`, the inverse lies in any unital C⋆-subalgebra `S`
containing `x`. -/
lemma star_subalgebra.is_unit_coe_inv_mem {S : star_subalgebra ℂ A} (hS : is_closed (S : set A))
  {x : A} (h : is_unit x) (hxS : x ∈ S) : ↑h.unit⁻¹ ∈ S :=
begin
  have hx := h.star.mul h,
  suffices this : (↑hx.unit⁻¹ : A) ∈ S,
  { rw [←one_mul (↑h.unit⁻¹ : A), ←hx.unit.inv_mul, mul_assoc, is_unit.unit_spec, mul_assoc,
      h.mul_coe_inv, mul_one],
    exact mul_mem this (star_mem hxS) },
  refine le_of_is_closed_of_mem ℂ hS (mul_mem (star_mem hxS) hxS) _,
  haveI := (is_self_adjoint.star_mul_self x).is_star_normal,
  have hx' := elemental_star_algebra.is_unit_of_is_unit_of_is_star_normal hx,
  convert (↑hx'.unit⁻¹ : elemental_star_algebra ℂ (star x * x)).prop using 1,
  exact left_inv_eq_right_inv hx.unit.inv_mul (congr_arg coe hx'.unit.mul_inv),
end

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
lemma star_subalgebra.coe_is_unit {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) {x : S} :
  is_unit (x : A) ↔ is_unit x :=
begin
  refine ⟨λ hx, ⟨⟨x, ⟨(↑hx.unit⁻¹ : A), star_subalgebra.is_unit_coe_inv_mem hS hx x.prop⟩, _, _⟩,
    rfl⟩, λ hx, hx.map S.subtype⟩,
  exacts [subtype.coe_injective hx.mul_coe_inv, subtype.coe_injective hx.coe_inv_mul],
end

lemma star_subalgebra.mem_spectrum_iff {S : star_subalgebra ℂ A} (hS : is_closed (S : set A))
  {x : S} {z : ℂ} : z ∈ spectrum ℂ x ↔ z ∈ spectrum ℂ (x : A) :=
not_iff_not.2 (star_subalgebra.coe_is_unit hS).symm

/-- **Spectral permanence.** The spectrum of an element is invariant of the (closed)
`star_subalgebra` in which it is contained. -/
lemma star_subalgebra.spectrum_eq {S : star_subalgebra ℂ A} (hS : is_closed (S : set A)) (x : S) :
  spectrum ℂ x = spectrum ℂ (x : A) :=
set.ext $ λ z, star_subalgebra.mem_spectrum_iff hS

variables (a)

/-- The natural map from `character_space ℂ (elemental_star_algebra ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfand_transform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental_star_algebra.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
noncomputable def elemental_star_algebra.character_space_to_spectrum (x : A)
  (φ : character_space ℂ (elemental_star_algebra ℂ x)) : spectrum ℂ x :=
{ val := φ ⟨x, self_mem ℂ x⟩,
  property := by simpa only [star_subalgebra.spectrum_eq (elemental_star_algebra.is_closed ℂ x)
    ⟨x, self_mem ℂ x⟩] using alg_hom.apply_mem_spectrum φ (⟨x, self_mem ℂ x⟩) }

lemma elemental_star_algebra.continuous_character_space_to_spectrum (x : A) :
  continuous (elemental_star_algebra.character_space_to_spectrum x) :=
continuous_induced_rng.2
  (map_continuous $ gelfand_transform ℂ (elemental_star_algebra ℂ x) ⟨x, self_mem ℂ x⟩)

lemma elemental_star_algebra.bijective_character_space_to_spectrum :
  function.bijective (elemental_star_algebra.character_space_to_spectrum a) :=
begin
  refine ⟨λ φ ψ h, star_alg_hom_class_ext ℂ (map_continuous φ) (map_continuous ψ)
    (by simpa only [elemental_star_algebra.character_space_to_spectrum, subtype.mk_eq_mk,
      continuous_map.coe_mk] using h), _⟩,
  rintros ⟨z, hz⟩,
  have hz' := (star_subalgebra.spectrum_eq (elemental_star_algebra.is_closed ℂ a)
    ⟨a, self_mem ℂ a⟩).symm.subst hz,
  rw character_space.mem_spectrum_iff_exists at hz',
  obtain ⟨φ, rfl⟩ := hz',
  exact ⟨φ, rfl⟩,
end

/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
noncomputable def elemental_star_algebra.character_space_homeo :
  character_space ℂ (elemental_star_algebra ℂ a) ≃ₜ spectrum ℂ a :=
@continuous.homeo_of_equiv_compact_to_t2 _ _ _ _ _ _
  (equiv.of_bijective (elemental_star_algebra.character_space_to_spectrum a)
    (elemental_star_algebra.bijective_character_space_to_spectrum a))
    (elemental_star_algebra.continuous_character_space_to_spectrum a)

/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `star_alg_equiv` from the complex-valued continuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(continuous_map.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuous_functional_calculus_map_id`. As such it extends the polynomial functional calculus. -/
noncomputable def continuous_functional_calculus :
  C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental_star_algebra ℂ a :=
((elemental_star_algebra.character_space_homeo a).comp_star_alg_equiv' ℂ ℂ).trans
  (gelfand_star_transform (elemental_star_algebra ℂ a)).symm

lemma continuous_functional_calculus_map_id :
  continuous_functional_calculus a ((continuous_map.id ℂ).restrict (spectrum ℂ a)) =
    ⟨a, self_mem ℂ a⟩ :=
star_alg_equiv.symm_apply_apply _ _
