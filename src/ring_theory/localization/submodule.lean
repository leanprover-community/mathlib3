/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.localization.fraction_ring
import ring_theory.localization.ideal
import ring_theory.principal_ideal_domain

/-!
# Submodules in localizations of commutative rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

namespace is_localization

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
-- This was previously a `has_coe` instance, but if `S = R` then this will loop.
-- It could be a `has_coe_t` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
def coe_submodule (I : ideal R) : submodule R S := submodule.map (algebra.linear_map R S) I

lemma mem_coe_submodule (I : ideal R) {x : S} :
  x ∈ coe_submodule S I ↔ ∃ y : R, y ∈ I ∧ algebra_map R S y = x :=
iff.rfl

lemma coe_submodule_mono {I J : ideal R} (h : I ≤ J) :
  coe_submodule S I ≤ coe_submodule S J :=
submodule.map_mono h

@[simp] lemma coe_submodule_bot : coe_submodule S (⊥ : ideal R) = ⊥ :=
by rw [coe_submodule, submodule.map_bot]

@[simp] lemma coe_submodule_top : coe_submodule S (⊤ : ideal R) = 1 :=
by rw [coe_submodule, submodule.map_top, submodule.one_eq_range]

@[simp] lemma coe_submodule_sup (I J : ideal R) :
  coe_submodule S (I ⊔ J) = coe_submodule S I ⊔ coe_submodule S J :=
submodule.map_sup _ _ _

@[simp] lemma coe_submodule_mul (I J : ideal R) :
  coe_submodule S (I * J) = coe_submodule S I * coe_submodule S J :=
submodule.map_mul _ _ (algebra.of_id R S)

lemma coe_submodule_fg
  (hS : function.injective (algebra_map R S)) (I : ideal R) :
  submodule.fg (coe_submodule S I) ↔ submodule.fg I :=
⟨submodule.fg_of_fg_map _ (linear_map.ker_eq_bot.mpr hS), submodule.fg.map _⟩

@[simp]
lemma coe_submodule_span (s : set R) :
  coe_submodule S (ideal.span s) = submodule.span R ((algebra_map R S) '' s) :=
by { rw [is_localization.coe_submodule, ideal.span, submodule.map_span], refl }

@[simp]
lemma coe_submodule_span_singleton (x : R) :
  coe_submodule S (ideal.span {x}) = submodule.span R {(algebra_map R S) x} :=
by rw [coe_submodule_span, set.image_singleton]

variables {g : R →+* P}
variables {T : submonoid P} (hy : M ≤ T.comap g) {Q : Type*} [comm_ring Q]
variables [algebra P Q] [is_localization T Q]
variables [is_localization M S]

section

include M

lemma is_noetherian_ring (h : is_noetherian_ring R) : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at h ⊢,
  exact order_embedding.well_founded ((is_localization.order_embedding M S).dual) h
end

end

variables {S Q M}

@[mono]
lemma coe_submodule_le_coe_submodule (h : M ≤ non_zero_divisors R)
  {I J : ideal R} :
  coe_submodule S I ≤ coe_submodule S J ↔ I ≤ J :=
submodule.map_le_map_iff_of_injective (is_localization.injective _ h) _ _

@[mono]
lemma coe_submodule_strict_mono (h : M ≤ non_zero_divisors R) :
  strict_mono (coe_submodule S : ideal R → submodule R S) :=
strict_mono_of_le_iff_le (λ _ _, (coe_submodule_le_coe_submodule h).symm)

variables (S) {Q M}

lemma coe_submodule_injective (h : M ≤ non_zero_divisors R) :
  function.injective (coe_submodule S : ideal R → submodule R S) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule h).mp)

lemma coe_submodule_is_principal {I : ideal R} (h : M ≤ non_zero_divisors R) :
  (coe_submodule S I).is_principal ↔ I.is_principal :=
begin
  split; unfreezingI { rintros ⟨⟨x, hx⟩⟩ },
  { have x_mem : x ∈ coe_submodule S I := hx.symm ▸ submodule.mem_span_singleton_self x,
    obtain ⟨x, x_mem, rfl⟩ := (mem_coe_submodule _ _).mp x_mem,
    refine ⟨⟨x, coe_submodule_injective S h _⟩⟩,
    rw [ideal.submodule_span_eq, hx, coe_submodule_span_singleton] },
  { refine ⟨⟨algebra_map R S x, _⟩⟩,
    rw [hx, ideal.submodule_span_eq, coe_submodule_span_singleton] }
end

variables {S} (M)
lemma mem_span_iff {N : Type*} [add_comm_group N] [module R N] [module S N] [is_scalar_tower R S N]
  {x : N} {a : set N} :
  x ∈ submodule.span S a ↔ ∃ (y ∈ submodule.span R a) (z : M), x = mk' S 1 z • y :=
begin
  split, intro h,
  { refine submodule.span_induction h _ _ _ _,
    { rintros x hx,
      exact ⟨x, submodule.subset_span hx, 1, by rw [mk'_one, _root_.map_one, one_smul]⟩ },
    { exact ⟨0, submodule.zero_mem _, 1, by rw [mk'_one, _root_.map_one, one_smul]⟩ },
    { rintros _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy', z', rfl⟩,
      refine ⟨(z' : R) • y + (z : R) • y',
        (submodule.add_mem _ (submodule.smul_mem _ _ hy) (submodule.smul_mem _ _ hy')), z * z', _⟩,
      rw [smul_add, ← is_scalar_tower.algebra_map_smul S (z : R),
          ← is_scalar_tower.algebra_map_smul S (z' : R), smul_smul, smul_smul],
      congr' 1,
      { rw [← mul_one (1 : R), mk'_mul, mul_assoc, mk'_spec,
            _root_.map_one, mul_one, mul_one] },
      { rw [← mul_one (1 : R), mk'_mul, mul_right_comm, mk'_spec,
            _root_.map_one, mul_one, one_mul] },
      all_goals { apply_instance } },
    { rintros a _ ⟨y, hy, z, rfl⟩,
      obtain ⟨y', z', rfl⟩ := mk'_surjective M a,
      refine ⟨y' • y, submodule.smul_mem _ _ hy, z' * z, _⟩,
      rw [← is_scalar_tower.algebra_map_smul S y', smul_smul, ← mk'_mul,
          smul_smul, mul_comm (mk' S _ _), mul_mk'_eq_mk'_of_mul],
      all_goals { apply_instance } } },
  { rintro ⟨y, hy, z, rfl⟩,
    exact submodule.smul_mem _ _ (submodule.span_subset_span R S _ hy) }
end

lemma mem_span_map {x : S} {a : set R} :
  x ∈ ideal.span (algebra_map R S '' a) ↔
    ∃ (y ∈ ideal.span a) (z : M), x = mk' S y z :=
begin
  refine (mem_span_iff M).trans _,
  split,
  { rw ← coe_submodule_span,
    rintros ⟨_, ⟨y, hy, rfl⟩, z, hz⟩,
    refine ⟨y, hy, z, _⟩,
    rw [hz, algebra.linear_map_apply, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one] },
  { rintros ⟨y, hy, z, hz⟩,
    refine ⟨algebra_map R S y, submodule.map_mem_span_algebra_map_image _ _ hy, z, _⟩,
    rw [hz, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one] },
end

end is_localization

namespace is_fraction_ring

open is_localization

variables {R} {A K : Type*} [comm_ring A]

section comm_ring

variables [comm_ring K] [algebra R K] [is_fraction_ring R K] [algebra A K] [is_fraction_ring A K]

@[simp, mono]
lemma coe_submodule_le_coe_submodule
  {I J : ideal R} : coe_submodule K I ≤ coe_submodule K J ↔ I ≤ J :=
is_localization.coe_submodule_le_coe_submodule le_rfl

@[mono]
lemma coe_submodule_strict_mono :
  strict_mono (coe_submodule K : ideal R → submodule R K) :=
strict_mono_of_le_iff_le (λ _ _, coe_submodule_le_coe_submodule.symm)

variables (R K)

lemma coe_submodule_injective :
  function.injective (coe_submodule K : ideal R → submodule R K) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule).mp)

@[simp]
lemma coe_submodule_is_principal {I : ideal R} :
  (coe_submodule K I).is_principal ↔ I.is_principal :=
is_localization.coe_submodule_is_principal _ le_rfl

end comm_ring

end is_fraction_ring
