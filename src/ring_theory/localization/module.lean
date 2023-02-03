/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
import linear_algebra.basis
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `linear_independent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `basis.localization_localization`: promote an `R`-basis `b` of `A` to an `Rₛ`-basis of `Aₛ`,
   where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s` respectively
 * `linear_independent.iff_fraction_ring`: `b` is linear independent over `R` iff it is
   linear independent over `Frac(R)`
-/

open_locale big_operators
open_locale non_zero_divisors

section localization

variables {R : Type*} (Rₛ : Type*) [comm_ring R] [comm_ring Rₛ] [algebra R Rₛ]
variables (S : submonoid R) [hT : is_localization S Rₛ]

include hT

section add_comm_monoid
variables {M : Type*} [add_comm_monoid M] [module R M] [module Rₛ M] [is_scalar_tower R Rₛ M]

lemma linear_independent.localization {ι : Type*} {b : ι → M} (hli : linear_independent R b) :
  linear_independent Rₛ b :=
begin
  rw linear_independent_iff' at ⊢ hli,
  intros s g hg i hi,
  choose! a g' hg' using is_localization.exist_integer_multiples S s g,
  specialize hli s g' _ i hi,
  { rw [← @smul_zero _ M _ _ (a : R), ← hg, finset.smul_sum],
    refine finset.sum_congr rfl (λ i hi, _),
    rw [← is_scalar_tower.algebra_map_smul Rₛ, hg' i hi, smul_assoc],
    apply_instance },
  refine ((is_localization.map_units Rₛ a).mul_right_eq_zero).mp _,
  rw [← algebra.smul_def, ← map_zero (algebra_map R Rₛ), ← hli, hg' i hi],
end
end add_comm_monoid

section localization_localization

variables {A : Type*} [comm_ring A] [algebra R A]
variables (Aₛ : Type*) [comm_ring Aₛ] [algebra A Aₛ]
variables [algebra Rₛ Aₛ] [algebra R Aₛ] [is_scalar_tower R Rₛ Aₛ] [is_scalar_tower R A Aₛ]
variables [hA : is_localization (algebra.algebra_map_submonoid A S) Aₛ]
include hA

open submodule

lemma linear_independent.localization_localization
  {ι : Type*} {v : ι → A} (hv : linear_independent R v) :
  linear_independent Rₛ (algebra_map A Aₛ ∘ v) :=
begin
  rw linear_independent_iff' at ⊢ hv,
  intros s g hg i hi,
  choose! a g' hg' using is_localization.exist_integer_multiples S s g,
  have h0 : algebra_map A Aₛ (∑ i in s, g' i • v i) = 0,
  { apply_fun ((•) (a : R)) at hg,
    rw [smul_zero, finset.smul_sum] at hg,
    rw [map_sum, ← hg],
    refine finset.sum_congr rfl (λ i hi, _),
    rw [← smul_assoc, ← hg' i hi, algebra.smul_def, map_mul,
        ← is_scalar_tower.algebra_map_apply, ← algebra.smul_def, algebra_map_smul] },
  obtain ⟨⟨_, r, hrS, rfl⟩, (hr : algebra_map R A r * _ = 0)⟩ :=
    (is_localization.map_eq_zero_iff (algebra.algebra_map_submonoid A S) _ _).1 h0,
  simp_rw [finset.mul_sum, ← algebra.smul_def, smul_smul] at hr,
  specialize hv s _ hr i hi,
  rw [← (is_localization.map_units Rₛ a).mul_right_eq_zero, ← algebra.smul_def, ← hg' i hi],
  exact (is_localization.map_eq_zero_iff S _ _).2 ⟨⟨r, hrS⟩, hv⟩,
end

lemma span_eq_top.localization_localization {v : set A} (hv : span R v = ⊤) :
  span Rₛ (algebra_map A Aₛ '' v) = ⊤ :=
begin
  rw eq_top_iff,
  rintros a' -,
  obtain ⟨a, ⟨_, s, hs, rfl⟩, rfl⟩ := is_localization.mk'_surjective
    (algebra.algebra_map_submonoid A S) a',
  rw [is_localization.mk'_eq_mul_mk'_one, mul_comm, ← map_one (algebra_map R A)],
  erw ← is_localization.algebra_map_mk' A Rₛ Aₛ (1 : R) ⟨s, hs⟩, -- `erw` needed to unify `⟨s, hs⟩`
  rw ← algebra.smul_def,
  refine smul_mem _ _ (span_subset_span R _ _ _),
  rw [← algebra.coe_linear_map, ← linear_map.coe_restrict_scalars R, ← linear_map.map_span],
  exact mem_map_of_mem (hv.symm ▸ mem_top),
  { apply_instance }
end

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[algebra A Aₛ]` is `localization_algebra`.
-/
noncomputable def basis.localization_localization {ι : Type*} (b : basis ι R A) : basis ι Rₛ Aₛ :=
basis.mk
  (b.linear_independent.localization_localization _ S _)
  (by { rw [set.range_comp, span_eq_top.localization_localization Rₛ S Aₛ b.span_eq],
        exact le_rfl })

@[simp] lemma basis.localization_localization_apply {ι : Type*} (b : basis ι R A) (i) :
  b.localization_localization Rₛ S Aₛ i = algebra_map A Aₛ (b i) :=
basis.mk_apply _ _ _

@[simp] lemma basis.localization_localization_repr_algebra_map
  {ι : Type*} (b : basis ι R A) (x i) :
  (b.localization_localization Rₛ S Aₛ).repr (algebra_map A Aₛ x) i =
    algebra_map R Rₛ (b.repr x i) :=
calc (b.localization_localization Rₛ S Aₛ).repr (algebra_map A Aₛ x) i
    = (b.localization_localization Rₛ S Aₛ).repr
        ((b.repr x).sum (λ j c, algebra_map R Rₛ c • algebra_map A Aₛ (b j))) i :
  by simp_rw [is_scalar_tower.algebra_map_smul, algebra.smul_def,
              is_scalar_tower.algebra_map_apply R A Aₛ, ← _root_.map_mul, ← map_finsupp_sum,
              ← algebra.smul_def, ← finsupp.total_apply, basis.total_repr]
... = (b.repr x).sum (λ j c, algebra_map R Rₛ c • finsupp.single j 1 i) :
  by simp_rw [← b.localization_localization_apply Rₛ S Aₛ, map_finsupp_sum,
              linear_equiv.map_smul, basis.repr_self, finsupp.sum_apply, finsupp.smul_apply]
... = _ : finset.sum_eq_single i
            (λ j _ hj, by simp [hj])
            (λ hi, by simp [finsupp.not_mem_support_iff.mp hi])
... = algebra_map R Rₛ (b.repr x i) : by simp [algebra.smul_def]

end localization_localization

end localization

section fraction_ring

variables (R K : Type*) [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K]
variables {V : Type*} [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]

lemma linear_independent.iff_fraction_ring {ι : Type*} {b : ι → V} :
  linear_independent R b ↔ linear_independent K b :=
⟨linear_independent.localization K (R⁰),
 linear_independent.restrict_scalars (smul_left_injective R one_ne_zero)⟩

end fraction_ring
