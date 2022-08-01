/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
import linear_algebra.linear_independent
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `linear_independent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `basis.localization`: promote an `R`-basis `b` to an `Rₛ`-basis,
   where `Rₛ` is a localization of `R`
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
  choose a g' hg' using is_localization.exist_integer_multiples S s g,
  letI := λ i, classical.prop_decidable (i ∈ s),
  specialize hli s (λ i, if hi : i ∈ s then g' i hi else 0) _ i hi,
  { rw [← @smul_zero _ M _ _ _ (a : R), ← hg, finset.smul_sum],
    refine finset.sum_congr rfl (λ i hi, _),
    dsimp only,
    rw [dif_pos hi, ← is_scalar_tower.algebra_map_smul Rₛ, hg' i hi, smul_assoc],
    apply_instance },
  refine ((is_localization.map_units Rₛ a).mul_right_eq_zero).mp _,
  rw [← algebra.smul_def, ← map_zero (algebra_map R Rₛ), ← hli],
  simv [hi, hg']
end
end add_comm_monoid

section add_comm_group
variables {M : Type*} [add_comm_group M] [module R M] [module Rₛ M] [is_scalar_tower R Rₛ M]

/-- Promote a basis for `M` over `R` to a basis for `M` over the localization `Rₛ` -/
noncomputable def basis.localization {ι : Type*} (b : basis ι R M) : basis ι Rₛ M :=
basis.mk (b.linear_independent.localization Rₛ S) $
by { rw [← eq_top_iff, ← @submodule.restrict_scalars_eq_top_iff Rₛ R, eq_top_iff, ← b.span_eq],
     apply submodule.span_le_restrict_scalars }

end add_comm_group

end localization

section fraction_ring

variables (R K : Type*) [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K]
variables {V : Type*} [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]

lemma linear_independent.iff_fraction_ring {ι : Type*} {b : ι → V} :
  linear_independent R b ↔ linear_independent K b :=
⟨linear_independent.localization K (R⁰),
 linear_independent.restrict_scalars (smul_left_injective R one_ne_zero)⟩

end fraction_ring
