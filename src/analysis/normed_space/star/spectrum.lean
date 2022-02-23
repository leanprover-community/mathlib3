/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum

/-!
In this file, we establish various properties related to the spectrum of elements in a
C⋆-algebra over ℂ.
-/

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [cstar_ring A] [complete_space A]
[measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

open_locale topological_space ennreal
open filter ennreal

lemma spectral_radius_eq_nnnorm_of_self_adjoint {a : A} (ha : a ∈ self_adjoint A) :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  have hconst : tendsto (λ n : ℕ, (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds,
  refine tendsto_nhds_unique _ hconst,
  convert (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (nat.tendsto_pow_at_top_at_top_of_one_lt (by linarith : 1 < 2)),
  refine funext (λ n, _),
  rw [function.comp_app, nnnorm_pow_two_pow_of_self_adjoint ha, ennreal.coe_pow, ←rpow_nat_cast,
    ←rpow_mul],
  simp,
end

lemma self_adjoint.coe_spectral_radius_eq_nnnorm (a : self_adjoint A) :
  spectral_radius ℂ (a : A) = ∥(a : A)∥₊ :=
spectral_radius_eq_nnnorm_of_self_adjoint a.property
