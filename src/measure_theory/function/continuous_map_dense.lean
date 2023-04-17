/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import measure_theory.measure.regular
import measure_theory.function.simple_func_dense_lp
import topology.urysohns_lemma
import measure_theory.integral.bochner

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `1 ≤ p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.
It also proves the same results for approximation by continuous functions with compact support
when the space is locally compact and `μ` is regular.

The result is presented in several versions. First concrete versions giving an approximation
up to `ε` in these various contexts, and then abstract versions stating that the topological
closure of the relevant subgroups of `Lp` are the whole space.

* `mem_ℒp.exists_has_compact_support_snorm_sub_le` states that, in a locally compact space,
  an `ℒp` function can be approximated by continuous functions with compact support,
  in the sense that `snorm (f - g) p μ` is small.
* `mem_ℒp.exists_has_compact_support_integral_rpow_sub_le`: same result, but expressed in
  terms of `∫ ‖f - g‖^p`.

Versions with `integrable` instead of `mem_ℒp` are specialized to the case `p = 1`.
Versions with `bounded_continuous` instead of `has_compact_support` drop the locally
compact assumption and give only approximation by a bounded continuous function.

* `measure_theory.Lp.bounded_continuous_function_dense`: The subgroup
  `measure_theory.Lp.bounded_continuous_function` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `bounded_continuous_function.to_Lp_dense_range`: For finite-measure `μ`, the continuous linear
  map `bounded_continuous_function.to_Lp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `continuous_map.to_Lp_dense_range`: For compact `α` and finite-measure `μ`, the continuous linear
  map `continuous_map.to_Lp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?  See the
Vitali-Carathéodory theorem, in the file `measure_theory.vitali_caratheodory`.

-/

open_locale ennreal nnreal topology bounded_continuous_function
open measure_theory topological_space continuous_map set

variables {α : Type*} [measurable_space α] [topological_space α] [normal_space α] [borel_space α]
variables {E : Type*} [normed_add_comm_group E] {μ : measure α} {p : ℝ≥0∞}

namespace measure_theory

variables [normed_space ℝ E]

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
lemma bounded_continuous_function_dense
  [second_countable_topology_either α E] [_i : fact (1 ≤ p)] (hp : p ≠ ∞) [μ.weakly_regular] :
  (bounded_continuous_function E p μ).topological_closure = ⊤ :=
begin
  rw add_subgroup.eq_top_iff',
  assume f,
  refine mem_closure_iff_frequently.mpr _,
  rw metric.nhds_basis_closed_ball.frequently_iff,
  intros ε hε,
  have A : ennreal.of_real ε ≠ 0, by simp only [ne.def, ennreal.of_real_eq_zero, not_le, hε],
  obtain ⟨g, hg, g_mem⟩ : ∃ (g : α →ᵇ E), snorm (f - g) p μ ≤ ennreal.of_real ε ∧ mem_ℒp g p μ,
    from (Lp.mem_ℒp f).exists_bounded_continuous_snorm_sub_le hp _i.out A,
  refine ⟨g_mem.to_Lp _, _, ⟨g, rfl⟩⟩,
  simp only [dist_eq_norm, metric.mem_closed_ball'],
  rw Lp.norm_def,
  convert ennreal.to_real_le_of_le_of_real hε.le hg using 2,
  apply snorm_congr_ae,
  filter_upwards [coe_fn_sub f (g_mem.to_Lp g), g_mem.coe_fn_to_Lp] with x hx h'x,
  simp only [hx, pi.sub_apply, sub_right_inj, h'x],
end

end Lp

end measure_theory

variables [second_countable_topology_either α E] [_i : fact (1 ≤ p)] (hp : p ≠ ∞)
variables (𝕜 : Type*) [normed_field 𝕜] [normed_algebra ℝ 𝕜] [normed_space 𝕜 E]
include _i hp
variables (E) (μ)

namespace bounded_continuous_function

lemma to_Lp_dense_range [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (linear_map.range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ))
    .to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp],
end

end bounded_continuous_function

namespace continuous_map

lemma to_Lp_dense_range [compact_space α] [μ.weakly_regular] [is_finite_measure μ] :
  dense_range ⇑(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ) :=
begin
  haveI : normed_space ℝ E := restrict_scalars.normed_space ℝ 𝕜 E,
  rw dense_range_iff_closure_range,
  suffices : (linear_map.range (to_Lp p μ 𝕜 : _ →L[𝕜] Lp E p μ))
    .to_add_subgroup.topological_closure = ⊤,
  { exact congr_arg coe this },
  simp [range_to_Lp p μ, measure_theory.Lp.bounded_continuous_function_dense E hp]
end

end continuous_map
