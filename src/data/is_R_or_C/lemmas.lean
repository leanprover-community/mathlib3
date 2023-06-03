/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import analysis.normed_space.finite_dimension
import field_theory.tower
import data.is_R_or_C.basic

/-! # Further lemmas about `is_R_or_C` 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/

variables {K E : Type*} [is_R_or_C K]

namespace polynomial

open_locale polynomial

lemma of_real_eval (p : ℝ[X]) (x : ℝ) : (p.eval x : K) = aeval ↑x p :=
(@aeval_algebra_map_apply_eq_algebra_map_eval ℝ K _ _ _ x p).symm

end polynomial

namespace finite_dimensional

open_locale classical
open is_R_or_C

/-- This instance generates a type-class problem with a metavariable `?m` that should satisfy
`is_R_or_C ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/
library_note "is_R_or_C instance"

/-- An `is_R_or_C` field is finite-dimensional over `ℝ`, since it is spanned by `{1, I}`. -/
@[nolint dangerous_instance] instance is_R_or_C_to_real : finite_dimensional ℝ K :=
⟨⟨{1, I},
  begin
    rw eq_top_iff,
    intros a _,
    rw [finset.coe_insert, finset.coe_singleton, submodule.mem_span_insert],
    refine ⟨re a, (im a) • I, _, _⟩,
    { rw submodule.mem_span_singleton,
      use im a },
    simp [re_add_im a, algebra.smul_def, algebra_map_eq_of_real]
  end⟩⟩

variables (K E) [normed_add_comm_group E] [normed_space K E]

/-- A finite dimensional vector space over an `is_R_or_C` is a proper metric space.

This is not an instance because it would cause a search for `finite_dimensional ?x E` before
`is_R_or_C ?x`. -/
lemma proper_is_R_or_C [finite_dimensional K E] : proper_space E :=
begin
  letI : normed_space ℝ E := restrict_scalars.normed_space ℝ K E,
  letI : finite_dimensional ℝ E := finite_dimensional.trans ℝ K E,
  apply_instance
end

variable {E}

instance is_R_or_C.proper_space_submodule (S : submodule K E) [finite_dimensional K ↥S] :
  proper_space S :=
proper_is_R_or_C K S

end finite_dimensional

namespace is_R_or_C

@[simp, is_R_or_C_simps] lemma re_clm_norm : ‖(re_clm : K →L[ℝ] ℝ)‖ = 1 :=
begin
  apply le_antisymm (linear_map.mk_continuous_norm_le _ zero_le_one _),
  convert continuous_linear_map.ratio_le_op_norm _ (1 : K),
  { simp },
  { apply_instance }
end

@[simp, is_R_or_C_simps] lemma conj_cle_norm : ‖(@conj_cle K _ : K →L[ℝ] K)‖ = 1 :=
(@conj_lie K _).to_linear_isometry.norm_to_continuous_linear_map

@[simp, is_R_or_C_simps] lemma of_real_clm_norm : ‖(of_real_clm : ℝ →L[ℝ] K)‖ = 1 :=
linear_isometry.norm_to_continuous_linear_map of_real_li

end is_R_or_C
