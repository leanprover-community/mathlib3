/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach
import analysis.normed_space.operator_norm
import topology.metric_space.antilipschitz

/-!
# The Lax-Milgram Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`.
Under the hypothesis that `B` is coercive
we prove the Lax-Milgram theorem:
that is, the map `inner_product_space.continuous_linear_map_of_bilin` from
`analysis.inner_product_space.dual` can be upgraded to a continuous equivalence
`is_coercive.continuous_linear_equiv_of_bilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/

noncomputable theory
open is_R_or_C linear_map continuous_linear_map inner_product_space linear_map (ker range)
open_locale real_inner_product_space nnreal

universe u

namespace is_coercive
variables {V : Type u} [normed_add_comm_group V] [inner_product_space ℝ V] [complete_space V]
variables {B : V →L[ℝ] V →L[ℝ] ℝ}

local postfix `♯`:1025 := @continuous_linear_map_of_bilin ℝ V _ _ _ _

lemma bounded_below (coercive : is_coercive B) :
  ∃ C, 0 < C ∧ ∀ v, C * ‖v‖ ≤ ‖B♯ v‖ :=
begin
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  refine ⟨C, C_ge_0, _⟩,
  intro v,
  by_cases h : 0 < ‖v‖,
  { refine (mul_le_mul_right h).mp _,
    calc C * ‖v‖ * ‖v‖
        ≤ B v v : coercivity v
    ... = ⟪B♯ v, v⟫_ℝ : (continuous_linear_map_of_bilin_apply ℝ B v v).symm
    ... ≤ ‖B♯ v‖ * ‖v‖ : real_inner_le_norm (B♯ v) v, },
  { have : v = 0 := by simpa using h,
    simp [this], }
end

lemma antilipschitz (coercive : is_coercive B) :
  ∃ C : ℝ≥0, 0 < C ∧ antilipschitz_with C B♯ :=
begin
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩,
  refine ⟨(C⁻¹).to_nnreal, real.to_nnreal_pos.mpr (inv_pos.mpr C_pos), _⟩,
  refine continuous_linear_map.antilipschitz_of_bound B♯ _,
  simp_rw [real.coe_to_nnreal',
    max_eq_left_of_lt (inv_pos.mpr C_pos),
    ←inv_mul_le_iff (inv_pos.mpr C_pos)],
  simpa using below_bound,
end

lemma ker_eq_bot (coercive : is_coercive B) : ker B♯ = ⊥ :=
begin
  rw [linear_map_class.ker_eq_bot],
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩,
  exact antilipschitz.injective,
end

lemma closed_range (coercive : is_coercive B) : is_closed (range B♯ : set V) :=
begin
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩,
  exact antilipschitz.is_closed_range B♯.uniform_continuous,
end

lemma range_eq_top (coercive : is_coercive B) : range B♯ = ⊤ :=
begin
  haveI := coercive.closed_range.complete_space_coe,
  rw ← (range B♯).orthogonal_orthogonal,
  rw submodule.eq_top_iff',
  intros v w mem_w_orthogonal,
  rcases coercive with ⟨C, C_pos, coercivity⟩,
  obtain rfl : w = 0,
  { rw [←norm_eq_zero, ←mul_self_eq_zero, ←mul_right_inj' C_pos.ne', mul_zero, ←mul_assoc],
    apply le_antisymm,
    { calc C * ‖w‖ * ‖w‖
          ≤ B w w : coercivity w
      ... = ⟪B♯ w, w⟫_ℝ : (continuous_linear_map_of_bilin_apply ℝ B w w).symm
      ... = 0 : mem_w_orthogonal _ ⟨w, rfl⟩ },
    { exact mul_nonneg (mul_nonneg C_pos.le (norm_nonneg w)) (norm_nonneg w) } },
  exact inner_zero_left _,
end

/--
The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `continuous_linear_equiv_of_bilin B v` is the unique element `V`
such that `⟪continuous_linear_equiv_of_bilin B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def continuous_linear_equiv_of_bilin (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  B♯
  coercive.ker_eq_bot
  coercive.range_eq_top

@[simp]
lemma continuous_linear_equiv_of_bilin_apply (coercive : is_coercive B) (v w : V) :
  ⟪coercive.continuous_linear_equiv_of_bilin v, w⟫_ℝ = B v w :=
continuous_linear_map_of_bilin_apply ℝ B v w

lemma unique_continuous_linear_equiv_of_bilin (coercive : is_coercive B) {v f : V}
  (is_lax_milgram : (∀ w, ⟪f, w⟫_ℝ = B v w)) :
  f = coercive.continuous_linear_equiv_of_bilin v :=
unique_continuous_linear_map_of_bilin ℝ B is_lax_milgram

end is_coercive
