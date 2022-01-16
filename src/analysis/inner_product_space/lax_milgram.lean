/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach

/-!
# The The Lax-Milgram Theorem


We consider an Hilbert space `V` over `ℝ`
equipped with a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.
For every such form we define the
`lax_milgram_map : V →L[ℝ] V`,
which is defined by the property `B (lax_milgram_map B v) w = ⟪v, w⟫`
using the Fréchet-Riesz representation theorem.

Under the hypothesis that `B` is *coercive* (fulfills `is_coercive`),
we prove the Lax-Milgram theorem:
that is, the `lax_milgram_map` can be upgraded to a continuous equivalence `lax_milgram`

## References

TODO cite the slides


## Tags

dual, Lax-Milgram
-/

noncomputable theory



open_locale classical complex_conjugate
open is_R_or_C continuous_linear_map linear_map linear_equiv

universe u
def is_coercive
  {V : Type u} [inner_product_space ℝ V] [complete_space V] (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u


namespace lax_milgram
variables {V : Type u} [inner_product_space ℝ V] [complete_space V]
variables (B : V →L[ℝ] V →L[ℝ] ℝ)


def lax_milgram_map (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
(inner_product_space.to_dual ℝ V).symm.to_continuous_linear_equiv.to_continuous_linear_map ∘L B


@[simp]
lemma lax_milgram_map_apply (v w : V) : B v w = inner (lax_milgram_map B v) w :=
begin
  dunfold lax_milgram_map,
  simp,
end


lemma injective (coercive : is_coercive B) : (lax_milgram_map B).ker = ⊥ :=
begin
  rw submodule.eq_bot_iff, intro v,
  simp only [continuous_linear_map.mem_ker, submodule.mem_bot],
  contrapose,
  simp_rw [←ne.def],
  intro v_ne_0,
  simp_rw [ ←norm_pos_iff] at ⊢ v_ne_0,
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  have squared : C * ∥v∥ * ∥v∥ ≤ ∥lax_milgram_map B v ∥ * ∥v∥ :=
  calc C * ∥v∥*∥v∥
       ≤ B v v                         : coercivity v
  ...  = inner (lax_milgram_map B v) v : by simp
  ...  ≤ ∥lax_milgram_map B v ∥ * ∥v∥    : real_inner_le_norm (lax_milgram_map B v) v,
  have coerced := (mul_le_mul_right v_ne_0).mp squared,
  exact calc 0 < C * ∥v∥                  : mul_pos C_ge_0 v_ne_0
  ...          ≤ ∥(lax_milgram_map B) v∥  : coerced,
end


lemma closed_range : @is_closed V infer_instance ↑(lax_milgram_map B).range :=
begin
  rw ←is_seq_closed_iff_is_closed,
  apply is_seq_closed_of_def,
  intros x y mem_range_x tendsto_y,
  sorry,
end

lemma surjective (coercive : is_coercive B): (lax_milgram_map B).range = ⊤ :=
begin
  rw submodule.eq_top_iff', intro v,
  -- As the range of lax_milgram_map is closed, it is also complete
  haveI := (closed_range B).complete_space_coe,
  -- Every vector can be decomposed uniquely as the sum of an element in the range
  -- and an element in the complement
  have decompose_v :=
    eq_sum_orthogonal_projection_self_orthogonal_complement (lax_milgram_map B).range v,
  -- We show the orthogonal component of v is 0
  have zero_orthogonal_component
    : ↑((orthogonal_projection (lax_milgram_map B).rangeᗮ) v) = (0 : V),
  by begin
    -- the orthogonal component of v is zero iff, for all w in the orthogonal complement ⟪v,w⟫=0
    refine eq_orthogonal_projection_of_mem_of_inner_eq_zero
      (submodule.zero_mem ((lax_milgram_map B).range)ᗮ) _,
    intros w mem_w_orthogonal,
    -- We show every element of the orthogonal complement is zero, by coercivity
    rcases coercive with ⟨C, C_ge_0, coercivity⟩,
    have nonneg_C : 0 ≤ C, by linarith,
    have : 0 ≤ C * ∥w∥*∥w∥ := mul_nonneg (mul_nonneg nonneg_C (norm_nonneg w)) (norm_nonneg w),
    have inner_product_eq_zero :=
      (submodule.mem_orthogonal ((lax_milgram_map B).range) w).mp mem_w_orthogonal,
    have : lax_milgram_map B w ∈ (lax_milgram_map B).range :=
      by simp [continuous_linear_map.mem_range],
    have : C * ∥w∥*∥w∥ ≤ 0 :=
    calc C * ∥w∥*∥w∥
         ≤ B w w                          : coercivity w
    ...  = inner (lax_milgram_map B w) w  : by simp
    ...  = 0                              : by {apply inner_product_eq_zero, assumption},
    have zero_eq_C_norm_w_squared : C * ∥w∥*∥w∥ = 0 := by linarith,
    have w_eq_zero : w = 0 := by begin
      simp at zero_eq_C_norm_w_squared,
      cases zero_eq_C_norm_w_squared, -- Either C or w is zero
       -- if C = 0 we get a contradiction
      exfalso, linarith,
      -- if w = 0 we've shown what we wanted
      assumption,
    end,
    simp [w_eq_zero],
  end,
  rw zero_orthogonal_component at decompose_v, simp at decompose_v,
  rw ←orthogonal_projection_eq_self_iff,
  symmetry, assumption,
end


theorem lax_milgram (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  (lax_milgram_map B)
  (injective B coercive)
  (surjective B coercive)


end lax_milgram
