/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach
import topology.metric_space.antilipschitz

/-!
# The Lax-Milgram Theorem


We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.
For every such form we define the
`continuous_linear_map_of_bilin : V →L[ℝ] V`,
which is defined by the property `⟪lax_milgram_map B v, w⟫ = B v w`
using the Fréchet-Riesz representation theorem.
We also define a property `is_coercive` for `B : V →L[ℝ] V →L[ℝ] ℝ`,
such that `is_coercive B` iff
`∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u`.

Under the hypothesis that `B` is coercive
we prove the Lax-Milgram theorem:
that is, the `continuous_linear_map_of_bilin` can be upgraded
to a continuous equivalence `lax_milgram_equiv : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]


## Tags

dual, Lax-Milgram
-/

noncomputable theory




open is_R_or_C continuous_linear_map linear_map linear_equiv inner_product_space
open_locale classical complex_conjugate inner_product_space.sharp

universe u

/--
A bounded bilinear form in an inner product space is coercive
if there is some positive constant C such that `C * ∥u∥ * ∥u∥ ≤ B u u`.
-/
def is_coercive
  {V : Type u} [inner_product_space ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u

namespace lax_milgram
variables {V : Type u} [inner_product_space ℝ V] [complete_space V]
variables {B : V →L[ℝ] V →L[ℝ] ℝ}


lemma bounded_below (coercive : is_coercive B) :
  ∃ C, 0 < C ∧ ∀ v, C * ∥v∥ ≤ ∥(B♯ : V →L[ℝ] V) v∥ :=
begin
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  refine ⟨C, C_ge_0, _⟩,
  intro v,
  by_cases h : 0 < ∥v∥,
  {
    refine (mul_le_mul_right h).mp _,
    exact calc C * ∥v∥ * ∥v∥
               ≤ B v v                         : coercivity v
    ...        = inner ((B♯ : V →L[ℝ] V) v) v : by simp
    ...        ≤ ∥(B♯ : V →L[ℝ] V) v∥ * ∥v∥     : real_inner_le_norm ((B♯ : V →L[ℝ] V) v) v,
  },
  {
    have : v = 0 := by simpa using h,
    simp [this],
  }
end

lemma antilipschitz_of_lax_milgram (coercive : is_coercive B) :
  ∃ C : nnreal, 0 < C ∧ antilipschitz_with C (B♯ : V →L[ℝ] V) :=
begin
  rcases bounded_below coercive with ⟨C, C_pos, below_bound⟩,
  refine ⟨(C⁻¹).to_nnreal, real.to_nnreal_pos.mpr (inv_pos.mpr C_pos), _⟩,
  refine linear_map.antilipschitz_of_bound (B♯ : V →L[ℝ] V) _,
  simp_rw [real.coe_to_nnreal',
    max_eq_left_of_lt (inv_pos.mpr C_pos),
    ←inv_mul_le_iff (inv_pos.mpr C_pos)],
  simpa using below_bound,
end

lemma ker_eq_bot (coercive : is_coercive B) : (B♯ : V →L[ℝ] V).ker = ⊥ :=
begin
  rw [←ker_coe, linear_map.ker_eq_bot],
  rcases antilipschitz_of_lax_milgram coercive with ⟨_, _, antilipschitz⟩,
  exact antilipschitz_with.injective antilipschitz,
end

lemma closed_range (coercive : is_coercive B) : is_closed ((B♯ : V →L[ℝ] V).range : set V) :=
begin
  rcases antilipschitz_of_lax_milgram coercive with ⟨_, _, antilipschitz⟩,
  exact antilipschitz.is_closed_range (B♯ : V →L[ℝ] V).uniform_continuous,
end

lemma range_eq_top (coercive : is_coercive B): (B♯ : V →L[ℝ] V).range = ⊤ :=
begin
  haveI := (closed_range coercive).complete_space_coe,
  rw ← (B♯ : V →L[ℝ] V).range.orthogonal_orthogonal,
  rw submodule.eq_top_iff',
  intros v w mem_w_orthogonal,
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  have : C * ∥w∥ * ∥w∥ ≤ 0 :=
  calc C * ∥w∥ * ∥w∥
        ≤ B w w                         : coercivity w
  ...  = inner ((B♯ : V →L[ℝ] V) w) w   : by simp
  ...  = 0                              : mem_w_orthogonal _ ⟨w, rfl⟩,
  have : ∥w∥ * ∥w∥ ≤ 0 := by nlinarith,
  have h : ∥w∥ = 0 := by nlinarith [norm_nonneg w],
  have w_eq_zero : w = 0 := by simpa using h,
  simp [w_eq_zero],
end

/--
The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `lax_milgram_equiv B v` is the unique element `V`
such that `⟪lax_milgram_equiv B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def continuous_linear_equiv_of_bilin (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  (B♯)
  (ker_eq_bot coercive)
  (range_eq_top coercive)


@[simp]
lemma continuous_linear_equiv_of_bilin_apply (coercive : is_coercive B) (v w : V) :
  inner (continuous_linear_equiv_of_bilin coercive v) w = B v w :=
continuous_linear_map_of_bilin_apply B v w

lemma continuous_linear_equiv_of_bilin_equiv (coercive : is_coercive B) {v f : V}
  (is_lax_milgram : (∀ w, inner f w = B v w)) :
  f = continuous_linear_equiv_of_bilin coercive v :=
unique_continuous_linear_map_of_bilin ℝ B is_lax_milgram

end lax_milgram
