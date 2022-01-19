/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual
import analysis.normed_space.banach

/-!
# The Lax-Milgram Theorem


We consider an Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.
For every such form we define the
`lax_milgram_map : V →L[ℝ] V`,
which is defined by the property `B (lax_milgram_map B v) w = ⟪v, w⟫`
using the Fréchet-Riesz representation theorem.
We also define a property `is_coercive` for (B : V →L[ℝ] V →L[ℝ] ℝ),
such that `is_coercive B` iff
`∃ C, (0 < C) ∧ ∀ u, C * ∥u∥ * ∥u∥ ≤ B u u`.

Under the hypothesis that `B` i
we prove the Lax-Milgram theorem:
that is, the `lax_milgram_map` can be upgraded to a continuous equivalence `lax_milgram`

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]


## Tags

dual, Lax-Milgram
-/

noncomputable theory



open_locale classical complex_conjugate
open is_R_or_C continuous_linear_map linear_map linear_equiv

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
variables (B : V →L[ℝ] V →L[ℝ] ℝ)


/--
The Lax-;ilgram map of a bounded bilinear operator: for all `v : V`
there exists an `lax_milgram_map B v` is the element of `V`
such that `⟪lax_milgram_map B v, w⟫ = B v w`.
This element is obtained using `inner_product_space.to_dual`.
-/
def lax_milgram_map (B : V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V :=
(inner_product_space.to_dual ℝ V).symm.to_continuous_linear_equiv.to_continuous_linear_map ∘L B


@[simp]
lemma lax_milgram_map_apply (v w : V) : B v w = inner (lax_milgram_map B v) w :=
by {dunfold lax_milgram_map, simp,}

lemma unique_lax_milgram_map (v f : V)
  (is_lax_milgram : (∀ w, inner f w = B v w)) :
  f = lax_milgram_map B v :=
begin
  refine inner_product_space.ext_inner_right ℝ _,
  intro w,
  rw ←lax_milgram_map_apply,
  exact is_lax_milgram w,
end

variables {B}

lemma bounded_below (coercive : is_coercive B) :
  ∃ C, 0 < C ∧ ∀ v, C * ∥v∥ ≤ ∥lax_milgram_map B v∥ :=
begin
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  refine ⟨C, C_ge_0, _⟩,
  intro v,
  by_cases h : 0 < ∥v∥,
  {
    refine (mul_le_mul_right h).mp _,
    exact calc C * ∥v∥ * ∥v∥
               ≤ B v v                         : coercivity v
    ...        = inner (lax_milgram_map B v) v : by simp
    ...        ≤ ∥lax_milgram_map B v∥ * ∥v∥     : real_inner_le_norm (lax_milgram_map B v) v,
  },
  {
    have : v = 0 := by simpa using h,
    simp [this],
  }
end

lemma injective (coercive : is_coercive B) : (lax_milgram_map B).ker = ⊥ :=
begin
  simp only [submodule.eq_bot_iff, continuous_linear_map.mem_ker],
  intros v zero_of_image,
  rw ←norm_le_zero_iff,
  rcases bounded_below coercive with ⟨C, C_pos, bound⟩,
  have := bound v,
  rw [zero_of_image, norm_zero] at this,
  nlinarith,
end

lemma closed_range (coercive : is_coercive B) : is_closed ((lax_milgram_map B).range : set V) :=
begin
  rw ←is_seq_closed_iff_is_closed,
  apply is_seq_closed_of_def,
  intros y Y mem_range_y tendsto_y,
  obtain ⟨x, preimage_of_x⟩ : ∃ (x : ℕ → V), ∀ n, lax_milgram_map B (x n) = y n,
  begin
    have := λ n, classical.indefinite_description
      (λ x1, lax_milgram_map B x1 = y n)
      (linear_map.mem_range.mp $ mem_range_y n),
    use λ n, ↑(this n),
    intro n,
    exact (this n).property,
  end,
  have : cauchy_seq x,
  begin
      rw normed_group.cauchy_seq_iff,
      intros ε pos_ε,
      rw normed_group.tendsto_at_top' at tendsto_y,
      rcases bounded_below coercive with ⟨C, C_pos, bound⟩,
      have : 0 < C / 2 * ε := by nlinarith,
      rcases tendsto_y (C / 2 * ε) this with ⟨N, h⟩,
      use N+1,
      intros m _ n _,
      have N_lt_m : N < m := by linarith,
      have N_lt_n : N < n := by linarith,
      rw ←mul_lt_mul_left C_pos,
      exact calc C * ∥x m - x n∥
                 ≤ ∥lax_milgram_map B (x m - x n)∥ : bound (x m - x n)
      ...        = ∥y m - y n∥                     : by simp [preimage_of_x]
      ...        = ∥(y m - Y) + (Y - y n)∥         : by simp
      ...        ≤ ∥y m - Y∥ + ∥Y - y n∥            : norm_add_le (y m - Y) (Y - y n)
      ...        = ∥y m - Y∥ + ∥y n - Y∥            : by {rw ←norm_neg (Y - y n), simp}
      ...        < C / 2 * ε + C / 2 * ε          : by {exact add_lt_add (h m N_lt_m) (h n N_lt_n)}
      ...        = C * ε                          : by nlinarith,
  end,
  obtain ⟨X, tendsto_X⟩ : ∃ X, filter.tendsto x filter.at_top (nhds X)
    := cauchy_seq_tendsto_of_complete this,
  have : lax_milgram_map B X = Y,
  begin
    have tendsto_AX
      := filter.tendsto.comp (continuous.tendsto (lax_milgram_map B).continuous X) tendsto_X,
    have y_eq_comp : ⇑(lax_milgram_map B) ∘ x = y := by {ext n, simp [preimage_of_x],},
    rw y_eq_comp at tendsto_AX,
    exact tendsto_nhds_unique tendsto_AX tendsto_y,
  end,
  simp only [continuous_linear_map.mem_range, set_like.mem_coe],
  use X, assumption,
end

lemma surjective (coercive : is_coercive B): (lax_milgram_map B).range = ⊤ :=
begin
  haveI := (closed_range coercive).complete_space_coe,
  rw ← (lax_milgram_map B).range.orthogonal_orthogonal,
  rw submodule.eq_top_iff',
  intros v w mem_w_orthogonal,
  rcases coercive with ⟨C, C_ge_0, coercivity⟩,
  have : C * ∥w∥ * ∥w∥ ≤ 0 :=
  calc C * ∥w∥ * ∥w∥
        ≤ B w w                         : coercivity w
  ...  = inner (lax_milgram_map B w) w  : by simp
  ...  = 0                              : mem_w_orthogonal _ ⟨w, rfl⟩,
  have : ∥w∥ * ∥w∥ ≤ 0 := by nlinarith,
  have h : ∥w∥ = 0 := by nlinarith [norm_nonneg w],
  have w_eq_zero : w = 0 := by simpa using h,
  simp [w_eq_zero],
end


def lax_milgram (coercive : is_coercive B) : V ≃L[ℝ] V :=
continuous_linear_equiv.of_bijective
  (lax_milgram_map B)
  (injective coercive)
  (surjective coercive)


end lax_milgram
