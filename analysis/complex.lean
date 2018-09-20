/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Topology of the complex numbers.
-/
import data.complex.basic analysis.metric_space data.complex.exponential

noncomputable theory
open filter

namespace complex

-- TODO(Mario): these proofs are all copied from analysis/real. Generalize
-- to normed fields
instance : metric_space ℂ :=
{ dist               := λx y, (x - y).abs,
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, complex.abs_sub _ _,
  dist_triangle      := assume x y z, complex.abs_sub_le _ _ _ }

theorem dist_eq (x y : ℂ) : dist x y = (x - y).abs := rfl

theorem uniform_continuous_add : uniform_continuous (λp : ℂ × ℂ, p.1 + p.2) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h, let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ h₁ h₂⟩

theorem uniform_continuous_neg : uniform_continuous (@has_neg.neg ℂ _) :=
uniform_continuous_of_metric.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [dist_eq] using h⟩

instance : uniform_add_group ℂ :=
uniform_add_group.mk' uniform_continuous_add uniform_continuous_neg

instance : topological_add_group ℂ := by apply_instance

lemma uniform_continuous_inv (s : set ℂ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ abs x) :
  uniform_continuous (λp:s, p.1⁻¹) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0 in
⟨δ, δ0, λ a b h, Hδ (H _ a.2) (H _ b.2) h⟩

lemma uniform_continuous_abs : uniform_continuous (abs : ℂ → ℝ) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _)⟩

lemma continuous_abs : continuous (abs : ℂ → ℝ) :=
uniform_continuous_abs.continuous

lemma tendsto_inv {r : ℂ} (r0 : r ≠ 0) : tendsto (λq, q⁻¹) (nhds r) (nhds r⁻¹) :=
by rw ← abs_pos at r0; exact
tendsto_of_uniform_continuous_subtype
  (uniform_continuous_inv {x | abs r / 2 < abs x} (half_pos r0) (λ x h, le_of_lt h))
  (mem_nhds_sets (continuous_abs _ $ is_open_lt' (abs r / 2)) (half_lt_self r0))

lemma continuous_inv' : continuous (λa:{r:ℂ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_tendsto.mpr $ assume ⟨r, hr⟩,
  (continuous_iff_tendsto.mp continuous_subtype_val _).comp (tendsto_inv hr)

lemma continuous_inv {α} [topological_space α] {f : α → ℂ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℂ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from (continuous_subtype_mk _ hf).comp continuous_inv'

lemma uniform_continuous_mul_const {x : ℂ} : uniform_continuous ((*) x) :=
uniform_continuous_of_metric.2 $ λ ε ε0, begin
  cases no_top (abs x) with y xy,
  have y0 := lt_of_le_of_lt (abs_nonneg _) xy,
  refine ⟨_, div_pos ε0 y0, λ a b h, _⟩,
  rw [dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gt y0)],
  exact mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0
end

lemma uniform_continuous_mul (s : set (ℂ × ℂ))
  {r₁ r₂ : ℝ} (r₁0 : 0 < r₁) (r₂0 : 0 < r₂)
  (H : ∀ x ∈ s, abs (x : ℂ × ℂ).1 < r₁ ∧ abs x.2 < r₂) :
  uniform_continuous (λp:s, p.1.1 * p.1.2) :=
uniform_continuous_of_metric.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0 r₁0 r₂0 in
⟨δ, δ0, λ a b h,
  let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

lemma continuous_mul : continuous (λp : ℂ × ℂ, p.1 * p.2) :=
continuous_iff_tendsto.2 $ λ ⟨a₁, a₂⟩,
tendsto_of_uniform_continuous_subtype
  (uniform_continuous_mul
    ({x | abs x < abs a₁ + 1}.prod {x | abs x < abs a₂ + 1})
    (lt_of_le_of_lt (abs_nonneg _) (lt_add_one _))
    (lt_of_le_of_lt (abs_nonneg _) (lt_add_one _))
    (λ x, id))
  (mem_nhds_sets
    (is_open_prod
      (continuous_abs _ $ is_open_gt' _)
      (continuous_abs _ $ is_open_gt' _))
    ⟨lt_add_one (abs a₁), lt_add_one (abs a₂)⟩)

instance : topological_ring ℂ :=
{ continuous_mul := continuous_mul, ..complex.topological_add_group }

instance : topological_semiring ℂ := by apply_instance

section exponential

open finset

lemma abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) :
  abs (exp x - (x + 1)) ≤ abs x ^ 2 * (3 / 4) :=
calc abs (exp x - (x + 1)) = abs (exp x - (range 2).sum (λ m, x ^ m / m.fact)) :
  by simp [sum_range_succ]
... ≤ abs x ^ 2 * ((nat.succ 2) * (nat.fact 2 * 2)⁻¹) :
  exp_bound hx dec_trivial
... = abs x ^ 2 * (3 / 4) : by norm_num

lemma half_le_self {α : Type*} [linear_ordered_field α] {a : α} (ha : 0 ≤ a) : a / 2 ≤ a :=
by linarith

lemma tendsto_exp_zero_one : tendsto exp (nhds 0) (nhds 1) :=
tendsto_nhds_of_metric.2 $ λ ε ε0,
  ⟨min 1 (real.sqrt ε / 2), sorry,
    λ x hx,
    have hx' : abs x < min 1 (real.sqrt ε / 2), by simpa [dist_eq] using hx,
    calc abs (exp x - 1) ≤ abs (exp x - (x + 1)) + abs ((x + 1) - 1) :
      abs_sub_le _ _ _
    ... < abs x ^ 2 * (3 / 4) + real.sqrt ε / 2 :
      add_lt_add_of_le_of_lt (abs_exp_sub_one_le (le_trans (le_of_lt hx') (min_le_left _ _)))
        (by rw add_sub_cancel; exact (lt_of_lt_of_le hx' (min_le_right _ _)))
    ... ≤ (real.sqrt ε / 2) ^ 2 * (3 / 4) + real.sqrt ε / 2 :
      add_le_add_right (mul_le_mul_of_nonneg_right
        (by rw [pow_two, pow_two]; exact mul_self_le_mul_self (abs_nonneg _)
          (le_trans (le_of_lt hx') (min_le_right _ _)))
        (by norm_num)) _
    ... < ε : begin
      rw [div_pow, real.sqr_sqrt],

    end⟩

end exponential

end complex
