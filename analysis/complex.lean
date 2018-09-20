/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Topology of the complex numbers.
-/
import data.complex.basic analysis.metric_space data.complex.exponential analysis.real

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

lemma continuous_re : continuous re :=
continuous_of_metric.2 (λ _ ε ε0, ⟨ε, ε0, λ _, lt_of_le_of_lt (abs_re_le_abs _)⟩)

lemma continuous_im : continuous im :=
continuous_of_metric.2 (λ _ ε ε0, ⟨ε, ε0, λ _, lt_of_le_of_lt (abs_im_le_abs _)⟩)

lemma continuous_of_real : continuous of_real :=
continuous_of_metric.2 (λ _ ε ε0, ⟨ε, ε0, λ _,
  by rw [real.dist_eq, complex.dist_eq, of_real_eq_coe, of_real_eq_coe, ← of_real_sub, abs_of_real];
    exact id⟩)


instance : topological_ring ℂ :=
{ continuous_mul := continuous_mul, ..complex.topological_add_group }

instance : topological_semiring ℂ := by apply_instance

open finset

lemma abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) :
  abs (exp x - 1) ≤ 2 * abs x :=
calc abs (exp x - 1) = abs (exp x - (range 1).sum (λ m, x ^ m / m.fact)) :
  by simp [sum_range_succ]
... ≤ abs x ^ 1 * ((nat.succ 1) * (nat.fact 1 * 1)⁻¹) :
  exp_bound hx dec_trivial
... = 2 * abs x : by simp [bit0, mul_comm]

lemma tendsto_exp_zero_one : tendsto (λ x : ℂ, exp x) (nhds (0 : ℂ)) (nhds (1 : ℂ)) :=
tendsto_nhds_of_metric.2 $ λ ε ε0,
  ⟨min (ε / 2) 1, lt_min (div_pos ε0 (by norm_num)) (by norm_num),
    λ x h, have h : abs x < min (ε / 2) 1, by simpa [dist_eq] using h,
      calc abs (exp x - 1) ≤ 2 * abs x : abs_exp_sub_one_le
        (le_trans (le_of_lt h) (min_le_right _ _))
      ... = abs x + abs x : two_mul (abs x)
      ... < ε / 2 + ε / 2 : add_lt_add
        (lt_of_lt_of_le h (min_le_left _ _)) (lt_of_lt_of_le h (min_le_left _ _))
      ... = ε : by rw add_halves⟩

lemma continuous_exp : continuous exp :=
continuous_iff_tendsto.2 (λ x,
  have H1 : tendsto (λ h, exp (x + h)) (nhds 0) (nhds (exp x)),
    by simpa [exp_add] using tendsto_mul tendsto_const_nhds tendsto_exp_zero_one,
  have H2 : tendsto (λ y, y - x) (nhds x) (nhds (x - x)) :=
     tendsto_sub tendsto_id (@tendsto_const_nhds _ _ _ x _),
  suffices tendsto ((λ h, exp (x + h)) ∘
    (λ y, id y - (λ z, x) y)) (nhds x) (nhds (exp x)),
    by simp only [function.comp, add_sub_cancel'_right, id.def] at this;
      exact this,
  tendsto.comp (by rw [sub_self] at H2; exact H2) H1)

lemma continuous_sin : continuous sin :=
_root_.continuous_mul
  (_root_.continuous_mul
    (_root_.continuous_sub
      (continuous.comp (_root_.continuous_mul continuous_neg' continuous_const) continuous_exp)
      (continuous.comp (_root_.continuous_mul continuous_id continuous_const) continuous_exp))
    continuous_const)
  continuous_const

lemma continuous_cos : continuous cos :=
_root_.continuous_mul
  (_root_.continuous_add
    (continuous.comp (_root_.continuous_mul continuous_id continuous_const) continuous_exp)
    (continuous.comp (_root_.continuous_mul continuous_neg' continuous_const) continuous_exp))
  continuous_const

lemma continuous_sinh : continuous sinh :=
_root_.continuous_mul
  (_root_.continuous_sub
    continuous_exp
    (continuous.comp continuous_neg' continuous_exp))
  continuous_const

lemma continuous_cosh : continuous cosh :=
_root_.continuous_mul
  (_root_.continuous_add
    continuous_exp
    (continuous.comp continuous_neg' continuous_exp))
  continuous_const

end complex

namespace real

lemma continuous_exp : continuous exp :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_exp)
  complex.continuous_re

lemma continuous_sin : continuous sin :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_sin)
  complex.continuous_re

lemma continuous_cos : continuous cos :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_cos)
  complex.continuous_re

lemma continuous_sinh : continuous sinh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_sinh)
  complex.continuous_re

lemma continuous_cosh : continuous cosh :=
continuous.comp
  (continuous.comp complex.continuous_of_real complex.continuous_cosh)
  complex.continuous_re

lemma exists_cos_eq_zero : ∃ x, 1 ≤ x ∧ x ≤ 2 ∧ cos x = 0 :=
real.exists_eq_zero_of_tendsto_of_zero_le_of_le_zero
  (λ x _ _, continuous_iff_tendsto.1 continuous_cos _)
  (le_of_lt complex.cos_one_pos)
  (le_of_lt complex.cos_two_neg) (by norm_num)

def pi : ℝ := 2 * classical.some exists_cos_eq_zero

end real