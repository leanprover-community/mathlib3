/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Topology of the complex numbers.
-/
import data.complex.basic
import topology.instances.real

noncomputable theory
open filter metric
open_locale topological_space

namespace complex

-- TODO(Mario): these proofs are all copied from analysis/real. Generalize
-- to normed fields
instance : metric_space ℂ :=
{ dist               := λx y, (x - y).abs,
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [sub_eq_zero],
  dist_comm          := assume x y, complex.abs_sub _ _,
  dist_triangle      := assume x y z, complex.abs_sub_le _ _ _ }

theorem dist_eq (x y : ℂ) : dist x y = (x - y).abs := rfl

theorem uniform_continuous_add : uniform_continuous (λp : ℂ × ℂ, p.1 + p.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h, let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ h₁ h₂⟩

theorem uniform_continuous_neg : uniform_continuous (@has_neg.neg ℂ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [dist_eq] using h⟩

instance : uniform_add_group ℂ :=
uniform_add_group.mk' uniform_continuous_add uniform_continuous_neg

instance : topological_add_group ℂ := by apply_instance -- short-circuit type class inference

lemma uniform_continuous_inv (s : set ℂ) {r : ℝ} (r0 : 0 < r) (H : ∀ x ∈ s, r ≤ abs x) :
  uniform_continuous (λp:s, p.1⁻¹) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0 in
⟨δ, δ0, λ a b h, Hδ (H _ a.2) (H _ b.2) h⟩

lemma uniform_continuous_abs : uniform_continuous (abs : ℂ → ℝ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _)⟩

lemma continuous_abs : continuous (abs : ℂ → ℝ) :=
uniform_continuous_abs.continuous

lemma tendsto_inv {r : ℂ} (r0 : r ≠ 0) : tendsto (λq, q⁻¹) (𝓝 r) (𝓝 r⁻¹) :=
by rw ← abs_pos at r0; exact
tendsto_of_uniform_continuous_subtype
  (uniform_continuous_inv {x | abs r / 2 < abs x} (half_pos r0) (λ x h, le_of_lt h))
  (mem_nhds_sets (continuous_abs _ $ is_open_lt' (abs r / 2)) (half_lt_self r0))

lemma continuous_inv : continuous (λa:{r:ℂ // r ≠ 0}, a.val⁻¹) :=
continuous_iff_continuous_at.mpr $ assume ⟨r, hr⟩,
  tendsto.comp (tendsto_inv hr) (continuous_iff_continuous_at.mp continuous_subtype_val _)

lemma continuous.inv {α} [topological_space α] {f : α → ℂ} (h : ∀a, f a ≠ 0) (hf : continuous f) :
  continuous (λa, (f a)⁻¹) :=
show continuous ((has_inv.inv ∘ @subtype.val ℂ (λr, r ≠ 0)) ∘ λa, ⟨f a, h a⟩),
  from continuous_inv.comp (continuous_subtype_mk _ hf)

lemma uniform_continuous_mul_const {x : ℂ} : uniform_continuous ((*) x) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, begin
  cases no_top (abs x) with y xy,
  have y0 := lt_of_le_of_lt (abs_nonneg _) xy,
  refine ⟨_, div_pos ε0 y0, λ a b h, _⟩,
  rw [dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gt y0)],
  exact mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0
end

lemma uniform_continuous_mul (s : set (ℂ × ℂ))
  {r₁ r₂ : ℝ} (H : ∀ x ∈ s, abs (x : ℂ × ℂ).1 < r₁ ∧ abs x.2 < r₂) :
  uniform_continuous (λp:s, p.1.1 * p.1.2) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0 in
⟨δ, δ0, λ a b h,
  let ⟨h₁, h₂⟩ := max_lt_iff.1 h in Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

protected lemma continuous_mul : continuous (λp : ℂ × ℂ, p.1 * p.2) :=
continuous_iff_continuous_at.2 $ λ ⟨a₁, a₂⟩,
tendsto_of_uniform_continuous_subtype
  (uniform_continuous_mul
    ({x | abs x < abs a₁ + 1}.prod {x | abs x < abs a₂ + 1})
    (λ x, id))
  (mem_nhds_sets
    (is_open_prod
      (continuous_abs _ $ is_open_gt' (abs a₁ + 1))
      (continuous_abs _ $ is_open_gt' (abs a₂ + 1)))
    ⟨lt_add_one (abs a₁), lt_add_one (abs a₂)⟩)

local attribute [semireducible] real.le

lemma uniform_continuous_re : uniform_continuous re :=
metric.uniform_continuous_iff.2 (λ ε ε0, ⟨ε, ε0, λ _ _, lt_of_le_of_lt (abs_re_le_abs _)⟩)

lemma continuous_re : continuous re := uniform_continuous_re.continuous

lemma uniform_continuous_im : uniform_continuous im :=
metric.uniform_continuous_iff.2 (λ ε ε0, ⟨ε, ε0, λ _ _, lt_of_le_of_lt (abs_im_le_abs _)⟩)

lemma continuous_im : continuous im := uniform_continuous_im.continuous

lemma uniform_continuous_of_real : uniform_continuous of_real :=
metric.uniform_continuous_iff.2 (λ ε ε0, ⟨ε, ε0, λ _ _,
  by rw [real.dist_eq, complex.dist_eq, of_real_eq_coe, of_real_eq_coe, ← of_real_sub, abs_of_real];
    exact id⟩)

lemma continuous_of_real : continuous of_real := uniform_continuous_of_real.continuous

instance : topological_ring ℂ :=
{ continuous_mul := complex.continuous_mul, ..complex.topological_add_group }

instance : topological_semiring ℂ := by apply_instance -- short-circuit type class inference

/-- `ℂ` is homeomorphic to the real plane with `max` norm. -/
def real_prod_homeo : ℂ ≃ₜ (ℝ × ℝ) :=
{ to_equiv := equiv_real_prod,
  continuous_to_fun := continuous_re.prod_mk continuous_im,
  continuous_inv_fun := show continuous (λ p : ℝ × ℝ, complex.mk p.1 p.2),
    by simp only [mk_eq_add_mul_I]; exact
      (continuous_of_real.comp continuous_fst).add
      ((continuous_of_real.comp continuous_snd).mul continuous_const) }

instance : proper_space ℂ :=
⟨λx r, begin
  refine real_prod_homeo.symm.compact_preimage.1
    (compact_of_is_closed_subset
      ((proper_space.compact_ball x.re r).prod (proper_space.compact_ball x.im r))
      (continuous_iff_is_closed.1 real_prod_homeo.symm.continuous _ is_closed_ball) _),
  exact λ p h, ⟨
    le_trans (abs_re_le_abs (⟨p.1, p.2⟩ - x)) h,
    le_trans (abs_im_le_abs (⟨p.1, p.2⟩ - x)) h⟩
end⟩

end complex
