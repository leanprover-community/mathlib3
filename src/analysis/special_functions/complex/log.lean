/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.complex.arg
import analysis.special_functions.log.basic

/-!
# The complex `log` function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Basic properties, relationship with `exp`.
-/

noncomputable theory

namespace complex

open set filter

open_locale real topology complex_conjugate

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot] noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
lemma log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs.pos hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 $ abs.ne_zero hx), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 $ abs.ne_zero hx), re_add_im]

@[simp] lemma range_exp : range exp = {0}ᶜ :=
set.ext $ λ x, ⟨by { rintro ⟨x, rfl⟩, exact exp_ne_zero x }, λ hx, ⟨log x, exp_log hx⟩⟩

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
by rw [log, abs_exp, real.log_exp, exp_eq_exp_re_mul_sin_add_cos, ← of_real_exp,
  arg_mul_cos_add_sin_mul_I (real.exp_pos _) ⟨hx₁, hx₂⟩, re_add_im]

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [← log_exp hx₁ hx₂, ← log_exp hy₁ hy₂, hxy]

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

lemma log_of_real_re (x : ℝ) : (log (x : ℂ)).re = real.log x := by simp [log_re]

lemma log_of_real_mul {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) :
  log (r * x) = real.log r + log x :=
begin
  replace hx := complex.abs.ne_zero_iff.mpr hx,
  simp_rw [log, map_mul, abs_of_real, arg_real_mul _ hr, abs_of_pos hr, real.log_mul hr.ne' hx,
    of_real_add, add_assoc],
end

lemma log_mul_of_real (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) :
  log (x * r) = real.log r + log x :=
by rw [mul_comm, log_of_real_mul hr hx, add_comm]

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

lemma log_conj_eq_ite (x : ℂ) :
  log (conj x) = if x.arg = π then log x else conj (log x) :=
begin
  simp_rw [log, abs_conj, arg_conj, map_add, map_mul, conj_of_real],
  split_ifs with hx,
  { rw hx },
  simp_rw [of_real_neg, conj_I, mul_neg, neg_mul]
end

lemma log_conj (x : ℂ) (h : x.arg ≠ π) : log (conj x) = conj (log x) :=
by rw [log_conj_eq_ite, if_neg h]

lemma log_inv_eq_ite (x : ℂ) : log (x⁻¹) = if x.arg = π then -conj (log x) else -log x :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  rw [inv_def, log_mul_of_real, real.log_inv, of_real_neg, ←sub_eq_neg_add, log_conj_eq_ite],
  { simp_rw [log, map_add, map_mul, conj_of_real, conj_I, norm_sq_eq_abs, real.log_pow,
      nat.cast_two, of_real_mul, of_real_bit0, of_real_one, neg_add, mul_neg, two_mul, neg_neg],
    split_ifs,
    { rw [add_sub_right_comm, sub_add_cancel'] },
    { rw [add_sub_right_comm, sub_add_cancel'] } },
  { rwa [inv_pos, complex.norm_sq_pos] },
  { rwa map_ne_zero },
end

lemma log_inv (x : ℂ) (hx : x.arg ≠ π) : log (x⁻¹) = -log x :=
by rw [log_inv_eq_ite, if_neg hx]

lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 :=
by norm_num [real.pi_ne_zero, I_ne_zero]

lemma exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :=
begin
  split,
  { intro h,
    rcases exists_unique_add_zsmul_mem_Ioc real.two_pi_pos x.im (-π) with ⟨n, hn, -⟩,
    use -n,
    rw [int.cast_neg, neg_mul, eq_neg_iff_add_eq_zero],
    have : (x + n * (2 * π * I)).im ∈ Ioc (-π) π, by simpa [two_mul, mul_add] using hn,
    rw [← log_exp this.1 this.2, exp_periodic.int_mul n, h, log_one] },
  { rintro ⟨n, rfl⟩, exact (exp_periodic.int_mul n).eq.trans exp_zero }
end

lemma exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
by rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

lemma exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * ((2 * π) * I) :=
by simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

@[simp] lemma countable_preimage_exp {s : set ℂ} : (exp ⁻¹' s).countable ↔ s.countable :=
begin
  refine ⟨λ hs, _, λ hs, _⟩,
  { refine ((hs.image exp).insert 0).mono _,
    rw [image_preimage_eq_inter_range, range_exp, ← diff_eq, ← union_singleton, diff_union_self],
    exact subset_union_left _ _ },
  { rw ← bUnion_preimage_singleton,
    refine hs.bUnion (λ z hz, _),
    rcases em (∃ w, exp w = z) with ⟨w, rfl⟩|hne,
    { simp only [preimage, mem_singleton_iff, exp_eq_exp_iff_exists_int, set_of_exists],
      exact countable_Union (λ m, countable_singleton _) },
    { push_neg at hne, simp [preimage, hne] } }
end

alias countable_preimage_exp ↔ _ _root_.set.countable.preimage_cexp

lemma tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto log (𝓝[{z : ℂ | z.im < 0}] z) (𝓝 $ real.log (abs z) - π * I) :=
begin
  have := (continuous_of_real.continuous_at.comp_continuous_within_at
    (continuous_abs.continuous_within_at.log _)).tendsto.add
    (((continuous_of_real.tendsto _).comp $
    tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero hre him).mul tendsto_const_nhds),
  convert this,
  { simp [sub_eq_add_neg] },
  { lift z to ℝ using him, simpa using hre.ne }
end

lemma continuous_within_at_log_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  continuous_within_at log {z : ℂ | 0 ≤ z.im} z :=
begin
  have := (continuous_of_real.continuous_at.comp_continuous_within_at
    (continuous_abs.continuous_within_at.log _)).tendsto.add
    ((continuous_of_real.continuous_at.comp_continuous_within_at $
    continuous_within_at_arg_of_re_neg_of_im_zero hre him).mul tendsto_const_nhds),
  convert this,
  { lift z to ℝ using him, simpa using hre.ne }
end

lemma tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto log (𝓝[{z : ℂ | 0 ≤ z.im}] z) (𝓝 $ real.log (abs z) + π * I) :=
by simpa only [log, arg_eq_pi_iff.2 ⟨hre, him⟩]
  using (continuous_within_at_log_of_re_neg_of_im_zero hre him).tendsto

@[simp] lemma map_exp_comap_re_at_bot : map exp (comap re at_bot) = 𝓝[≠] 0 :=
by rw [← comap_exp_nhds_zero, map_comap, range_exp, nhds_within]

@[simp] lemma map_exp_comap_re_at_top : map exp (comap re at_top) = comap abs at_top :=
begin
  rw [← comap_exp_comap_abs_at_top, map_comap, range_exp, inf_eq_left, le_principal_iff],
  exact eventually_ne_of_tendsto_norm_at_top tendsto_comap 0
end

end complex

section log_deriv

open complex filter
open_locale topology

variables {α : Type*}

lemma continuous_at_clog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
  continuous_at log x :=
begin
  refine continuous_at.add _ _,
  { refine continuous_of_real.continuous_at.comp _,
    refine (real.continuous_at_log _).comp complex.continuous_abs.continuous_at,
    rw complex.abs.ne_zero_iff,
    rintro rfl,
    simpa using h },
  { have h_cont_mul : continuous (λ x : ℂ, x * I), from continuous_id'.mul continuous_const,
    refine h_cont_mul.continuous_at.comp (continuous_of_real.continuous_at.comp _),
    exact continuous_at_arg h, },
end

lemma filter.tendsto.clog {l : filter α} {f : α → ℂ} {x : ℂ} (h : tendsto f l (𝓝 x))
  (hx : 0 < x.re ∨ x.im ≠ 0) :
  tendsto (λ t, log (f t)) l (𝓝 $ log x) :=
(continuous_at_clog hx).tendsto.comp h

variables [topological_space α]

lemma continuous_at.clog {f : α → ℂ} {x : α} (h₁ : continuous_at f x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_at (λ t, log (f t)) x :=
h₁.clog h₂

lemma continuous_within_at.clog {f : α → ℂ} {s : set α} {x : α} (h₁ : continuous_within_at f s x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_within_at (λ t, log (f t)) s x :=
h₁.clog h₂

lemma continuous_on.clog {f : α → ℂ} {s : set α} (h₁ : continuous_on f s)
  (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_on (λ t, log (f t)) s :=
λ x hx, (h₁ x hx).clog (h₂ x hx)

lemma continuous.clog {f : α → ℂ} (h₁ : continuous f) (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous (λ t, log (f t)) :=
continuous_iff_continuous_at.2 $ λ x, h₁.continuous_at.clog (h₂ x)

end log_deriv
