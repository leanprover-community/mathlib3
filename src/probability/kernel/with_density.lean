/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import probability.kernel.measurable_integral

/-!
# With Density

For an s-finite kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` which is finite
everywhere, we define `with_density κ f` as the kernel `a ↦ (κ a).with_density (f a)`. This is
an s-finite kernel.

## Main definitions

* `kernel.with_density κ (f : α → β → ℝ≥0∞)`: kernel `a ↦ (κ a).with_density (f a)`.
  It is defined if `κ` is s-finite. If `f` is finite everywhere, then this is also an s-finite
  kernel. The class of s-finite kernels is the smallest class of kernels that contains finite
  kernels and which is stable by `with_density`.
  Integral: `∫⁻ b, g b ∂(with_density κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `lintegral_with_density`: `∫⁻ b, g b ∂(with_density κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

-/

open measure_theory probability_theory

open_locale measure_theory ennreal nnreal big_operators

namespace probability_theory.kernel

variables {α β ι : Type*} {mα : measurable_space α} {mβ : measurable_space β}

include mα mβ

variables {κ : kernel α β} {f : α → β → ℝ≥0∞}

/-- Kernel with image `(κ a).with_density (f a)` if `function.uncurry f` is measurable, and
with image 0 otherwise. If `function.uncurry f` is measurable, it satisfies
`∫⁻ b, g b ∂(with_density κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`. -/
noncomputable
def with_density (κ : kernel α β) [is_s_finite_kernel κ] (f : α → β → ℝ≥0∞) :
  kernel α β :=
@dite _ (measurable (function.uncurry f)) (classical.dec _)
  (λ hf, ({ val := λ a, (κ a).with_density (f a),
    property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      simp_rw with_density_apply _ hs,
      exact measurable_set_lintegral κ hf hs,
    end, } : kernel α β))
  (λ hf, 0)

lemma with_density_of_not_measurable (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : ¬ measurable (function.uncurry f)) :
  with_density κ f = 0 :=
by { classical, exact dif_neg hf, }

protected lemma with_density_apply (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) :
  with_density κ f a = (κ a).with_density (f a) :=
by { classical, rw [with_density, dif_pos hf], refl, }

lemma with_density_apply' (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) {s : set β} (hs : measurable_set s) :
  with_density κ f a s = ∫⁻ b in s, f a b ∂(κ a) :=
by rw [kernel.with_density_apply κ hf, with_density_apply _ hs]

lemma lintegral_with_density (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) {g : β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ b, g b ∂(with_density κ f a) = ∫⁻ b, f a b * g b ∂(κ a) :=
begin
  rw [kernel.with_density_apply _ hf,
    lintegral_with_density_eq_lintegral_mul _ (measurable.of_uncurry_left hf) hg],
  simp_rw pi.mul_apply,
end

lemma with_density_add_left (κ η : kernel α β) [is_s_finite_kernel κ] [is_s_finite_kernel η]
  (f : α → β → ℝ≥0∞) :
  with_density (κ + η) f = with_density κ f + with_density η f :=
begin
  by_cases hf : measurable (function.uncurry f),
  { ext a s hs : 2,
    simp only [kernel.with_density_apply _ hf, coe_fn_add, pi.add_apply, with_density_add_measure,
      measure.add_apply], },
  { simp_rw [with_density_of_not_measurable _ hf],
    rw zero_add, },
end

lemma with_density_kernel_sum [countable ι] (κ : ι → kernel α β)
  (hκ : ∀ i, is_s_finite_kernel (κ i)) (f : α → β → ℝ≥0∞) :
  @with_density _ _ _ _ (kernel.sum κ) (is_s_finite_kernel_sum hκ) f
    = kernel.sum (λ i, with_density (κ i) f) :=
begin
  by_cases hf : measurable (function.uncurry f),
  { ext1 a,
    simp_rw [sum_apply, kernel.with_density_apply _ hf, sum_apply,
      with_density_sum (λ n, κ n a) (f a)], },
  { simp_rw [with_density_of_not_measurable _ hf],
    exact sum_zero.symm, },
end

lemma with_density_tsum [countable ι] (κ : kernel α β) [is_s_finite_kernel κ]
  {f : ι → α → β → ℝ≥0∞} (hf : ∀ i, measurable (function.uncurry (f i))) :
  with_density κ (∑' n, f n) = kernel.sum (λ n, with_density κ (f n)) :=
begin
  have h_sum_a : ∀ a, summable (λ n, f n a) := λ a, pi.summable.mpr (λ b, ennreal.summable),
  have h_sum : summable (λ n, f n) := pi.summable.mpr h_sum_a,
  ext a s hs : 2,
  rw [sum_apply' _ a hs, with_density_apply' κ _ a hs],
  swap,
  { have : function.uncurry (∑' n, f n) = ∑' n, function.uncurry (f n),
    { ext1 p,
      simp only [function.uncurry_def],
      rw [tsum_apply h_sum, tsum_apply (h_sum_a _), tsum_apply],
      exact pi.summable.mpr (λ p, ennreal.summable), },
    rw this,
    exact measurable.ennreal_tsum' hf, },
  have : ∫⁻ b in s, (∑' n, f n) a b ∂(κ a) = ∫⁻ b in s, (∑' n, (λ b, f n a b) b) ∂(κ a),
  { congr' with b,
    rw [tsum_apply h_sum, tsum_apply (h_sum_a a)], },
  rw [this, lintegral_tsum (λ n, (measurable.of_uncurry_left (hf n)).ae_measurable)],
  congr' with n,
  rw with_density_apply' _ (hf n) a hs,
end

/-- If a kernel `κ` is finite and a function `f : α → β → ℝ≥0∞` is bounded, then `with_density κ f`
is finite. -/
lemma is_finite_kernel_with_density_of_bounded (κ : kernel α β) [is_finite_kernel κ]
  {B : ℝ≥0∞} (hB_top : B ≠ ∞) (hf_B : ∀ a b, f a b ≤ B) :
  is_finite_kernel (with_density κ f) :=
begin
  by_cases hf : measurable (function.uncurry f),
  { exact
      ⟨⟨B * is_finite_kernel.bound κ, ennreal.mul_lt_top hB_top (is_finite_kernel.bound_ne_top κ),
        λ a,
        begin
          rw with_density_apply' κ hf a measurable_set.univ,
          calc ∫⁻ b in set.univ, f a b ∂(κ a)
              ≤ ∫⁻ b in set.univ, B ∂(κ a) : lintegral_mono (hf_B a)
          ... = B * κ a set.univ :
            by simp only [measure.restrict_univ, measure_theory.lintegral_const]
          ... ≤ B * is_finite_kernel.bound κ :
            mul_le_mul_left' (measure_le_bound κ a set.univ) _,
        end⟩⟩, },
  { rw with_density_of_not_measurable _ hf,
    apply_instance, },
end

/-- Auxiliary lemma for `is_s_finite_kernel_with_density`.
If a kernel `κ` is finite, then `with_density κ f` is s-finite. -/
lemma is_s_finite_kernel_with_density_of_is_finite_kernel (κ : kernel α β) [is_finite_kernel κ]
  (hf_ne_top : ∀ a b, f a b ≠ ∞) :
  is_s_finite_kernel (with_density κ f) :=
begin
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `with_density κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `with_density` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : measurable (function.uncurry f),
  swap, { rw with_density_of_not_measurable _ hf, apply_instance, },
  let fs : ℕ → α → β → ℝ≥0∞ := λ n a b, min (f a b) (n + 1) - min (f a b) n,
  have h_le : ∀ a b n, ⌈(f a b).to_real⌉₊ ≤ n → f a b ≤ n,
  { intros a b n hn,
    have : (f a b).to_real ≤ n := nat.le_of_ceil_le hn,
    rw ← ennreal.le_of_real_iff_to_real_le (hf_ne_top a b) _ at this,
    { refine this.trans (le_of_eq _),
      rw ennreal.of_real_coe_nat, },
    { norm_cast,
      exact zero_le _, }, },
  have h_zero : ∀ a b n, ⌈(f a b).to_real⌉₊ ≤ n → fs n a b = 0,
  { intros a b n hn,
    suffices : min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b,
    { simp_rw [fs, this.1, this.2, tsub_self (f a b)], },
    exact ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
      min_eq_left (h_le a b n hn)⟩, },
  have hf_eq_tsum : f = ∑' n, fs n,
  { have h_sum_a : ∀ a, summable (λ n, fs n a),
    { refine λ a, pi.summable.mpr (λ b, _),
      suffices : ∀ n, n ∉ finset.range ⌈(f a b).to_real⌉₊ → fs n a b = 0,
        from summable_of_ne_finset_zero this,
      intros n hn_not_mem,
      rw [finset.mem_range, not_lt] at hn_not_mem,
      exact h_zero a b n hn_not_mem, },
    ext a b : 2,
    rw [tsum_apply (pi.summable.mpr h_sum_a), tsum_apply (h_sum_a a),
      ennreal.tsum_eq_liminf_sum_nat],
    have h_finset_sum : ∀ n, ∑ i in finset.range n, fs i a b = min (f a b) n,
    { intros n,
      induction n with n hn,
      { simp only [finset.range_zero, finset.sum_empty, algebra_map.coe_zero, min_zero], },
      rw [finset.sum_range_succ, hn],
      simp_rw [fs],
      norm_cast,
      rw add_tsub_cancel_iff_le,
      refine min_le_min le_rfl _,
      norm_cast,
      exact nat.le_succ n, },
    simp_rw h_finset_sum,
    refine (filter.tendsto.liminf_eq _).symm,
    refine filter.tendsto.congr' _ tendsto_const_nhds,
    rw [filter.eventually_eq, filter.eventually_at_top],
    exact ⟨⌈(f a b).to_real⌉₊, λ n hn, (min_eq_left (h_le a b n hn)).symm⟩, },
  rw [hf_eq_tsum, with_density_tsum _ (λ (n : ℕ), _)],
  swap, { exact (hf.min measurable_const).sub (hf.min measurable_const), },
  refine is_s_finite_kernel_sum (λ n, _),
  suffices : is_finite_kernel (with_density κ (fs n)), by { haveI := this, apply_instance, },
  refine is_finite_kernel_with_density_of_bounded _ (ennreal.coe_ne_top : (↑n + 1) ≠ ∞) (λ a b, _),
  norm_cast,
  calc fs n a b ≤ min (f a b) (n + 1) : tsub_le_self
            ... ≤ (n + 1) : min_le_right _ _
            ... = ↑(n + 1) : by norm_cast,
end

/-- For a s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is everywhere finite,
`with_density κ f` is s-finite. -/
theorem is_s_finite_kernel.with_density (κ : kernel α β) [is_s_finite_kernel κ]
  (hf_ne_top : ∀ a b, f a b ≠ ∞) :
  is_s_finite_kernel (with_density κ f) :=
begin
  have h_eq_sum : with_density κ f = kernel.sum (λ i, with_density (seq κ i) f),
  { rw ← with_density_kernel_sum _ _,
    congr,
    exact (kernel_sum_seq κ).symm, },
  rw h_eq_sum,
  exact is_s_finite_kernel_sum
    (λ n, is_s_finite_kernel_with_density_of_is_finite_kernel (seq κ n) hf_ne_top),
end

/-- For a s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `with_density κ f` is s-finite. -/
instance (κ : kernel α β) [is_s_finite_kernel κ] (f : α → β → ℝ≥0) :
  is_s_finite_kernel (with_density κ (λ a b, f a b)) :=
is_s_finite_kernel.with_density κ (λ _ _, ennreal.coe_ne_top)


end probability_theory.kernel
