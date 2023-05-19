/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.integrals
import analysis.special_functions.non_integrable

/-!
# Non-integrability of inverses

In this file we prove integrability conditions for `(x - c)⁻¹` and `x⁻¹`.

## Main results

* `interval_integrable_sub_inv_iff`, `interval_integrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/

open_locale interval
open measure_theory filter asymptotics interval_integral

/-- The function `λ x, (x - c)⁻¹` is integrable on `a..b` if and only if `a = b` or `c ∉ [a, b]`. -/
@[simp] lemma interval_integrable_sub_inv_iff {a b c : ℝ} :
  interval_integrable (λ x, (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [a, b] :=
begin
  split,
  { refine λ h, or_iff_not_imp_left.2 (λ hne hc, _),
    exact not_interval_integrable_of_sub_inv_is_O_punctured (is_O_refl _ _) hne hc h },
  { rintro (rfl|h₀),
    exacts [interval_integrable.refl,
      interval_integrable_inv (λ x hx, sub_ne_zero.2 $ ne_of_mem_of_not_mem hx h₀)
        (continuous_on_id.sub continuous_on_const)] }
end

/-- The function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or `0 ∉ [a, b]`. -/
@[simp] lemma interval_integrable_inv_iff {a b : ℝ} :
  interval_integrable (λ x, x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [a, b] :=
by simp only [← interval_integrable_sub_inv_iff, sub_zero]
