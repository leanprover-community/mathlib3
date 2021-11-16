/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.inverse
import analysis.special_functions.trigonometric.deriv

/-!
# derivatives of the inverse trigonometric functions

Derivatives of `arcsin` and `arccos`.
-/

noncomputable theory
open_locale classical topological_space filter
open set filter

open_locale real

namespace real

section arcsin

lemma deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x ∧ times_cont_diff_at ℝ ⊤ arcsin x :=
begin
  cases h₁.lt_or_lt with h₁ h₁,
  { have : 1 - x ^ 2 < 0, by nlinarith [h₁],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, -(π / 2) :=
      (gt_mem_nhds h₁).mono (λ y hy, arcsin_of_le_neg_one hy.le),
    exact ⟨(has_strict_deriv_at_const _ _).congr_of_eventually_eq this.symm,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ },
  cases h₂.lt_or_lt with h₂ h₂,
  { have : 0 < sqrt (1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂]),
    simp only [← cos_arcsin h₁.le h₂.le, one_div] at this ⊢,
    exact ⟨sin_local_homeomorph.has_strict_deriv_at_symm ⟨h₁, h₂⟩ this.ne'
      (has_strict_deriv_at_sin _),
      sin_local_homeomorph.times_cont_diff_at_symm_deriv this.ne' ⟨h₁, h₂⟩
        (has_deriv_at_sin _) times_cont_diff_sin.times_cont_diff_at⟩ },
  { have : 1 - x ^ 2 < 0, by nlinarith [h₂],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, π / 2 := (lt_mem_nhds h₂).mono (λ y hy, arcsin_of_one_le hy.le),
    exact ⟨(has_strict_deriv_at_const _ _).congr_of_eventually_eq this.symm,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ }
end

lemma has_strict_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x :=
(deriv_arcsin_aux h₁ h₂).1

lemma has_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x :=
(has_strict_deriv_at_arcsin h₁ h₂).has_deriv_at

lemma times_cont_diff_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x :=
(deriv_arcsin_aux h₁ h₂).2.of_le le_top

lemma has_deriv_within_at_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Ici x) x :=
begin
  rcases em (x = 1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (π / 2)).congr _ _;
      simp [arcsin_of_one_le] { contextual := tt } },
  { exact (has_deriv_at_arcsin h h').has_deriv_within_at }
end

lemma has_deriv_within_at_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Iic x) x :=
begin
  rcases em (x = -1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (-(π / 2))).congr _ _;
      simp [arcsin_of_le_neg_one] { contextual := tt } },
  { exact (has_deriv_at_arcsin h' h).has_deriv_within_at }
end

lemma differentiable_within_at_arcsin_Ici {x : ℝ} :
  differentiable_within_at ℝ arcsin (Ici x) x ↔ x ≠ -1 :=
begin
  refine ⟨_, λ h, (has_deriv_within_at_arcsin_Ici h).differentiable_within_at⟩,
  rintro h rfl,
  have : sin ∘ arcsin =ᶠ[𝓝[Ici (-1:ℝ)] (-1)] id,
  { filter_upwards [Icc_mem_nhds_within_Ici ⟨le_rfl, neg_lt_self (@zero_lt_one ℝ _ _)⟩],
    exact λ x, sin_arcsin' },
  have := h.has_deriv_within_at.sin.congr_of_eventually_eq this.symm (by simp),
  simpa using (unique_diff_on_Ici _ _ left_mem_Ici).eq_deriv _ this (has_deriv_within_at_id _ _)
end

lemma differentiable_within_at_arcsin_Iic {x : ℝ} :
  differentiable_within_at ℝ arcsin (Iic x) x ↔ x ≠ 1 :=
begin
  refine ⟨λ h, _, λ h, (has_deriv_within_at_arcsin_Iic h).differentiable_within_at⟩,
  rw [← neg_neg x, ← image_neg_Ici] at h,
  have := (h.comp (-x) differentiable_within_at_id.neg (maps_to_image _ _)).neg,
  simpa [(∘), differentiable_within_at_arcsin_Ici] using this
end

lemma differentiable_at_arcsin {x : ℝ} :
  differentiable_at ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
⟨λ h, ⟨differentiable_within_at_arcsin_Ici.1 h.differentiable_within_at,
  differentiable_within_at_arcsin_Iic.1 h.differentiable_within_at⟩,
  λ h, (has_deriv_at_arcsin h.1 h.2).differentiable_at⟩

@[simp] lemma deriv_arcsin : deriv arcsin = λ x, 1 / sqrt (1 - x ^ 2) :=
begin
  funext x,
  by_cases h : x ≠ -1 ∧ x ≠ 1,
  { exact (has_deriv_at_arcsin h.1 h.2).deriv },
  { rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_arcsin.1 h)],
    simp only [not_and_distrib, ne.def, not_not] at h,
    rcases h with (rfl|rfl); simp }
end

lemma differentiable_on_arcsin : differentiable_on ℝ arcsin {-1, 1}ᶜ :=
λ x hx, (differentiable_at_arcsin.2
  ⟨λ h, hx (or.inl h), λ h, hx (or.inr h)⟩).differentiable_within_at

lemma times_cont_diff_on_arcsin {n : with_top ℕ} :
  times_cont_diff_on ℝ n arcsin {-1, 1}ᶜ :=
λ x hx, (times_cont_diff_at_arcsin (mt or.inl hx) (mt or.inr hx)).times_cont_diff_within_at

lemma times_cont_diff_at_arcsin_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
⟨λ h, or_iff_not_imp_left.2 $ λ hn, differentiable_at_arcsin.1 $ h.differentiable_at $
  with_top.one_le_iff_pos.2 (pos_iff_ne_zero.2 hn),
  λ h, h.elim (λ hn, hn.symm ▸ (times_cont_diff_zero.2 continuous_arcsin).times_cont_diff_at) $
    λ hx, times_cont_diff_at_arcsin hx.1 hx.2⟩

end arcsin

section arccos

lemma has_strict_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arccos (-(1 / sqrt (1 - x ^ 2))) x :=
(has_strict_deriv_at_arcsin h₁ h₂).const_sub (π / 2)

lemma has_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arccos (-(1 / sqrt (1 - x ^ 2))) x :=
(has_deriv_at_arcsin h₁ h₂).const_sub (π / 2)

lemma times_cont_diff_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x :=
times_cont_diff_at_const.sub (times_cont_diff_at_arcsin h₁ h₂)

lemma has_deriv_within_at_arccos_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Ici x) x :=
(has_deriv_within_at_arcsin_Ici h).const_sub _

lemma has_deriv_within_at_arccos_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Iic x) x :=
(has_deriv_within_at_arcsin_Iic h).const_sub _

lemma differentiable_within_at_arccos_Ici {x : ℝ} :
  differentiable_within_at ℝ arccos (Ici x) x ↔ x ≠ -1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Ici

lemma differentiable_within_at_arccos_Iic {x : ℝ} :
  differentiable_within_at ℝ arccos (Iic x) x ↔ x ≠ 1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Iic

lemma differentiable_at_arccos {x : ℝ} :
  differentiable_at ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
(differentiable_at_const_sub_iff _).trans differentiable_at_arcsin

@[simp] lemma deriv_arccos : deriv arccos = λ x, -(1 / sqrt (1 - x ^ 2)) :=
funext $ λ x, (deriv_const_sub _).trans $ by simp only [deriv_arcsin]

lemma differentiable_on_arccos : differentiable_on ℝ arccos {-1, 1}ᶜ :=
differentiable_on_arcsin.const_sub _

lemma times_cont_diff_on_arccos {n : with_top ℕ} :
  times_cont_diff_on ℝ n arccos {-1, 1}ᶜ :=
times_cont_diff_on_const.sub times_cont_diff_on_arcsin

lemma times_cont_diff_at_arccos_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
by refine iff.trans ⟨λ h, _, λ h, _⟩ times_cont_diff_at_arcsin_iff;
  simpa [arccos] using (@times_cont_diff_at_const _ _ _ _ _ _ _ _ _ _ (π / 2)).sub h

end arccos

end real
