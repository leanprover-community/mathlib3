/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import algebra.quadratic_discriminant
import analysis.complex.polynomial
import field_theory.is_alg_closed.basic
import analysis.special_functions.trigonometric.basic
import analysis.convex.specific_functions

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`analysis.special_functions.trigonometric.basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/

noncomputable theory

namespace complex

open set filter
open_locale real

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
begin
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1,
  { rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero', zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub],
    field_simp only, congr' 3, ring },
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_exists_int, mul_right_comm],
  refine exists_congr (λ x, _),
  refine (iff_of_eq $ congr_arg _ _).trans (mul_right_inj' $ mul_ne_zero two_ne_zero' I_ne_zero),
  ring,
end

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
by rw [← not_exists, not_iff_not, cos_eq_zero_iff]

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k * π :=
begin
  rw [← complex.cos_sub_pi_div_two, cos_eq_zero_iff],
  split,
  { rintros ⟨k, hk⟩,
    use k + 1,
    field_simp [eq_add_of_sub_eq hk],
    ring },
  { rintros ⟨k, rfl⟩,
    use k - 1,
    field_simp,
    ring }
end

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π :=
by rw [← not_exists, not_iff_not, sin_eq_zero_iff]


lemma tan_eq_zero_iff {θ : ℂ} : tan θ = 0 ↔ ∃ k : ℤ, θ = k * π / 2 :=
begin
  have h := (sin_two_mul θ).symm,
  rw mul_assoc at h,
  rw [tan, div_eq_zero_iff, ← mul_eq_zero, ← zero_mul ((1/2):ℂ), mul_one_div,
      cancel_factors.cancel_factors_eq_div h two_ne_zero', mul_comm],
  simpa only [zero_div, zero_mul, ne.def, not_false_iff] with field_simps using sin_eq_zero_iff,
end

lemma tan_ne_zero_iff {θ : ℂ} : tan θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π / 2 :=
by rw [← not_exists, not_iff_not, tan_eq_zero_iff]

lemma tan_int_mul_pi_div_two (n : ℤ) : tan (n * π/2) = 0 :=
tan_eq_zero_iff.mpr (by use n)

lemma cos_eq_cos_iff {x y : ℂ} :
  cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
calc cos x = cos y ↔ cos x - cos y = 0 : sub_eq_zero.symm
... ↔ -2 * sin((x + y)/2) * sin((x - y)/2) = 0 : by rw cos_sub_cos
... ↔ sin((x + y)/2) = 0 ∨ sin((x - y)/2) = 0 : by simp [(by norm_num : (2:ℂ) ≠ 0)]
... ↔ sin((x - y)/2) = 0 ∨ sin((x + y)/2) = 0 : or.comm
... ↔ (∃ k : ℤ, y = 2 * k * π + x) ∨ (∃ k :ℤ, y = 2 * k * π - x) :
begin
  apply or_congr;
    field_simp [sin_eq_zero_iff, (by norm_num : -(2:ℂ) ≠ 0), eq_sub_iff_add_eq',
      sub_eq_iff_eq_add, mul_comm (2:ℂ), mul_right_comm _ (2:ℂ)],
  split; { rintros ⟨k, rfl⟩, use -k, simp, },
end
... ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x : exists_or_distrib.symm

lemma sin_eq_sin_iff {x y : ℂ} :
  sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
begin
  simp only [← complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add],
  refine exists_congr (λ k, or_congr _ _); refine eq.congr rfl _; field_simp; ring
end

lemma tan_add {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
begin
  rcases h with ⟨h1, h2⟩ | ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩,
  { rw [tan, sin_add, cos_add,
        ← div_div_div_cancel_right (sin x * cos y + cos x * sin y)
            (mul_ne_zero (cos_ne_zero_iff.mpr h1) (cos_ne_zero_iff.mpr h2)),
        add_div, sub_div],
    simp only [←div_mul_div_comm, ←tan, mul_one, one_mul,
              div_self (cos_ne_zero_iff.mpr h1), div_self (cos_ne_zero_iff.mpr h2)] },
  { obtain ⟨t, hx, hy, hxy⟩ := ⟨tan_int_mul_pi_div_two, t (2*k+1), t (2*l+1), t (2*k+1+(2*l+1))⟩,
    simp only [int.cast_add, int.cast_bit0, int.cast_mul, int.cast_one, hx, hy] at hx hy hxy,
    rw [hx, hy, add_zero, zero_div,
        mul_div_assoc, mul_div_assoc, ← add_mul (2*(k:ℂ)+1) (2*l+1) (π/2), ← mul_div_assoc, hxy] },
end

lemma tan_add' {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2)) :
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
tan_add (or.inl h)

lemma tan_two_mul {z : ℂ} : tan (2 * z) = 2 * tan z / (1 - tan z ^ 2) :=
begin
  by_cases h : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2,
  { rw [two_mul, two_mul, sq, tan_add (or.inl ⟨h, h⟩)] },
  { rw not_forall_not at h,
    rw [two_mul, two_mul, sq, tan_add (or.inr ⟨h, h⟩)] },
end

lemma tan_add_mul_I {x y : ℂ}
  (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y * I ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y * I = (2 * l + 1) * π / 2)) :
  tan (x + y*I) = (tan x + tanh y * I) / (1 - tan x * tanh y * I) :=
by rw [tan_add h, tan_mul_I, mul_assoc]

lemma tan_eq {z : ℂ}
  (h : ((∀ k : ℤ, (z.re:ℂ) ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, (z.im:ℂ) * I ≠ (2 * l + 1) * π / 2)
     ∨ ((∃ k : ℤ, (z.re:ℂ) = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, (z.im:ℂ) * I = (2 * l + 1) * π / 2)) :
  tan z = (tan z.re + tanh z.im * I) / (1 - tan z.re * tanh z.im * I) :=
by convert tan_add_mul_I h; exact (re_add_im z).symm

open_locale topological_space

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
continuous_on_sin.div continuous_on_cos $ λ x, id

@[continuity]
lemma continuous_tan : continuous (λ x : {x | cos x ≠ 0}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

lemma cos_eq_iff_quadratic {z w : ℂ} :
  cos z = w ↔ (exp (z * I)) ^ 2 - 2 * w * exp (z * I) + 1 = 0 :=
begin
  rw ← sub_eq_zero,
  field_simp [cos, exp_neg, exp_ne_zero],
  refine eq.congr _ rfl,
  ring
end

lemma cos_surjective : function.surjective cos :=
begin
  intro x,
  obtain ⟨w, w₀, hw⟩ : ∃ w ≠ 0, 1 * w * w + (-2 * x) * w + 1 = 0,
  { rcases exists_quadratic_eq_zero (@one_ne_zero ℂ _ _) (is_alg_closed.exists_eq_mul_self _)
      with ⟨w, hw⟩,
    refine ⟨w, _, hw⟩,
    rintro rfl,
    simpa only [zero_add, one_ne_zero, mul_zero] using hw },
  refine ⟨log w / I, cos_eq_iff_quadratic.2 _⟩,
  rw [div_mul_cancel _ I_ne_zero, exp_log w₀],
  convert hw,
  ring
end

@[simp] lemma range_cos : range cos = set.univ :=
cos_surjective.range_eq

lemma sin_surjective : function.surjective sin :=
begin
  intro x,
  rcases cos_surjective x with ⟨z, rfl⟩,
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩
end

@[simp] lemma range_sin : range sin = set.univ :=
sin_surjective.range_eq

end complex

namespace real

open_locale real

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
by exact_mod_cast @complex.cos_eq_zero_iff θ

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
by rw [← not_exists, not_iff_not, cos_eq_zero_iff]

lemma cos_eq_cos_iff {x y : ℝ} :
  cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
by exact_mod_cast @complex.cos_eq_cos_iff x y

lemma sin_eq_sin_iff {x y : ℝ} :
  sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
by exact_mod_cast @complex.sin_eq_sin_iff x y

lemma lt_sin_mul {x : ℝ} (hx : 0 < x) (hx' : x < 1) : x < sin ((π / 2) * x) :=
by simpa [mul_comm x] using strict_concave_on_sin_Icc.2 ⟨le_rfl, pi_pos.le⟩
  ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ pi_div_two_pos.ne (sub_pos.2 hx') hx

lemma le_sin_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : x ≤ sin ((π / 2) * x) :=
by simpa [mul_comm x] using strict_concave_on_sin_Icc.concave_on.2 ⟨le_rfl, pi_pos.le⟩
  ⟨pi_div_two_pos.le, half_le_self pi_pos.le⟩ (sub_nonneg.2 hx') hx

lemma mul_lt_sin {x : ℝ} (hx : 0 < x) (hx' : x < π / 2) : (2 / π) * x < sin x :=
begin
  rw [←inv_div],
  simpa [-inv_div, pi_div_two_pos.ne'] using @lt_sin_mul ((π / 2)⁻¹ * x) _ _,
  { exact mul_pos (inv_pos.2 pi_div_two_pos) hx },
  { rwa [←div_eq_inv_mul, div_lt_one pi_div_two_pos] },
end

/-- In the range `[0, π / 2]`, we have a linear lower bound on `sin`. This inequality forms one half
of Jordan's inequality, the other half is `real.sin_lt` -/
lemma mul_le_sin {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ π / 2) : (2 / π) * x ≤ sin x :=
begin
  rw [←inv_div],
  simpa [-inv_div, pi_div_two_pos.ne'] using @le_sin_mul ((π / 2)⁻¹ * x) _ _,
  { exact mul_nonneg (inv_nonneg.2 pi_div_two_pos.le) hx },
  { rwa [←div_eq_inv_mul, div_le_one pi_div_two_pos] },
end

end real
