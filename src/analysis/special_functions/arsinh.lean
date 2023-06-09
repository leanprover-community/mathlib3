/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.basic

/-!
# Inverse of the sinh function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `real.arsinh`: The inverse function of `real.sinh`.

- `real.sinh_equiv`, `real.sinh_order_iso`, `real.sinh_homeomorph`: `real.sinh` as an `equiv`,
  `order_iso`, and `homeomorph`, respectively.

## Main Results

- `real.sinh_surjective`, `real.sinh_bijective`: `real.sinh` is surjective and bijective;

- `real.arsinh_injective`, `real.arsinh_surjective`, `real.arsinh_bijective`: `real.arsinh` is
  injective, surjective, and bijective;

- `real.continuous_arsinh`, `real.differentiable_arsinh`, `real.cont_diff_arsinh`: `real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `filter.tendsto.arsinh` and `cont_diff_at.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/
noncomputable theory

open function filter set
open_locale topology

namespace real

variables {x y : ℝ}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))`. -/
@[pp_nodot] def arsinh (x : ℝ) := log (x + sqrt (1 + x^2))

lemma exp_arsinh (x : ℝ) : exp (arsinh x) = x + sqrt (1 + x^2) :=
begin
  apply exp_log,
  rw [← neg_lt_iff_pos_add'],
  calc -x ≤ sqrt (x ^ 2) : le_sqrt_of_sq_le (neg_pow_bit0 _ _).le
  ... < sqrt (1 + x ^ 2) : sqrt_lt_sqrt (sq_nonneg _) (lt_one_add _)
end

@[simp] lemma arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

@[simp] lemma arsinh_neg (x : ℝ) : arsinh (-x) = -arsinh x :=
begin
  rw [← exp_eq_exp, exp_arsinh, exp_neg, exp_arsinh],
  apply eq_inv_of_mul_eq_one_left,
  rw [neg_sq, neg_add_eq_sub, add_comm x, mul_comm, ← sq_sub_sq, sq_sqrt, add_sub_cancel],
  exact add_nonneg zero_le_one (sq_nonneg _)
end

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp] lemma sinh_arsinh (x : ℝ) : sinh (arsinh x) = x :=
by { rw [sinh_eq, ← arsinh_neg, exp_arsinh, exp_arsinh, neg_sq], field_simp }

@[simp] lemma cosh_arsinh (x : ℝ) : cosh (arsinh x) = sqrt (1 + x^2) :=
by rw [← sqrt_sq (cosh_pos _).le, cosh_sq', sinh_arsinh]

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b`. -/
lemma sinh_surjective : surjective sinh := left_inverse.surjective sinh_arsinh

/-- `sinh` is bijective, both injective and surjective. -/
lemma sinh_bijective : bijective sinh := ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp] lemma arsinh_sinh (x : ℝ) : arsinh (sinh x) = x :=
right_inverse_of_injective_of_left_inverse sinh_injective sinh_arsinh x

/-- `real.sinh` as an `equiv`. -/
@[simps] def sinh_equiv : ℝ ≃ ℝ :=
{ to_fun := sinh,
  inv_fun := arsinh,
  left_inv := arsinh_sinh,
  right_inv := sinh_arsinh }

/-- `real.sinh` as an `order_iso`. -/
@[simps { fully_applied := ff }] def sinh_order_iso : ℝ ≃o ℝ :=
{ to_equiv := sinh_equiv,
  map_rel_iff' := @sinh_le_sinh }

/-- `real.sinh` as a `homeomorph`. -/
@[simps { fully_applied := ff }] def sinh_homeomorph : ℝ ≃ₜ ℝ := sinh_order_iso.to_homeomorph

lemma arsinh_bijective : bijective arsinh := sinh_equiv.symm.bijective
lemma arsinh_injective : injective arsinh := sinh_equiv.symm.injective
lemma arsinh_surjective : surjective arsinh := sinh_equiv.symm.surjective

lemma arsinh_strict_mono : strict_mono arsinh := sinh_order_iso.symm.strict_mono

@[simp] lemma arsinh_inj : arsinh x = arsinh y ↔ x = y := arsinh_injective.eq_iff
@[simp] lemma arsinh_le_arsinh : arsinh x ≤ arsinh y ↔ x ≤ y := sinh_order_iso.symm.le_iff_le
@[simp] lemma arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y := sinh_order_iso.symm.lt_iff_lt

@[simp] lemma arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
arsinh_injective.eq_iff' arsinh_zero

@[simp] lemma arsinh_nonneg_iff : 0 ≤ arsinh x ↔ 0 ≤ x :=
by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp] lemma arsinh_nonpos_iff : arsinh x ≤ 0 ↔ x ≤ 0 :=
by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp] lemma arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp] lemma arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

lemma has_strict_deriv_at_arsinh (x : ℝ) : has_strict_deriv_at arsinh (sqrt (1 + x ^ 2))⁻¹ x :=
begin
  convert sinh_homeomorph.to_local_homeomorph.has_strict_deriv_at_symm (mem_univ x)
    (cosh_pos _).ne' (has_strict_deriv_at_sinh _),
  exact (cosh_arsinh _).symm
end

lemma has_deriv_at_arsinh (x : ℝ) : has_deriv_at arsinh (sqrt (1 + x ^ 2))⁻¹ x :=
(has_strict_deriv_at_arsinh x).has_deriv_at

lemma differentiable_arsinh : differentiable ℝ arsinh :=
λ x, (has_deriv_at_arsinh x).differentiable_at

lemma cont_diff_arsinh {n : ℕ∞} : cont_diff ℝ n arsinh :=
sinh_homeomorph.cont_diff_symm_deriv (λ x, (cosh_pos x).ne') has_deriv_at_sinh cont_diff_sinh

@[continuity] lemma continuous_arsinh : continuous arsinh := sinh_homeomorph.symm.continuous

end real

open real

lemma filter.tendsto.arsinh {α : Type*} {l : filter α} {f : α → ℝ} {a : ℝ}
  (h : tendsto f l (𝓝 a)) : tendsto (λ x, arsinh (f x)) l (𝓝 (arsinh a)) :=
(continuous_arsinh.tendsto _).comp h

section continuous

variables {X : Type*} [topological_space X] {f : X → ℝ} {s : set X} {a : X}

lemma continuous_at.arsinh (h : continuous_at f a) : continuous_at (λ x, arsinh (f x)) a := h.arsinh

lemma continuous_within_at.arsinh (h : continuous_within_at f s a) :
  continuous_within_at (λ x, arsinh (f x)) s a :=
h.arsinh

lemma continuous_on.arsinh (h : continuous_on f s) : continuous_on (λ x, arsinh (f x)) s :=
λ x hx, (h x hx).arsinh

lemma continuous.arsinh (h : continuous f) : continuous (λ x, arsinh (f x)) :=
continuous_arsinh.comp h

end continuous

section fderiv

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {f : E → ℝ} {s : set E} {a : E}
  {f' : E →L[ℝ] ℝ} {n : ℕ∞}

lemma has_strict_fderiv_at.arsinh (hf : has_strict_fderiv_at f f' a) :
  has_strict_fderiv_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') a :=
(has_strict_deriv_at_arsinh _).comp_has_strict_fderiv_at a hf

lemma has_fderiv_at.arsinh (hf : has_fderiv_at f f' a) :
  has_fderiv_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') a :=
(has_deriv_at_arsinh _).comp_has_fderiv_at a hf

lemma has_fderiv_within_at.arsinh (hf : has_fderiv_within_at f f' s a) :
  has_fderiv_within_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') s a :=
(has_deriv_at_arsinh _).comp_has_fderiv_within_at a hf

lemma differentiable_at.arsinh (h : differentiable_at ℝ f a) :
  differentiable_at ℝ (λ x, arsinh (f x)) a :=
(differentiable_arsinh _).comp a h

lemma differentiable_within_at.arsinh (h : differentiable_within_at ℝ f s a) :
  differentiable_within_at ℝ (λ x, arsinh (f x)) s a :=
(differentiable_arsinh _).comp_differentiable_within_at a h

lemma differentiable_on.arsinh (h : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ x, arsinh (f x)) s :=
λ x hx, (h x hx).arsinh

lemma differentiable.arsinh (h : differentiable ℝ f) :
  differentiable ℝ (λ x, arsinh (f x)) :=
differentiable_arsinh.comp h

lemma cont_diff_at.arsinh (h : cont_diff_at ℝ n f a) :
  cont_diff_at ℝ n (λ x, arsinh (f x)) a :=
cont_diff_arsinh.cont_diff_at.comp a h

lemma cont_diff_within_at.arsinh (h : cont_diff_within_at ℝ n f s a) :
  cont_diff_within_at ℝ n (λ x, arsinh (f x)) s a :=
cont_diff_arsinh.cont_diff_at.comp_cont_diff_within_at a h

lemma cont_diff.arsinh (h : cont_diff ℝ n f) : cont_diff ℝ n (λ x, arsinh (f x)) :=
cont_diff_arsinh.comp h

lemma cont_diff_on.arsinh (h : cont_diff_on ℝ n f s) : cont_diff_on ℝ n (λ x, arsinh (f x)) s :=
λ x hx, (h x hx).arsinh

end fderiv

section deriv

variables {f : ℝ → ℝ} {s : set ℝ} {a f' : ℝ}

lemma has_strict_deriv_at.arsinh (hf : has_strict_deriv_at f f' a) :
  has_strict_deriv_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') a :=
(has_strict_deriv_at_arsinh _).comp a hf

lemma has_deriv_at.arsinh (hf : has_deriv_at f f' a) :
  has_deriv_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') a :=
(has_deriv_at_arsinh _).comp a hf

lemma has_deriv_within_at.arsinh (hf : has_deriv_within_at f f' s a) :
  has_deriv_within_at (λ x, arsinh (f x)) ((sqrt (1 + (f a) ^ 2))⁻¹ • f') s a :=
(has_deriv_at_arsinh _).comp_has_deriv_within_at a hf

end deriv
