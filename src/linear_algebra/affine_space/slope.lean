/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import algebra.order.module
import linear_algebra.affine_space.affine_map
import tactic.field_simp

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/

open affine_map
variables {k E PE : Type*} [field k] [add_comm_group E] [module k E] [add_torsor E PE]

include E

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope (f : k → PE) (a b : k) : E := (b - a)⁻¹ • (f b -ᵥ f a)

lemma slope_fun_def (f : k → PE) : slope f = λ a b, (b - a)⁻¹ • (f b -ᵥ f a) := rfl

omit E

lemma slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
(div_eq_inv_mul _ _).symm

@[simp] lemma slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 :=
by rw [slope, sub_self, inv_zero, zero_smul]

include E

lemma slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) := rfl

@[simp] lemma sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a :=
begin
  rcases eq_or_ne a b with rfl | hne,
  { rw [sub_self, zero_smul, vsub_self] },
  { rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)] }
end

lemma sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b :=
by rw [sub_smul_slope, vsub_vadd]

@[simp] lemma slope_vadd_const (f : k → E) (c : PE) :
  slope (λ x, f x +ᵥ c) = slope f :=
begin
  ext a b,
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]
end

@[simp] lemma slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b):
  slope (λ x, (x - a) • f x) a b = f b :=
by simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

lemma eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0:E)) : f a = f b :=
by rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]

lemma affine_map.slope_comp {F PF : Type*} [add_comm_group F] [module k F] [add_torsor F PF]
  (f : PE →ᵃ[k] PF) (g : k → PE) (a b : k) :
  slope (f ∘ g) a b = f.linear (slope g a b) :=
by simp only [slope, (∘), f.linear.map_smul, f.linear_map_vsub]

lemma linear_map.slope_comp {F : Type*} [add_comm_group F] [module k F]
  (f : E →ₗ[k] F) (g : k → E) (a b : k) :
  slope (f ∘ g) a b = f (slope g a b) :=
f.to_affine_map.slope_comp g a b

lemma slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a :=
by rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `line_map_slope_slope_sub_div_sub`. -/
lemma sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
  ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c :=
begin
  by_cases hab : a = b,
  { subst hab,
    rw [sub_self, zero_div, zero_smul, zero_add],
    by_cases hac : a = c,
    { simp [hac] },
    { rw [div_self (sub_ne_zero.2 $ ne.symm hac), one_smul] } },
  by_cases hbc : b = c, { subst hbc, simp [sub_ne_zero.2 (ne.symm hab)] },
  rw [add_comm],
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul₀ (sub_ne_zero.2 $ ne.symm hab), smul_inv_smul₀ (sub_ne_zero.2 $ ne.symm hbc),
    vsub_add_vsub_cancel],
end

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`line_map` to express this property. -/
lemma line_map_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
  line_map (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c :=
by  field_simp [sub_ne_zero.2 h.symm, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
  line_map_apply_module]

/-- `slope f a b` is an affine combination of `slope f a (line_map a b r)` and
`slope f (line_map a b r) b`. We use `line_map` to express this property. -/
lemma line_map_slope_line_map_slope_line_map (f : k → PE) (a b r : k) :
  line_map (slope f (line_map a b r) b) (slope f a (line_map a b r)) r = slope f a b :=
begin
  obtain (rfl|hab) : a = b ∨ a ≠ b := classical.em _, { simp },
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b],
  convert line_map_slope_slope_sub_div_sub f b (line_map a b r) a hab.symm using 2,
  rw [line_map_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]
end
