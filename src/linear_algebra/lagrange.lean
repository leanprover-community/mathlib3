/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau.
-/

import data.polynomial algebra.big_operators

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s x` where `s : finset F` and `x : F`: the Lagrange basis polynomial
  that evaluates to `1` at `x` and `0` at other elements of `s`.
* `lagrange.interpolate s f` where `s : finset F` and `f : s → F`: the Lagrange interpolant
  that evaluates to `f x` at `x` for `x ∈ s`.

-/

noncomputable theory
open_locale classical

universe u

namespace lagrange

variables {F : Type u} [decidable_eq F] [field F] (s : finset F)

open polynomial

/-- Lagrange basis polynomials that evaluate to 1 at `x` and 0 at other elements of `s`. -/
def basis (x : F) : polynomial F :=
(s.erase x).prod $ λ y, C (x - y)⁻¹ * (X - C y)

@[simp] theorem basis_empty (x : F) : basis ∅ x = 1 :=
rfl

@[simp] theorem eval_basis_self (x : F) : (basis s x).eval x = 1 :=
begin
  rw [basis, ← (s.erase x).prod_hom (eval x), finset.prod_eq_one],
  intros y hy, simp_rw [eval_mul, eval_sub, eval_C, eval_X],
  exact inv_mul_cancel (sub_ne_zero_of_ne (finset.ne_of_mem_erase hy).symm)
end

@[simp] theorem eval_basis_ne (x y : F) (h1 : y ∈ s) (h2 : y ≠ x) : (basis s x).eval y = 0 :=
begin
  rw [basis, ← (s.erase x).prod_hom (eval y), finset.prod_eq_zero (finset.mem_erase.2 ⟨h2, h1⟩)],
  simp_rw [eval_mul, eval_sub, eval_C, eval_X, sub_self, mul_zero]
end

theorem eval_basis (x y : F) (h : y ∈ s) : (basis s x).eval y = if y = x then 1 else 0 :=
by { split_ifs with H, { subst H, apply eval_basis_self }, { exact eval_basis_ne s x y h H } }

@[simp] theorem nat_degree_basis (x : F) (hx : x ∈ s) : (basis s x).nat_degree = s.card - 1 :=
begin
  unfold basis, generalize hsx : s.erase x = sx,
  have : x ∉ sx := hsx ▸ finset.not_mem_erase x s,
  rw [← finset.insert_erase hx, hsx, finset.card_insert_of_not_mem this, nat.add_sub_cancel],
  clear hx hsx s, revert this, apply sx.induction_on,
  { intros hx, rw [finset.prod_empty, nat_degree_one], refl },
  { intros y s hys ih hx, rw [finset.mem_insert, not_or_distrib] at hx,
    have h1 : C (x - y)⁻¹ ≠ C 0 := λ h, hx.1 (eq_of_sub_eq_zero $ inv_eq_zero.1 $ C_inj.1 h),
    have h2 : X ^ 1 - C y ≠ 0 := by convert X_pow_sub_C_ne_zero zero_lt_one _,
    rw C_0 at h1, rw pow_one at h2,
    rw [finset.prod_insert hys, nat_degree_mul_eq (mul_ne_zero h1 h2), ih hx.2,
        finset.card_insert_of_not_mem hys, nat_degree_mul_eq h1 h2,
        nat_degree_C, zero_add, nat_degree, degree_X_sub_C, add_comm], refl,
    rw [ne, finset.prod_eq_zero_iff], rintro ⟨z, hzs, hz⟩,
    rw mul_eq_zero at hz, cases hz with hz hz,
    { rw [← C_0, C_inj, inv_eq_zero, sub_eq_zero] at hz, exact hx.2 (hz.symm ▸ hzs) },
    { rw ← pow_one (X : polynomial F) at hz, exact X_pow_sub_C_ne_zero zero_lt_one _ hz } }
end

variables (f : (↑s : set F) → F)

/-- Lagrange interpolation: given a finset `s` and a function `f : s → F`,
`interpolate s f` is the unique polynomial of degree `< s.card`
that takes value `f x` on all `x` in `s`. -/
def interpolate : polynomial F :=
s.attach.sum $ λ x, C (f x) * basis s x

@[simp] theorem interpolate_empty (f) : interpolate (∅ : finset F) f = 0 :=
rfl

@[simp] theorem eval_interpolate (x) (H : x ∈ s) : eval x (interpolate s f) = f ⟨x, H⟩ :=
begin
  rw [interpolate, ← finset.sum_hom _ (eval x), finset.sum_eq_single (⟨x, H⟩ : { x // x ∈ s })],
  { rw [eval_mul, eval_C, subtype.coe_mk, eval_basis_self, mul_one] },
  { rintros ⟨y, hy⟩ _ hyx, rw [eval_mul, subtype.coe_mk, eval_basis_ne s y x H, mul_zero],
    { rintros rfl, exact hyx rfl } },
  { intro h, exact absurd (finset.mem_attach _ _) h }
end

theorem degree_interpolate_lt : (interpolate s f).degree < s.card :=
if H : s = ∅ then by { subst H, rw [interpolate_empty, degree_zero], exact with_bot.bot_lt_coe _ }
else lt_of_le_of_lt (degree_sum_le _ _) $ (finset.sup_lt_iff $ with_bot.bot_lt_coe s.card).2 $ λ b _,
calc  (C (f b) * basis s b).degree
    ≤ (C (f b)).degree + (basis s b).degree : degree_mul_le _ _
... ≤ 0 + (basis s b).degree : add_le_add_right' degree_C_le
... = (basis s b).degree : zero_add _
... ≤ (basis s b).nat_degree : degree_le_nat_degree
... = (s.card - 1 : ℕ) : by { rw nat_degree_basis s b b.2 }
... < s.card : with_bot.coe_lt_coe.2 (nat.pred_lt $ mt finset.card_eq_zero.1 H)

end lagrange
