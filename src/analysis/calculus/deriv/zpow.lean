/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.inv

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, power
-/

universes u v w
open_locale classical topology big_operators filter
open filter asymptotics set

variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {E : Type v} [normed_add_comm_group E] [normed_space 𝕜 E]

variables {x : 𝕜}
variables {s : set 𝕜}
variables {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

lemma has_strict_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
  has_strict_deriv_at (λx, x^m) ((m : 𝕜) * x^(m-1)) x :=
begin
  have : ∀ m : ℤ, 0 < m → has_strict_deriv_at (λx, x^m) ((m:𝕜) * x^(m-1)) x,
  { assume m hm,
    lift m to ℕ using (le_of_lt hm),
    simp only [zpow_coe_nat, int.cast_coe_nat],
    convert has_strict_deriv_at_pow _ _ using 2,
    rw [← int.coe_nat_one, ← int.coe_nat_sub, zpow_coe_nat],
    norm_cast at hm,
    exact nat.succ_le_of_lt hm },
  rcases lt_trichotomy m 0 with hm|hm|hm,
  { have hx : x ≠ 0, from h.resolve_right hm.not_le,
    have := (has_strict_deriv_at_inv _).scomp _ (this (-m) (neg_pos.2 hm));
      [skip, exact zpow_ne_zero_of_ne_zero hx _],
    simp only [(∘), zpow_neg, one_div, inv_inv, smul_eq_mul] at this,
    convert this using 1,
    rw [sq, mul_inv, inv_inv, int.cast_neg, neg_mul, neg_mul_neg,
      ← zpow_add₀ hx, mul_assoc, ← zpow_add₀ hx], congr, abel },
  { simp only [hm, zpow_zero, int.cast_zero, zero_mul, has_strict_deriv_at_const] },
  { exact this m hm }
end

lemma has_deriv_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
  has_deriv_at (λx, x^m) ((m : 𝕜) * x^(m-1)) x :=
(has_strict_deriv_at_zpow m x h).has_deriv_at

theorem has_deriv_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) (s : set 𝕜) :
  has_deriv_within_at (λx, x^m) ((m : 𝕜) * x^(m-1)) s x :=
(has_deriv_at_zpow m x h).has_deriv_within_at

lemma differentiable_at_zpow : differentiable_at 𝕜 (λx, x^m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
⟨λ H, normed_field.continuous_at_zpow.1 H.continuous_at,
  λ H, (has_deriv_at_zpow m x H).differentiable_at⟩

lemma differentiable_within_at_zpow (m : ℤ) (x : 𝕜) (h : x ≠ 0 ∨ 0 ≤ m) :
  differentiable_within_at 𝕜 (λx, x^m) s x :=
(differentiable_at_zpow.mpr h).differentiable_within_at

lemma differentiable_on_zpow (m : ℤ) (s : set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
  differentiable_on 𝕜 (λx, x^m) s :=
λ x hxs, differentiable_within_at_zpow m x $ h.imp_left $ ne_of_mem_of_not_mem hxs

lemma deriv_zpow (m : ℤ) (x : 𝕜) : deriv (λ x, x ^ m) x = m * x ^ (m - 1) :=
begin
  by_cases H : x ≠ 0 ∨ 0 ≤ m,
  { exact (has_deriv_at_zpow m x H).deriv },
  { rw deriv_zero_of_not_differentiable_at (mt differentiable_at_zpow.1 H),
    push_neg at H, rcases H with ⟨rfl, hm⟩,
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, mul_zero] }
end

@[simp] lemma deriv_zpow' (m : ℤ) : deriv (λ x : 𝕜, x ^ m) = λ x, m * x ^ (m - 1) :=
funext $ deriv_zpow m

lemma deriv_within_zpow (hxs : unique_diff_within_at 𝕜 s x) (h : x ≠ 0 ∨ 0 ≤ m) :
  deriv_within (λx, x^m) s x = (m : 𝕜) * x^(m-1) :=
(has_deriv_within_at_zpow m x h s).deriv_within hxs

@[simp] lemma iter_deriv_zpow' (m : ℤ) (k : ℕ) :
  deriv^[k] (λ x : 𝕜, x ^ m) = λ x, (∏ i in finset.range k, (m - i)) * x ^ (m - k) :=
begin
  induction k with k ihk,
  { simp only [one_mul, int.coe_nat_zero, id, sub_zero, finset.prod_range_zero,
      function.iterate_zero] },
  { simp only [function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      finset.prod_range_succ, int.coe_nat_succ, ← sub_sub, int.cast_sub, int.cast_coe_nat,
      mul_assoc], }
end

lemma iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
  deriv^[k] (λ y, y ^ m) x = (∏ i in finset.range k, (m - i)) * x ^ (m - k) :=
congr_fun (iter_deriv_zpow' m k) x

lemma iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
  deriv^[k] (λx:𝕜, x^n) x = (∏ i in finset.range k, (n - i)) * x^(n-k) :=
begin
  simp only [← zpow_coe_nat, iter_deriv_zpow, int.cast_coe_nat],
  cases le_or_lt k n with hkn hnk,
  { rw int.coe_nat_sub hkn },
  { have : ∏ i in finset.range k, (n - i : 𝕜) = 0,
      from finset.prod_eq_zero (finset.mem_range.2 hnk) (sub_self _),
    simp only [this, zero_mul] }
end

@[simp] lemma iter_deriv_pow' (n k : ℕ) :
  deriv^[k] (λ x : 𝕜, x ^ n) = λ x, (∏ i in finset.range k, (n - i)) * x ^ (n - k) :=
funext $ λ x, iter_deriv_pow n x k

lemma iter_deriv_inv (k : ℕ) (x : 𝕜) :
  deriv^[k] has_inv.inv x = (∏ i in finset.range k, (-1 - i)) * x ^ (-1 - k : ℤ) :=
by simpa only [zpow_neg_one, int.cast_neg, int.cast_one] using iter_deriv_zpow (-1) x k

@[simp] lemma iter_deriv_inv' (k : ℕ) :
  deriv^[k] has_inv.inv = λ x : 𝕜, (∏ i in finset.range k, (-1 - i)) * x ^ (-1 - k : ℤ) :=
funext (iter_deriv_inv k)

variables {f : E → 𝕜} {t : set E} {a : E}

lemma differentiable_within_at.zpow (hf : differentiable_within_at 𝕜 f t a) (h : f a ≠ 0 ∨ 0 ≤ m) :
  differentiable_within_at 𝕜 (λ x, f x ^ m) t a :=
(differentiable_at_zpow.2 h).comp_differentiable_within_at a hf

lemma differentiable_at.zpow (hf : differentiable_at 𝕜 f a) (h : f a ≠ 0 ∨ 0 ≤ m) :
  differentiable_at 𝕜 (λ x, f x ^ m) a :=
(differentiable_at_zpow.2 h).comp a hf

lemma differentiable_on.zpow (hf : differentiable_on 𝕜 f t) (h : (∀ x ∈ t, f x ≠ 0) ∨ 0 ≤ m) :
  differentiable_on 𝕜 (λ x, f x ^ m) t :=
λ x hx, (hf x hx).zpow $ h.imp_left (λ h, h x hx)

lemma differentiable.zpow (hf : differentiable 𝕜 f) (h : (∀ x, f x ≠ 0) ∨ 0 ≤ m) :
  differentiable 𝕜 (λ x, f x ^ m) :=
λ x, (hf x).zpow $ h.imp_left (λ h, h x)

