/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.polynomial.big_operators
import data.nat.choose.cast
import data.nat.choose.vandermonde
import data.polynomial.derivative

/-!
# Hasse derivative of polynomials

The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It is a variant of the usual derivative, and satisfies `k! * (hasse_deriv k f) = derivative^[k] f`.
The main benefit is that is gives an atomic way of talking about expressions such as
`(derivative^[k] f).eval r / k!`, that occur in Taylor expansions, for example.

## Main declarations

In the following, we write `D k` for the `k`-th Hasse derivative `hasse_deriv k`.

* `polynomial.hasse_deriv`: the `k`-th Hasse derivative of a polynomial
* `polynomial.hasse_deriv_zero`: the `0`th Hasse derivative is the identity
* `polynomial.hasse_deriv_one`: the `1`st Hasse derivative is the usual derivative
* `polynomial.factorial_smul_hasse_deriv`: the identity `k! • (D k f) = derivative^[k] f`
* `polynomial.hasse_deriv_comp`: the identity `(D k).comp (D l) = (k+l).choose k • D (k+l)`
* `polynomial.hasse_deriv_mul`:
  the "Leibniz rule" `D k (f * g) = ∑ ij in antidiagonal k, D ij.1 f * D ij.2 g`

For the identity principle, see `polynomial.eq_zero_of_hasse_deriv_eq_zero`
in `data/polynomial/taylor.lean`.

## Reference

https://math.fontein.de/2009/08/12/the-hasse-derivative/

-/

noncomputable theory

namespace polynomial

open_locale nat big_operators polynomial
open function nat (hiding nsmul_eq_mul)

variables {R : Type*} [semiring R] (k : ℕ) (f : R[X])

/-- The `k`th Hasse derivative of a polynomial `∑ a_i X^i` is `∑ (i.choose k) a_i X^(i-k)`.
It satisfies `k! * (hasse_deriv k f) = derivative^[k] f`. -/
def hasse_deriv (k : ℕ) : R[X] →ₗ[R] R[X] :=
lsum (λ i, (monomial (i-k)) ∘ₗ distrib_mul_action.to_linear_map R R (i.choose k))

lemma hasse_deriv_apply :
  hasse_deriv k f = f.sum (λ i r, monomial (i - k) (↑(i.choose k) * r)) :=
by simpa only [← nsmul_eq_mul]

lemma hasse_deriv_coeff (n : ℕ) :
  (hasse_deriv k f).coeff n = (n + k).choose k * f.coeff (n + k) :=
begin
  rw [hasse_deriv_apply, coeff_sum, sum_def, finset.sum_eq_single (n + k), coeff_monomial],
  { simp only [if_true, add_tsub_cancel_right, eq_self_iff_true], },
  { intros i hi hink,
    rw [coeff_monomial],
    by_cases hik : i < k,
    { simp only [nat.choose_eq_zero_of_lt hik, if_t_t, nat.cast_zero, zero_mul], },
    { push_neg at hik, rw if_neg, contrapose! hink,
      exact (tsub_eq_iff_eq_add_of_le hik).mp hink, } },
  { intro h, simp only [not_mem_support_iff.mp h, monomial_zero_right, mul_zero, coeff_zero] }
end

lemma hasse_deriv_zero' : hasse_deriv 0 f = f :=
by simp only [hasse_deriv_apply, tsub_zero, nat.choose_zero_right,
  nat.cast_one, one_mul, sum_monomial_eq]

@[simp] lemma hasse_deriv_zero : @hasse_deriv R _ 0 = linear_map.id :=
linear_map.ext $ hasse_deriv_zero'

lemma hasse_deriv_eq_zero_of_lt_nat_degree (p : R[X]) (n : ℕ)
  (h : p.nat_degree < n) : hasse_deriv n p = 0 :=
begin
  rw [hasse_deriv_apply, sum_def],
  refine finset.sum_eq_zero (λ x hx, _),
  simp [nat.choose_eq_zero_of_lt ((le_nat_degree_of_mem_supp _ hx).trans_lt h)]
end

lemma hasse_deriv_one' : hasse_deriv 1 f = derivative f :=
by simp only [hasse_deriv_apply, derivative_apply, ← C_mul_X_pow_eq_monomial, nat.choose_one_right,
    (nat.cast_commute _ _).eq]

@[simp] lemma hasse_deriv_one : @hasse_deriv R _ 1 = derivative :=
linear_map.ext $ hasse_deriv_one'

@[simp] lemma hasse_deriv_monomial (n : ℕ) (r : R) :
  hasse_deriv k (monomial n r) = monomial (n - k) (↑(n.choose k) * r) :=
begin
  ext i,
  simp only [hasse_deriv_coeff, coeff_monomial],
  by_cases hnik : n = i + k,
  { rw [if_pos hnik, if_pos, ← hnik], apply tsub_eq_of_eq_add_rev, rwa add_comm },
  { rw [if_neg hnik, mul_zero],
    by_cases hkn : k ≤ n,
    { rw [← tsub_eq_iff_eq_add_of_le hkn] at hnik, rw [if_neg hnik] },
    { push_neg at hkn, rw [nat.choose_eq_zero_of_lt hkn, nat.cast_zero, zero_mul, if_t_t] } }
end

lemma hasse_deriv_C (r : R) (hk : 0 < k) : hasse_deriv k (C r) = 0 :=
by rw [← monomial_zero_left, hasse_deriv_monomial, nat.choose_eq_zero_of_lt hk,
    nat.cast_zero, zero_mul, monomial_zero_right]

lemma hasse_deriv_apply_one (hk : 0 < k) : hasse_deriv k (1 : R[X]) = 0 :=
by rw [← C_1, hasse_deriv_C k _ hk]

lemma hasse_deriv_X (hk : 1 < k) : hasse_deriv k (X : R[X]) = 0 :=
by rw [← monomial_one_one_eq_X, hasse_deriv_monomial, nat.choose_eq_zero_of_lt hk,
    nat.cast_zero, zero_mul, monomial_zero_right]

lemma factorial_smul_hasse_deriv :
  ⇑(k! • @hasse_deriv R _ k) = ((@derivative R _)^[k]) :=
begin
  induction k with k ih,
  { rw [hasse_deriv_zero, factorial_zero, iterate_zero, one_smul, linear_map.id_coe], },
  ext f n : 2,
  rw [iterate_succ_apply', ← ih],
  simp only [linear_map.smul_apply, coeff_smul, linear_map.map_smul_of_tower, coeff_derivative,
    hasse_deriv_coeff, ← @choose_symm_add _ k],
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ],
  rw ← (cast_commute (n+1) (f.coeff (n + k + 1))).eq,
  simp only [← mul_assoc], norm_cast, congr' 2,
  apply @cast_injective ℚ,
  have h1 : n + 1 ≤ n + k + 1 := succ_le_succ le_self_add,
  have h2 : k + 1 ≤ n + k + 1 := succ_le_succ le_add_self,
  have H : ∀ (n : ℕ), (n! : ℚ) ≠ 0, { exact_mod_cast factorial_ne_zero },
  -- why can't `field_simp` help me here?
  simp only [cast_mul, cast_choose ℚ, h1, h2, -one_div, -mul_eq_zero,
    succ_sub_succ_eq_sub, add_tsub_cancel_right, add_tsub_cancel_left] with field_simps,
  rw [eq_div_iff_mul_eq (mul_ne_zero (H _) (H _)), eq_comm, div_mul_eq_mul_div,
    eq_div_iff_mul_eq (mul_ne_zero (H _) (H _))],
  norm_cast,
  simp only [factorial_succ, succ_eq_add_one], ring,
end

lemma hasse_deriv_comp (k l : ℕ) :
  (@hasse_deriv R _ k).comp (hasse_deriv l) = (k+l).choose k • hasse_deriv (k+l) :=
begin
  ext i : 2,
  simp only [linear_map.smul_apply, comp_app, linear_map.coe_comp, smul_monomial,
    hasse_deriv_apply, mul_one, monomial_eq_zero_iff, sum_monomial_index, mul_zero,
    ← tsub_add_eq_tsub_tsub, add_comm l k],
  rw_mod_cast nsmul_eq_mul,
  congr' 2,
  by_cases hikl : i < k + l,
  { rw [choose_eq_zero_of_lt hikl, mul_zero],
    by_cases hil : i < l,
    { rw [choose_eq_zero_of_lt hil, mul_zero] },
    { push_neg at hil, rw [← tsub_lt_iff_right hil] at hikl,
      rw [choose_eq_zero_of_lt hikl , zero_mul], }, },
  push_neg at hikl, apply @cast_injective ℚ,
  have h1 : l ≤ i     := le_of_add_le_right hikl,
  have h2 : k ≤ i - l := le_tsub_of_add_le_right hikl,
  have h3 : k ≤ k + l := le_self_add,
  have H : ∀ (n : ℕ), (n! : ℚ) ≠ 0, { exact_mod_cast factorial_ne_zero },
  -- why can't `field_simp` help me here?
  simp only [cast_mul, cast_choose ℚ, h1, h2, h3, hikl, -one_div, -mul_eq_zero,
    succ_sub_succ_eq_sub, add_tsub_cancel_right, add_tsub_cancel_left] with field_simps,
  rw [eq_div_iff_mul_eq, eq_comm, div_mul_eq_mul_div, eq_div_iff_mul_eq, ← tsub_add_eq_tsub_tsub,
    add_comm l k],
  { ring, },
  all_goals { apply_rules [mul_ne_zero, H] }
end

lemma nat_degree_hasse_deriv_le (p : R[X]) (n : ℕ) :
  nat_degree (hasse_deriv n p) ≤ nat_degree p - n :=
begin
  classical,
  rw [hasse_deriv_apply, sum_def],
  refine (nat_degree_sum_le _ _).trans _,
  simp_rw [function.comp, nat_degree_monomial],
  rw [finset.fold_ite, finset.fold_const],
  { simp only [if_t_t, max_eq_right, zero_le', finset.fold_max_le, true_and, and_imp,
               tsub_le_iff_right, mem_support_iff, ne.def, finset.mem_filter],
    intros x hx hx',
    have hxp : x ≤ p.nat_degree := le_nat_degree_of_ne_zero hx,
    have hxn : n ≤ x,
    { contrapose! hx',
      simp [nat.choose_eq_zero_of_lt hx'] },
    rwa [tsub_add_cancel_of_le (hxn.trans hxp)] },
  { simp }
end

lemma nat_degree_hasse_deriv [no_zero_smul_divisors ℕ R] (p : R[X]) (n : ℕ) :
  nat_degree (hasse_deriv n p) = nat_degree p - n :=
begin
  cases lt_or_le p.nat_degree n with hn hn,
  { simpa [hasse_deriv_eq_zero_of_lt_nat_degree, hn] using (tsub_eq_zero_of_le hn.le).symm },
  { refine map_nat_degree_eq_sub _ _,
    { exact λ h, hasse_deriv_eq_zero_of_lt_nat_degree _ _ },
    { classical,
      simp only [ite_eq_right_iff, ne.def, nat_degree_monomial, hasse_deriv_monomial],
      intros k c c0 hh,
      -- this is where we use the `smul_eq_zero` from `no_zero_smul_divisors`
      rw [←nsmul_eq_mul, smul_eq_zero, nat.choose_eq_zero_iff] at hh,
      exact (tsub_eq_zero_of_le (or.resolve_right hh c0).le).symm } }
end

section
open add_monoid_hom finset.nat

lemma hasse_deriv_mul (f g : R[X]) :
  hasse_deriv k (f * g) = ∑ ij in antidiagonal k, hasse_deriv ij.1 f * hasse_deriv ij.2 g :=
begin
  let D := λ k, (@hasse_deriv R _ k).to_add_monoid_hom,
  let Φ := @add_monoid_hom.mul R[X] _,
  show (comp_hom (D k)).comp Φ f g =
    ∑ (ij : ℕ × ℕ) in antidiagonal k, ((comp_hom.comp ((comp_hom Φ) (D ij.1))).flip (D ij.2) f) g,
  simp only [← finset_sum_apply],
  congr' 2, clear f g,
  ext m r n s : 4,
  simp only [finset_sum_apply, coe_mul_left, coe_comp, flip_apply, comp_app,
    hasse_deriv_monomial, linear_map.to_add_monoid_hom_coe, comp_hom_apply_apply, coe_mul,
    monomial_mul_monomial],
  have aux : ∀ (x : ℕ × ℕ), x ∈ antidiagonal k →
    monomial (m - x.1 + (n - x.2)) (↑(m.choose x.1) * r * (↑(n.choose x.2) * s)) =
    monomial (m + n - k) (↑(m.choose x.1) * ↑(n.choose x.2) * (r * s)),
  { intros x hx, rw [finset.nat.mem_antidiagonal] at hx, subst hx,
    by_cases hm : m < x.1,
    { simp only [nat.choose_eq_zero_of_lt hm, nat.cast_zero, zero_mul, monomial_zero_right], },
    by_cases hn : n < x.2,
    { simp only [nat.choose_eq_zero_of_lt hn, nat.cast_zero,
        zero_mul, mul_zero, monomial_zero_right], },
    push_neg at hm hn,
    rw [tsub_add_eq_add_tsub hm, ← add_tsub_assoc_of_le hn, ← tsub_add_eq_tsub_tsub,
      add_comm x.2 x.1, mul_assoc, ← mul_assoc r, ← (nat.cast_commute _ r).eq, mul_assoc,
      mul_assoc], },
  conv_rhs { apply_congr, skip, rw aux _ H, },
  rw_mod_cast [← linear_map.map_sum, ← finset.sum_mul, ← nat.add_choose_eq],
end

end

end polynomial
