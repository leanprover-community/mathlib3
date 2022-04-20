/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import analysis.complex.polynomial
import data.polynomial.mirror

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`. We also define `polynomial.norm2`, which is the sum of the squares of the
coefficients of a polynomial. It is also a coefficient of `p * p.mirror`.

## Main definitions

- `polynomial.mirror`
- `polynomial.norm2`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`
- `polynomial.norm2_eq_mul_reverse_coeff`: `norm2` is a coefficient of `p * p.mirror`

-/

namespace polynomial
open_locale polynomial

section

variables {R : Type*} [comm_ring R] [is_domain R] (p : R[X])

lemma mul_mirror_nat_degree : nat_degree (p * mirror p) = 2 * nat_degree p :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_degree_zero, mul_zero] },
  { rw [nat_degree_mul hp (mt p.mirror_eq_zero.mp hp), mirror_nat_degree, two_mul] },
end

lemma mul_mirror_nat_trailing_degree :
  nat_trailing_degree (p * mirror p) = 2 * nat_trailing_degree p :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero] },
  { rw [nat_trailing_degree_mul hp (mt p.mirror_eq_zero.mp hp),
        mirror_nat_trailing_degree, two_mul] },
end

/-- A unit trinomial is a trinomial whose three nonzero coeffients are units. -/
def is_unit_trinomial := ∃ {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : R}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w), p = C u * X ^ k + C v * X ^ m + C w * X ^ n

lemma unit_trinomial_nat_degree {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : R}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w) :
  nat_degree (C u * X ^ k + C v * X ^ m + C w * X ^ n) = n :=
begin
  refine le_antisymm (nat_degree_add_le_of_degree_le (nat_degree_add_le_of_degree_le _ _) _)
    (le_nat_degree_of_ne_zero _),
  { rw [nat_degree_C_mul_X_pow k u hu.ne_zero],
    exact (hkm.trans hmn).le },
  { rw [nat_degree_C_mul_X_pow m v hv.ne_zero],
    exact hmn.le },
  { rw [nat_degree_C_mul_X_pow n w hw.ne_zero] },
  { rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
        if_neg (hkm.trans hmn).ne', if_neg hmn.ne', if_pos rfl, zero_add, zero_add],
    exact hw.ne_zero },
end

lemma unit_trinomial_nat_trailing_degree {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : R}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w) :
  nat_trailing_degree (C u * X ^ k + C v * X ^ m + C w * X ^ n) = k :=
begin
  refine le_antisymm (nat_trailing_degree_le_of_ne_zero _) _,
  { rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow,
        if_pos rfl, if_neg hkm.ne, if_neg (hkm.trans hmn).ne, add_zero, add_zero],
    exact hu.ne_zero },
  { sorry },
end

lemma unit_trinomial_mirror {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : R}
  (hu : is_unit u) (hv : is_unit v) (hw : is_unit w) :
  mirror (C u * X ^ k + C v * X ^ m + C w * X ^ n) =
    C w * X ^ k + C v * X ^ (n - m + k) + C u * X ^ n :=
begin
  rw [mirror, unit_trinomial_nat_trailing_degree hkm hmn hu hv hw, reverse,
      unit_trinomial_nat_degree hkm hmn hu hv hw, reflect_add, reflect_add,
      reflect_C_mul_X_pow, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
      rev_at_le (hkm.trans hmn).le, rev_at_le hmn.le, rev_at_le le_rfl,
      add_mul, add_mul, mul_assoc, mul_assoc, mul_assoc, ←pow_add, ←pow_add, ←pow_add,
      nat.sub_add_cancel (hkm.trans hmn).le, nat.sub_self, zero_add,
      add_comm, add_assoc, add_right_inj, add_comm],
end

variables {p}

lemma is_unit_trinomial.not_is_unit (hp : is_unit_trinomial p) : ¬ is_unit p :=
begin
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩ := hp,
  exact λ h, ne_zero_of_lt hmn ((unit_trinomial_nat_degree hkm hmn hu hv hw).symm.trans
    (nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit h))),
end

end

variables {p : ℤ[X]}

lemma is_unit_trinomial_iff : is_unit_trinomial p ↔ coeff (p * mirror p)
  ((nat_trailing_degree (p * mirror p) + nat_degree (p * mirror p)) / 2) = 3 :=
begin
  rw [mul_mirror_nat_degree, mul_mirror_nat_trailing_degree, ←mul_add,
      nat.mul_div_right _ zero_lt_two],
  split,
  { rintros ⟨k, m, n, hkm, hmn, u, v, w, hu, hv, hw, rfl⟩,
    rw [unit_trinomial_nat_degree hkm hmn hu hv hw,
        unit_trinomial_nat_trailing_degree hkm hmn hu hv hw,
        unit_trinomial_mirror hkm hmn hu hv hw],
    simp_rw [mul_add, add_mul, coeff_add, mul_assoc, coeff_C_mul, mul_comm, ←mul_assoc, mul_comm,
      coeff_mul_C, ←pow_add, coeff_X_pow, add_left_inj, add_right_inj],
    rw [if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne'],
    sorry },
  { sorry },
end

lemma is_unit_trinomial.irreducible1 (hp : is_unit_trinomial p)
  (h : ∀ q : ℤ[X], q ∣ p → q ∣ mirror p → is_unit q) :
  irreducible p :=
begin
  refine irreducible_of_mirror hp.not_is_unit (λ q hq, _) h,
  -- this is a big result!
  sorry
end

lemma is_unit_trinomial.irreducible2 (hp : is_unit_trinomial p)
  (h : ∀ z : ℂ, ¬ (aeval z p = 0 ∧ aeval z (mirror p) = 0)) : irreducible p :=
begin
  refine hp.irreducible1 (λ q hq hq', _),
  suffices : ¬ (0 < q.nat_degree),
  { rw [not_lt, nat.le_zero_iff] at this,
    rw [eq_C_of_nat_degree_eq_zero this, is_unit_C, ←this],
    cases hq with h fgh,
    apply @is_unit_of_mul_is_unit_left _ _ q.leading_coeff h.leading_coeff,
    rw [←leading_coeff_mul, ←fgh],
    sorry },
  intro hq'',
  have inj : function.injective (algebra_map ℤ ℂ) := (algebra_map ℤ ℂ).injective_int,
  rw [nat_degree_pos_iff_degree_pos, ←degree_map_eq_of_injective inj] at hq'',
  cases complex.exists_root hq'' with z hz,
  apply h z,
  rw [is_root, eval_map, ←aeval_def] at hz,
  split,
  { cases hq with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  { cases hq' with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
end

lemma is_unit_trinomial.irreducible3 (hp : is_unit_trinomial p)
  (hp1 : ¬ X ∣ p) (hp2 : ¬ X ^ 2 + X + 1 ∣ p) (hp3 : ¬ X ^ 2 - X + 1 ∣ p) : irreducible p :=
begin
  refine hp.irreducible2 (λ z hz, _),
  sorry,
end

lemma selmer_irreducible {n : ℕ} (hn : 1 < n) : irreducible (X ^ n - X - 1 : ℤ[X]) :=
begin
  let p : ℤ[X] := X ^ n - X - 1,
  have hp : is_unit_trinomial p,
  { refine ⟨0, 1, n, zero_lt_one, hn, 1, -1, -1, is_unit_one, is_unit_one.neg, is_unit_one.neg, _⟩,
    rw [C_neg, neg_mul, neg_mul, C_1, one_mul, one_mul, one_mul, pow_zero, pow_one],
    sorry },
  refine hp.irreducible3 _ _ _,
end

end polynomial
