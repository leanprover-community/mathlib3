/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import algebra.order.absolute_value
import algebra.field_power
import ring_theory.int.basic
import tactic.basic
import tactic.ring_exp
import number_theory.divisors

/-!
# p-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in padic_norm.lean.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact p.prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

universe u

open nat

open_locale rat

open multiplicity

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `n = 0` or `p = 1`, then `padic_val_nat p q` defaults to `0`. -/
def padic_val_nat (p : ℕ) (n : ℕ) : ℕ :=
if h : p ≠ 1 ∧ 0 < n then (multiplicity p n).get (multiplicity.finite_nat_iff.2 h) else 0

namespace padic_val_nat

open multiplicity

variables {p : ℕ}

/-- `padic_val_nat p 0` is `0` for any `p`. -/
@[simp] protected lemma zero : padic_val_nat p 0 = 0 := by simp [padic_val_nat]

/-- `padic_val_nat p 1` is `0` for any `p`. -/
@[simp] protected lemma one : padic_val_nat p 1 = 0 := by { unfold padic_val_nat, split_ifs, simp }

/-- For `p ≠ 0`, `p ≠ 1`, `padic_val_rat p p` is `1`. -/
@[simp] lemma self (hp : 1 < p) : padic_val_nat p p = 1 :=
begin
  have neq_one : (¬ p = 1) ↔ true,
  { exact iff_of_true ((ne_of_lt hp).symm) trivial },
  have eq_zero_false : p = 0 ↔ false,
  { exact iff_false_intro ((ne_of_lt (trans zero_lt_one hp)).symm) },
  simp [padic_val_nat, neq_one, eq_zero_false]
end

lemma eq_zero_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : padic_val_nat p n = 0 :=
by { rw padic_val_nat, split_ifs; simp [multiplicity_eq_zero_of_not_dvd h] }

end padic_val_nat

/-- For `p ≠ 1`, the `p`-adic valuation of an integer `z ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `x = 0` or `p = 1`, then `padic_val_int p q` defaults to `0`. -/
def padic_val_int (p : ℕ) (z : ℤ) : ℕ := padic_val_nat p z.nat_abs

namespace padic_val_int

open multiplicity

variables {p : ℕ}

lemma of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) : padic_val_int p z =
  (multiplicity (p : ℤ) z).get (by {apply multiplicity.finite_int_iff.2, simp [hp, hz]}) :=
begin
  rw [padic_val_int, padic_val_nat, dif_pos (and.intro hp (int.nat_abs_pos_of_ne_zero hz))],
  simp only [multiplicity.int.nat_abs p z],
  refl
end

/-- `padic_val_int p 0` is `0` for any `p`. -/
@[simp] protected lemma zero : padic_val_int p 0 = 0 := by simp [padic_val_int]

/-- `padic_val_int p 1` is `0` for any `p`. -/
@[simp] protected lemma one : padic_val_int p 1 = 0 := by simp [padic_val_int]

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp] lemma of_nat {n : ℕ} : padic_val_int p n = padic_val_nat p n := by simp [padic_val_int]

/-- For `p ≠ 0`, `p ≠ 1`, `padic_val_int p p` is `1`. -/
lemma self (hp : 1 < p) : padic_val_int p p = 1 := by simp [padic_val_nat.self hp]

lemma eq_zero_of_not_dvd {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padic_val_int p z = 0 :=
begin
  rw [padic_val_int, padic_val_nat],
  split_ifs; simp [multiplicity.int.nat_abs, multiplicity_eq_zero_of_not_dvd h],
end

end padic_val_int

/-- `padic_val_rat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.denom`. If `q = 0` or `p = 1`, then `padic_val_rat p q` defaults to 0. -/
def padic_val_rat (p : ℕ) (q : ℚ) : ℤ := padic_val_int p q.num - padic_val_nat p q.denom

namespace padic_val_rat

open multiplicity

variables {p : ℕ}

/-- `padic_val_rat p q` is symmetric in `q`. -/
@[simp] protected lemma neg (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q :=
by simp [padic_val_rat, padic_val_int]

/-- `padic_val_rat p 0` is `0` for any `p`. -/
@[simp] protected lemma zero : padic_val_rat p 0 = 0 := by simp [padic_val_rat]

/-- `padic_val_rat p 1` is `0` for any `p`. -/
@[simp] protected lemma one : padic_val_rat p 1 = 0 := by simp [padic_val_rat]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic_value as a rational. -/
@[simp] lemma of_int {z : ℤ} : padic_val_rat p z = padic_val_int p z := by simp [padic_val_rat]

/-- The `p`-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`. -/
lemma of_int_multiplicity {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
  padic_val_rat p (z : ℚ) = (multiplicity (p : ℤ) z).get (finite_int_iff.2 ⟨hp, hz⟩) :=
by rw [of_int, padic_val_int.of_ne_one_ne_zero hp hz]

lemma multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) : padic_val_rat p q =
  (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp, rat.num_ne_zero_of_ne_zero hq⟩) -
  (multiplicity p q.denom).get (by { rw [← finite_iff_dom, finite_nat_iff], exact ⟨hp, q.pos⟩ }) :=
begin
  rw [padic_val_rat, padic_val_int.of_ne_one_ne_zero hp, padic_val_nat, dif_pos],
  { refl },
  { exact ⟨hp, q.pos⟩ },
  { exact rat.num_ne_zero_of_ne_zero hq }
end

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp] lemma of_nat {n : ℕ} : padic_val_rat p n = padic_val_nat p n := by simp [padic_val_rat]

/-- For `p ≠ 0`, `p ≠ 1`, `padic_val_rat p p` is `1`. -/
lemma self (hp : 1 < p) : padic_val_rat p p = 1 := by simp [hp]

end padic_val_rat

section padic_val_nat

variables {p : ℕ}

lemma zero_le_padic_val_rat_of_nat (n : ℕ) : 0 ≤ padic_val_rat p n := by simp

/-- `padic_val_rat` coincides with `padic_val_nat`. -/
@[norm_cast] lemma padic_val_rat_of_nat (n : ℕ) : (padic_val_nat p n : ℤ) = padic_val_rat p n :=
by simp

/-- A simplification of `padic_val_nat` when one input is prime, by analogy with
`padic_val_rat_def`. -/
lemma padic_val_nat_def [hp : fact p.prime] {n : ℕ} (hn : 0 < n) :
  padic_val_nat p n
    = (multiplicity p n).get (multiplicity.finite_nat_iff.2 ⟨nat.prime.ne_one hp.1, hn⟩) :=
begin
  simp [padic_val_nat],
  split_ifs,
  { refl },
  { exfalso,
    exact h ⟨hp.out.ne_one, hn⟩ }
end

lemma padic_val_nat_def' {n : ℕ} (hp : p ≠ 1) (hn : 0 < n) :
  ↑(padic_val_nat p n) = multiplicity p n :=
by simp [padic_val_nat, hp, hn]

@[simp] lemma padic_val_nat_self [fact p.prime] : padic_val_nat p p = 1 :=
by simp [padic_val_nat_def (fact.out p.prime).pos]

lemma one_le_padic_val_nat_of_dvd {n : ℕ} [hp : fact p.prime] (hn : 0 < n) (div : p ∣ n) :
  1 ≤ padic_val_nat p n :=
begin
  rw padic_val_nat_def hn,
  let one_le_mul : _ ≤ multiplicity p n :=
    multiplicity.le_multiplicity_of_pow_dvd (by { rw [pow_one], exact div }),
  simp only [nat.cast_one] at one_le_mul,
  rcases one_le_mul with ⟨_, q⟩,
  dsimp at q,
  solve_by_elim,
  exact hp
end

lemma dvd_iff_padic_val_nat_ne_zero {p n : ℕ} [fact p.prime] (hn0 : n ≠ 0) :
  (p ∣ n) ↔ padic_val_nat p n ≠ 0 :=
⟨λ h, one_le_iff_ne_zero.mp (one_le_padic_val_nat_of_dvd hn0.bot_lt h),
 λ h, not_not.1 (mt padic_val_nat.eq_zero_of_not_dvd h)⟩

end padic_val_nat

namespace padic_val_rat

open multiplicity

variables {p : ℕ} [hp : fact p.prime]

include hp

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
lemma finite_int_prime_iff {a : ℤ} : finite (p : ℤ) a ↔ a ≠ 0 :=
by simp [finite_int_iff, ne.symm (ne_of_lt hp.1.one_lt)]

/-- A rewrite lemma for `padic_val_rat p q` when `q` is expressed in terms of `rat.mk`. -/
protected lemma defn (p : ℕ) [hp : fact p.prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
  (qdf : q = n /. d) : padic_val_rat p q
    = (multiplicity (p : ℤ) n).get
      (finite_int_iff.2 ⟨ne.symm $ ne_of_lt hp.1.one_lt, λ hn, by simp * at *⟩)
    - (multiplicity (p : ℤ) d).get
      (finite_int_iff.2 ⟨ne.symm $ ne_of_lt hp.1.one_lt, λ hd, by simp * at *⟩) :=
have hd : d ≠ 0, from rat.mk_denom_ne_zero_of_ne_zero hqz qdf,
let ⟨c, hc1, hc2⟩ := rat.num_denom_mk hd qdf in
begin
  rw [padic_val_rat.multiplicity_sub_multiplicity];
  simp [hc1, hc2, multiplicity.mul' (nat.prime_iff_prime_int.1 hp.1),
    ne.symm (ne_of_lt hp.1.one_lt), hqz, pos_iff_ne_zero, int.coe_nat_multiplicity p q.denom]
end

/-- A rewrite lemma for `padic_val_rat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q * r) = padic_val_rat p q + padic_val_rat p r :=
have q * r = (q.num * r.num) /. (q.denom * r.denom), by rw_mod_cast rat.mul_num_denom,
have hq' : q.num /. q.denom ≠ 0, by rw rat.num_denom; exact hq,
have hr' : r.num /. r.denom ≠ 0, by rw rat.num_denom; exact hr,
have hp' : _root_.prime (p : ℤ), from nat.prime_iff_prime_int.1 hp.1,
begin
  rw [padic_val_rat.defn p (mul_ne_zero hq hr) this],
  conv_rhs { rw [← @rat.num_denom q, padic_val_rat.defn p hq', ← @rat.num_denom r,
    padic_val_rat.defn p hr'] },
  rw [multiplicity.mul' hp', multiplicity.mul' hp']; simp [add_comm, add_left_comm, sub_eq_add_neg]
end

/-- A rewrite lemma for `padic_val_rat p (q^k)` with condition `q ≠ 0`. -/
protected lemma pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
  padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
by induction k; simp [*, padic_val_rat.mul hq (pow_ne_zero _ hq), pow_succ, add_mul, add_comm]

/-- A rewrite lemma for `padic_val_rat p (q⁻¹)` with condition `q ≠ 0`. -/
protected lemma inv (q : ℚ) : padic_val_rat p q⁻¹ = -padic_val_rat p q :=
begin
  by_cases hq : q = 0,
  { simp [hq] },
  { rw [eq_neg_iff_add_eq_zero, ← padic_val_rat.mul (inv_ne_zero hq) hq, inv_mul_cancel hq,
      padic_val_rat.one],
    exact hp },
end

/-- A rewrite lemma for `padic_val_rat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected lemma div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r :=
begin
  rw [div_eq_mul_inv, padic_val_rat.mul hq (inv_ne_zero hr), padic_val_rat.inv r, sub_eq_add_neg],
  all_goals { exact hp }
end

/-- A condition for `padic_val_rat p (n₁ / d₁) ≤ padic_val_rat p (n₂ / d₂)`, in terms of
divisibility by `p^n`. -/
lemma padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ}
  (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
  padic_val_rat p (n₁ /. d₁) ≤ padic_val_rat p (n₂ /. d₂) ↔
  ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ :=
have hf1 : finite (p : ℤ) (n₁ * d₂),
  from finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂),
have hf2 : finite (p : ℤ) (n₂ * d₁),
  from finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁),
  by conv
  { to_lhs,
    rw [padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl,
      sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le],
    norm_cast,
    rw [← multiplicity.mul' (nat.prime_iff_prime_int.1 hp.1) hf1, add_comm,
      ← multiplicity.mul' (nat.prime_iff_prime_int.1 hp.1) hf2,
      part_enat.get_le_get, multiplicity_le_multiplicity_iff] }

/-- Sufficient conditions to show that the `p`-adic valuation of `q` is less than or equal to the
`p`-adic valuation of `q + r`. -/
theorem le_padic_val_rat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0)
  (h : padic_val_rat p q ≤ padic_val_rat p r) : padic_val_rat p q ≤ padic_val_rat p (q + r) :=
if hq : q = 0 then by simpa [hq] using h else
if hr : r = 0 then by simp [hr] else
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hq,
have hqd : (q.denom : ℤ) ≠ 0, by exact_mod_cast rat.denom_ne_zero _,
have hrn : r.num ≠ 0, from rat.num_ne_zero_of_ne_zero hr,
have hrd : (r.denom : ℤ) ≠ 0, by exact_mod_cast rat.denom_ne_zero _,
have hqreq : q + r = (q.num * r.denom + q.denom * r.num) /. (q.denom * r.denom),
  from rat.add_num_denom _ _,
have hqrd : q.num * r.denom + q.denom * r.num ≠ 0,
  from rat.mk_num_ne_zero_of_ne_zero hqr hqreq,
begin
  conv_lhs { rw ← @rat.num_denom q },
  rw [hqreq, padic_val_rat_le_padic_val_rat_iff hqn hqrd hqd (mul_ne_zero hqd hrd),
    ← multiplicity_le_multiplicity_iff, mul_left_comm,
    multiplicity.mul (nat.prime_iff_prime_int.1 hp.1), add_mul],
  rw [← @rat.num_denom q, ← @rat.num_denom r, padic_val_rat_le_padic_val_rat_iff hqn hrn hqd hrd,
    ← multiplicity_le_multiplicity_iff] at h,
  calc _ ≤ min (multiplicity (p : ℤ) (q.num * r.denom * q.denom))
    (multiplicity (p : ℤ) (q.denom * r.num * q.denom)) : (le_min
    (by rw [@multiplicity.mul _ _ _ _ (_ * _) _ (nat.prime_iff_prime_int.1 hp.1), add_comm])
    (by rw [mul_assoc, @multiplicity.mul _ _ _ _ (q.denom : ℤ)
        (_ * _) (nat.prime_iff_prime_int.1 hp.1)]; exact add_le_add_left h _))
    ... ≤ _ : min_le_multiplicity_add,
  all_goals { exact hp }
end

/-- The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`. -/
theorem min_le_padic_val_rat_add {q r : ℚ} (hqr : q + r ≠ 0) :
  min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) :=
(le_total (padic_val_rat p q) (padic_val_rat p r)).elim
  (λ h, by rw [min_eq_left h]; exact le_padic_val_rat_add_of_le hqr h)
  (λ h, by rw [min_eq_right h, add_comm]; exact le_padic_val_rat_add_of_le (by rwa add_comm) h)

open_locale big_operators

/-- A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic valuation
(if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padic_val_rat p (F i))
  (hn0 : ∑ i in finset.range n, F i ≠ 0) : 0 < padic_val_rat p (∑ i in finset.range n, F i) :=
begin
  induction n with d hd,
  { exact false.elim (hn0 rfl) },
  { rw finset.sum_range_succ at hn0 ⊢,
    by_cases h : ∑ (x : ℕ) in finset.range d, F x = 0,
    { rw [h, zero_add],
      exact hF d (lt_add_one _) },
    { refine lt_of_lt_of_le _ (min_le_padic_val_rat_add hn0),
      { refine lt_min (hd (λ i hi, _) h) (hF d (lt_add_one _)),
        exact hF _ (lt_trans hi (lt_add_one _)) } } }
end

end padic_val_rat

namespace padic_val_nat

variables {p a b : ℕ} [hp : fact p.prime]

include hp

/-- A rewrite lemma for `padic_val_nat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`. -/
protected lemma mul (ha : a ≠ 0) (hb : b ≠ 0) :
  padic_val_nat p (a * b) = padic_val_nat p a + padic_val_nat p b :=
begin
  apply int.coe_nat_inj,
  simp only [padic_val_rat_of_nat, nat.cast_mul],
  rw padic_val_rat.mul,
  norm_cast,
  exact cast_ne_zero.mpr ha,
  exact cast_ne_zero.mpr hb
end

protected lemma div_of_dvd (h : b ∣ a) :
  padic_val_nat p (a / b) = padic_val_nat p a - padic_val_nat p b :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp },
  obtain ⟨k, rfl⟩ := h,
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha,
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padic_val_nat.mul hk hb, nat.add_sub_cancel],
  exact hp
end

/-- Dividing out by a prime factor reduces the `padic_val_nat` by `1`. -/
protected lemma div (dvd : p ∣ b) : padic_val_nat p (b / p) = (padic_val_nat p b) - 1 :=
begin
  convert padic_val_nat.div_of_dvd dvd,
  rw padic_val_nat_self,
  exact hp
end

/-- A version of `padic_val_rat.pow` for `padic_val_nat`. -/
protected lemma pow (n : ℕ) (ha : a ≠ 0) :
  padic_val_nat p (a ^ n) = n * padic_val_nat p a :=
by simpa only [← @nat.cast_inj ℤ] with push_cast using padic_val_rat.pow (cast_ne_zero.mpr ha)

@[simp] protected lemma prime_pow (n : ℕ) : padic_val_nat p (p ^ n) = n :=
by rwa [padic_val_nat.pow _ (fact.out p.prime).ne_zero, padic_val_nat_self, mul_one]

protected lemma div_pow (dvd : p ^ a ∣ b) : padic_val_nat p (b / p ^ a) = (padic_val_nat p b) - a :=
begin
  convert padic_val_nat.div_of_dvd dvd,
  rw padic_val_nat.prime_pow,
  exact hp
end

end padic_val_nat

section padic_val_nat

variables {p : ℕ}

lemma dvd_of_one_le_padic_val_nat {n : ℕ} (hp : 1 ≤ padic_val_nat p n) : p ∣ n :=
begin
  by_contra h,
  rw padic_val_nat.eq_zero_of_not_dvd h at hp,
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)
end

lemma pow_padic_val_nat_dvd {n : ℕ} : p ^ padic_val_nat p n ∣ n :=
begin
  rcases n.eq_zero_or_pos with rfl | hn, { simp },
  rcases eq_or_ne p 1 with rfl | hp, { simp },
  rw [multiplicity.pow_dvd_iff_le_multiplicity, padic_val_nat_def']; assumption
end

lemma pow_succ_padic_val_nat_not_dvd {n : ℕ} [hp : fact p.prime] (hn : 0 < n) :
  ¬ p ^ (padic_val_nat p n + 1) ∣ n :=
begin
  rw multiplicity.pow_dvd_iff_le_multiplicity,
  rw padic_val_nat_def hn,
  { rw [nat.cast_add, part_enat.coe_get],
    simp only [nat.cast_one, not_le],
    exact part_enat.lt_add_one (ne_top_iff_finite.mpr
      (finite_nat_iff.mpr ⟨(fact.elim hp).ne_one, hn⟩)), },
  { apply_instance }
end

lemma padic_val_nat_dvd_iff (n : ℕ) [hp : fact p.prime] (a : ℕ) :
  p ^ n ∣ a ↔ a = 0 ∨ n ≤ padic_val_nat p a :=
begin
  split,
  { rw [pow_dvd_iff_le_multiplicity, padic_val_nat],
    split_ifs,
    { rw part_enat.coe_le_iff,
      exact λ hn, or.inr (hn _) },
    { simp only [true_and, not_lt, ne.def, not_false_iff, nat.le_zero_iff, hp.out.ne_one] at h,
      exact λ hn, or.inl h } },
  { rintro (rfl|h),
    { exact dvd_zero (p ^ n) },
    { exact dvd_trans (pow_dvd_pow p h) pow_padic_val_nat_dvd } }
end

lemma padic_val_nat_primes {q : ℕ} [hp : fact p.prime] [hq : fact q.prime] (neq : p ≠ q) :
  padic_val_nat p q = 0 :=
@padic_val_nat.eq_zero_of_not_dvd p q $
  (not_congr (iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp neq

protected lemma padic_val_nat.div' [hp : fact p.prime] :
  ∀ {m : ℕ} (cpm : coprime p m) {b : ℕ} (dvd : m ∣ b), padic_val_nat p (b / m) = padic_val_nat p b
| 0 := λ cpm b dvd, by { rw zero_dvd_iff at dvd, rw [dvd, nat.zero_div] }
| (n + 1) :=
  λ cpm b dvd,
  begin
    rcases dvd with ⟨c, rfl⟩,
    rw [mul_div_right c (nat.succ_pos _)],by_cases hc : c = 0,
    { rw [hc, mul_zero] },
    { rw padic_val_nat.mul,
      { suffices : ¬ p ∣ (n + 1),
        { rw [padic_val_nat.eq_zero_of_not_dvd this, zero_add] },
        contrapose! cpm,
        exact hp.1.dvd_iff_not_coprime.mp cpm },
      { exact nat.succ_ne_zero _ },
      { exact hc } }
  end

open_locale big_operators

lemma range_pow_padic_val_nat_subset_divisors {n : ℕ} (hn : n ≠ 0) :
  (finset.range (padic_val_nat p n + 1)).image (pow p) ⊆ n.divisors :=
begin
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw nat.mem_divisors,
  exact ⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩
end

lemma range_pow_padic_val_nat_subset_divisors' {n : ℕ} [hp : fact p.prime] :
  (finset.range (padic_val_nat p n)).image (λ t, p ^ (t + 1)) ⊆ n.divisors \ {1} :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw [finset.mem_sdiff, nat.mem_divisors],
  refine ⟨⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩, _⟩,
  rw [finset.mem_singleton],
  nth_rewrite 1 ← one_pow (k + 1),
  exact (nat.pow_lt_pow_of_lt_left hp.1.one_lt $ nat.succ_pos k).ne'
end

end padic_val_nat

section padic_val_int

variables {p : ℕ} [hp : fact p.prime]

include hp

lemma padic_val_int_dvd_iff (n : ℕ) (a : ℤ) : (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padic_val_int p a :=
by rw [padic_val_int, ← int.nat_abs_eq_zero, ← padic_val_nat_dvd_iff, ← int.coe_nat_dvd_left,
    int.coe_nat_pow]

lemma padic_val_int_dvd (a : ℤ) : (p : ℤ) ^ padic_val_int p a ∣ a :=
begin
  rw padic_val_int_dvd_iff,
  exact or.inr le_rfl
end

lemma padic_val_int_self : padic_val_int p p = 1 := padic_val_int.self hp.out.one_lt

lemma padic_val_int.mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  padic_val_int p (a * b) = padic_val_int p a + padic_val_int p b :=
begin
  simp_rw padic_val_int,
  rw [int.nat_abs_mul, padic_val_nat.mul];
  rwa int.nat_abs_ne_zero
end

lemma padic_val_int_mul_eq_succ (a : ℤ) (ha : a ≠ 0) :
  padic_val_int p (a * p) = (padic_val_int p a) + 1 :=
begin
  rw padic_val_int.mul ha (int.coe_nat_ne_zero.mpr hp.out.ne_zero),
  simp only [eq_self_iff_true, padic_val_int.of_nat, padic_val_nat_self],
  exact hp
end

end padic_val_int
