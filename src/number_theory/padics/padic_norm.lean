/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import number_theory.padics.padic_val

/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

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

/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ -padic_val_rat p q`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padic_norm (p : ℕ) (q : ℚ) : ℚ := if q = 0 then 0 else (p : ℚ) ^ -padic_val_rat p q

namespace padic_norm

open padic_val_rat
variables {p : ℕ}

/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp] protected lemma eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
  padic_norm p q = p ^ -padic_val_rat p q :=
by simp [hq, padic_norm]

/-- The `p`-adic norm is nonnegative. -/
protected lemma nonneg (q : ℚ) : 0 ≤ padic_norm p q :=
if hq : q = 0 then by simp [hq, padic_norm]
else
  begin
    unfold padic_norm; split_ifs,
    apply zpow_nonneg,
    exact_mod_cast nat.zero_le _
  end

/-- The `p`-adic norm of `0` is `0`. -/
@[simp] protected lemma zero : padic_norm p 0 = 0 := by simp [padic_norm]

/-- The `p`-adic norm of `1` is `1`. -/
@[simp] protected lemma one : padic_norm p 1 = 1 := by simp [padic_norm]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padic_norm.padic_norm_p_of_prime` for a version assuming `p` is prime. -/
lemma padic_norm_p (hp : 1 < p) : padic_norm p p = p⁻¹ :=
by simp [padic_norm, (pos_of_gt hp).ne', padic_val_nat.self hp]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padic_norm.padic_norm_p` for a version assuming `1 < p`. -/
@[simp] lemma padic_norm_p_of_prime [fact p.prime] : padic_norm p p = p⁻¹ :=
padic_norm_p $ nat.prime.one_lt (fact.out _)

/-- The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
lemma padic_norm_of_prime_of_ne {q : ℕ} [p_prime : fact p.prime] [q_prime : fact q.prime]
  (neq : p ≠ q) : padic_norm p q = 1 :=
begin
  have p : padic_val_rat p q = 0,
  { exact_mod_cast @padic_val_nat_primes p q p_prime q_prime neq },
  simp [padic_norm, p, q_prime.1.1, q_prime.1.ne_zero],
end

/-- The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padic_norm.padic_norm_p_lt_one_of_prime` for a version assuming `p` is prime. -/
lemma padic_norm_p_lt_one (hp : 1 < p) : padic_norm p p < 1 :=
begin
  rw [padic_norm_p hp, inv_lt_one_iff],
  exact_mod_cast (or.inr hp)
end

/-- The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padic_norm.padic_norm_p_lt_one` for a version assuming `1 < p`. -/
lemma padic_norm_p_lt_one_of_prime [fact p.prime] : padic_norm p p < 1 :=
padic_norm_p_lt_one $ nat.prime.one_lt (fact.out _)

/-- `padic_norm p q` takes discrete values `p ^ -z` for `z : ℤ`. -/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padic_norm p q = p ^ -z :=
⟨ (padic_val_rat p q), by simp [padic_norm, hq] ⟩

/-- `padic_norm p` is symmetric. -/
@[simp] protected lemma neg (q : ℚ) : padic_norm p (-q) = padic_norm p q :=
if hq : q = 0 then by simp [hq]
else by simp [padic_norm, hq]

variable [hp : fact p.prime]
include hp

/-- If `q ≠ 0`, then `padic_norm p q ≠ 0`. -/
protected lemma nonzero {q : ℚ} (hq : q ≠ 0) : padic_norm p q ≠ 0 :=
begin
  rw padic_norm.eq_zpow_of_nonzero hq,
  apply zpow_ne_zero_of_ne_zero,
  exact_mod_cast ne_of_gt hp.1.pos
end

/-- If the `p`-adic norm of `q` is 0, then `q` is `0`. -/
lemma zero_of_padic_norm_eq_zero {q : ℚ} (h : padic_norm p q = 0) : q = 0 :=
begin
  apply by_contradiction, intro hq,
  unfold padic_norm at h, rw if_neg hq at h,
  apply absurd h,
  apply zpow_ne_zero_of_ne_zero,
  exact_mod_cast hp.1.ne_zero
end

/-- The `p`-adic norm is multiplicative. -/
@[simp] protected theorem mul (q r : ℚ) : padic_norm p (q * r) = padic_norm p q * padic_norm p r :=
if hq : q = 0 then
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else
  have q * r ≠ 0, from mul_ne_zero hq hr,
  have (p : ℚ) ≠ 0, by simp [hp.1.ne_zero],
  by simp [padic_norm, *, padic_val_rat.mul, zpow_add₀ this, mul_comm]

/-- The `p`-adic norm respects division. -/
@[simp] protected theorem div (q r : ℚ) : padic_norm p (q / r) = padic_norm p q / padic_norm p r :=
if hr : r = 0 then by simp [hr] else
eq_div_of_mul_eq (padic_norm.nonzero hr) (by rw [←padic_norm.mul, div_mul_cancel _ hr])

/-- The `p`-adic norm of an integer is at most `1`. -/
protected theorem of_int (z : ℤ) : padic_norm p z ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one] else
begin
  unfold padic_norm,
  rw [if_neg _],
  { refine zpow_le_one_of_nonpos _ _,
    { exact_mod_cast le_of_lt hp.1.one_lt },
    { rw [padic_val_rat.of_int, neg_nonpos],
      norm_cast, simp }},
  exact_mod_cast hz,
end

private lemma nonarchimedean_aux {q r : ℚ} (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
have hnqp : padic_norm p q ≥ 0, from padic_norm.nonneg _,
have hnrp : padic_norm p r ≥ 0, from padic_norm.nonneg _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp, le_max_right]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp, le_max_left]
else if hqr : q + r = 0 then
  le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
else
  begin
    unfold padic_norm, split_ifs,
    apply le_max_iff.2,
    left,
    apply zpow_le_of_le,
    { exact_mod_cast le_of_lt hp.1.one_lt },
    { apply neg_le_neg,
      have : padic_val_rat p q =
              min (padic_val_rat p q) (padic_val_rat p r),
        from (min_eq_left h).symm,
      rw this,
      apply min_le_padic_val_rat_add; assumption }
  end

/-- The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p`
and the norm of `q`. -/
protected theorem nonarchimedean {q r : ℚ} :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
begin
  wlog hle : (padic_val_rat p q) ≤ (padic_val_rat p r) generalizing q r,
  { rw [add_comm, max_comm], exact this (le_of_not_le hle) },
  exact nonarchimedean_aux hle
end

/-- The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of
`p` plus the norm of `q`. -/
theorem triangle_ineq (q r : ℚ) : padic_norm p (q + r) ≤ padic_norm p q + padic_norm p r :=
calc padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) : padic_norm.nonarchimedean
                       ... ≤ padic_norm p q + padic_norm p r :
                         max_le_add_of_nonneg (padic_norm.nonneg _) (padic_norm.nonneg _)

/-- The `p`-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the `p`-adic norm. -/
protected theorem sub {q r : ℚ} : padic_norm p (q - r) ≤ max (padic_norm p q) (padic_norm p r) :=
by rw [sub_eq_add_neg, ←padic_norm.neg r]; apply padic_norm.nonarchimedean

/-- If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max
of the norms of `q` and `r`. -/
lemma add_eq_max_of_ne {q r : ℚ} (hne : padic_norm p q ≠ padic_norm p r) :
  padic_norm p (q + r) = max (padic_norm p q) (padic_norm p r) :=
begin
  wlog hlt : (padic_norm p r) < (padic_norm p q),
  { rw [add_comm, max_comm], exact this hne.symm (hne.lt_or_lt.resolve_right hlt) },
  have : padic_norm p q ≤ max (padic_norm p (q + r)) (padic_norm p r), from calc
   padic_norm p q = padic_norm p (q + r - r) : by congr; ring
               ... ≤ max (padic_norm p (q + r)) (padic_norm p (-r)) : padic_norm.nonarchimedean
               ... = max (padic_norm p (q + r)) (padic_norm p r) : by simp,
  have hnge : padic_norm p r ≤ padic_norm p (q + r),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : padic_norm p q ≤ padic_norm p (q + r), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
  { apply padic_norm.nonarchimedean },
  { rwa max_eq_left_of_lt hlt }
end

/-- The `p`-adic norm is an absolute value: positive-definite and multiplicative, satisfying the
triangle inequality. -/
instance : is_absolute_value (padic_norm p) :=
{ abv_nonneg := padic_norm.nonneg,
  abv_eq_zero := λ _, ⟨zero_of_padic_norm_eq_zero, λ hx, by simpa only [hx]⟩,
  abv_add := padic_norm.triangle_ineq,
  abv_mul := padic_norm.mul }

lemma dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padic_norm p z ≤ p ^ (-n : ℤ) :=
begin
  unfold padic_norm, split_ifs with hz,
  { norm_cast at hz,
    have : 0 ≤ (p ^ n : ℚ), {apply pow_nonneg, exact_mod_cast le_of_lt hp.1.pos },
    simp [hz, this] },
  { rw [zpow_le_iff_le, neg_le_neg_iff, padic_val_rat.of_int,
      padic_val_int.of_ne_one_ne_zero hp.1.ne_one _],
    { norm_cast,
      rw [← part_enat.coe_le_coe, part_enat.coe_get, ← multiplicity.pow_dvd_iff_le_multiplicity],
      simp },
    { exact_mod_cast hz },
    { exact_mod_cast hp.1.one_lt } }
end

/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
lemma int_eq_one_iff (m : ℤ) : padic_norm p m = 1 ↔ ¬ (p : ℤ) ∣ m :=
begin
  nth_rewrite 1 ← pow_one p,
  simp only [dvd_iff_norm_le, int.cast_coe_nat, nat.cast_one, zpow_neg, zpow_one, not_le],
  split,
  { intro h,
    rw [h, inv_lt_one_iff_of_pos];
    norm_cast,
    { exact nat.prime.one_lt (fact.out _), },
    { exact nat.prime.pos (fact.out _), }, },
  { simp only [padic_norm],
    split_ifs,
    { rw [inv_lt_zero, ← nat.cast_zero, nat.cast_lt],
      intro h, exact (nat.not_lt_zero p h).elim, },
    { have : 1 < (p : ℚ) := by norm_cast; exact (nat.prime.one_lt (fact.out _ : nat.prime p)),
      rw [← zpow_neg_one, zpow_lt_iff_lt this],
      have : 0 ≤ padic_val_rat p m, simp only [of_int, nat.cast_nonneg],
      intro h,
      rw [← zpow_zero (p : ℚ), zpow_inj];
      linarith, } },
end

lemma int_lt_one_iff (m : ℤ) : padic_norm p m < 1 ↔ (p : ℤ) ∣ m :=
begin
  rw [← not_iff_not, ← int_eq_one_iff, eq_iff_le_not_lt],
  simp only [padic_norm.of_int, true_and],
end

lemma of_nat (m : ℕ) : padic_norm p m ≤ 1 := padic_norm.of_int (m : ℤ)

/-- The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`. -/
lemma nat_eq_one_iff (m : ℕ) : padic_norm p m = 1 ↔ ¬ p ∣ m :=
by simp only [←int.coe_nat_dvd, ←int_eq_one_iff, int.cast_coe_nat]

lemma nat_lt_one_iff (m : ℕ) : padic_norm p m < 1 ↔ p ∣ m :=
by simp only [←int.coe_nat_dvd, ←int_lt_one_iff, int.cast_coe_nat]

open_locale big_operators

lemma sum_lt {α : Type*} {F : α → ℚ} {t : ℚ} {s : finset α} :
  s.nonempty → (∀ i ∈ s, padic_norm p (F i) < t) → padic_norm p (∑ i in s, F i) < t :=
begin
  classical,
  refine s.induction_on (by { rintro ⟨-, ⟨⟩⟩, }) _,
  rintro a S haS IH - ht,
  by_cases hs : S.nonempty,
  { rw finset.sum_insert haS,
    exact lt_of_le_of_lt padic_norm.nonarchimedean (max_lt
      (ht a (finset.mem_insert_self a S))
      (IH hs (λ b hb, ht b (finset.mem_insert_of_mem hb)))), },
  { simp * at *, },
end

lemma sum_le {α : Type*} {F : α → ℚ} {t : ℚ} {s : finset α} :
  s.nonempty → (∀ i ∈ s, padic_norm p (F i) ≤ t) → padic_norm p (∑ i in s, F i) ≤ t :=
begin
  classical,
  refine s.induction_on (by { rintro ⟨-, ⟨⟩⟩, }) _,
  rintro a S haS IH - ht,
  by_cases hs : S.nonempty,
  { rw finset.sum_insert haS,
    exact padic_norm.nonarchimedean.trans (max_le
      (ht a (finset.mem_insert_self a S))
      (IH hs (λ b hb, ht b (finset.mem_insert_of_mem hb)))), },
  { simp * at *, },
end

lemma sum_lt' {α : Type*} {F : α → ℚ} {t : ℚ} {s : finset α} (hF : ∀ i ∈ s, padic_norm p (F i) < t)
  (ht : 0 < t) : padic_norm p (∑ i in s, F i) < t :=
begin
  obtain rfl | hs := finset.eq_empty_or_nonempty s,
  { simp [ht], },
  { exact sum_lt hs hF, },
end

lemma sum_le' {α : Type*} {F : α → ℚ} {t : ℚ} {s : finset α} (hF : ∀ i ∈ s, padic_norm p (F i) ≤ t)
  (ht : 0 ≤ t) : padic_norm p (∑ i in s, F i) ≤ t :=
begin
  obtain rfl | hs := finset.eq_empty_or_nonempty s,
  { simp [ht], },
  { exact sum_le hs hF, },
end

end padic_norm
