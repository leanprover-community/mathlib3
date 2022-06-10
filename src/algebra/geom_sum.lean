/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/

import algebra.group_with_zero.power
import algebra.big_operators.order
import algebra.big_operators.ring
import algebra.big_operators.intervals
import tactic.abel
import data.nat.parity

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-y^{n-m}x^m}{x-y}$ in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

universe u
variable {α : Type u}

open finset mul_opposite

open_locale big_operators

section semiring
variable [semiring α]

lemma geom_sum_succ {x : α} {n : ℕ} :
  ∑ i in range (n + 1), x ^ i = x * ∑ i in range n, x ^ i + 1 :=
by simp only [mul_sum, ←pow_succ, sum_range_succ', pow_zero]

lemma geom_sum_succ' {x : α} {n : ℕ} :
  ∑ i in range (n + 1), x ^ i = x ^ n + ∑ i in range n, x ^ i :=
(sum_range_succ _ _).trans (add_comm _ _)

theorem geom_sum_zero (x : α) :
  ∑ i in range 0, x ^ i = 0 := rfl

theorem geom_sum_one (x : α) :
  ∑ i in range 1, x ^ i = 1 :=
by simp [geom_sum_succ']

@[simp] lemma geom_sum_two {x : α} : ∑ i in range 2, x ^ i = x + 1 :=
by simp [geom_sum_succ']

@[simp] lemma zero_geom_sum : ∀ {n}, ∑ i in range n, (0 : α) ^ i = if n = 0 then 0 else 1
| 0     := by simp
| 1     := by simp
| (n+2) := by { rw geom_sum_succ', simp [zero_geom_sum] }

lemma one_geom_sum (n : ℕ) : ∑ i in range n, (1 : α) ^ i = n :=
by simp

@[simp] lemma op_geom_sum (x : α) (n : ℕ) :
  op (∑ i in range n, x ^ i) = ∑ i in range n, (op x) ^ i :=
by simp

@[simp] lemma op_geom_sum₂ (x y : α) (n : ℕ) :
  op (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) =
    ∑ i in range n, (op y) ^ i * ((op x) ^ (n - 1 - i)) :=
begin
  simp only [op_sum, op_mul, op_pow],
  rw ← sum_range_reflect,
  refine sum_congr rfl (λ j j_in, _),
  rw [mem_range, nat.lt_iff_add_one_le] at j_in,
  congr,
  apply tsub_tsub_cancel_of_le,
  exact le_tsub_of_add_le_right j_in
end

theorem geom_sum₂_with_one (x : α) (n : ℕ) :
  ∑ i in range n, x ^ i * (1 ^ (n - 1 - i)) = ∑ i in range n, x ^ i :=
sum_congr rfl (λ i _, by { rw [one_pow, mul_one] })

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem commute.geom_sum₂_mul_add {x y : α} (h : commute x y) (n : ℕ) :
  (∑ i in range n, (x + y) ^ i * (y ^ (n - 1 - i))) * x + y ^ n = (x + y) ^ n :=
begin
  let f := λ (m i : ℕ), (x + y) ^ i * y ^ (m - 1 - i),
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n,
  induction n with n ih,
  { rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero] },
  { have f_last : f (n + 1) n = (x + y) ^ n :=
     by { dsimp [f],
          rw [← tsub_add_eq_tsub_tsub, nat.add_comm, tsub_self, pow_zero, mul_one] },
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i :=
      λ i hi, by
      { dsimp [f],
        have : commute y ((x + y) ^ i) :=
         (h.symm.add_right (commute.refl y)).pow_right i,
        rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ y (n - 1 - i)],
        congr' 2,
        rw [add_tsub_cancel_right, ← tsub_add_eq_tsub_tsub, add_comm 1 i],
        have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi),
        rw [add_comm (i + 1)] at this,
        rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc,
            add_tsub_cancel_right] },
    rw [pow_succ (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc],
    rw (((commute.refl x).add_right h).pow_right n).eq,
    congr' 1,
    rw [sum_congr rfl f_succ, ← mul_sum, pow_succ y, mul_assoc, ← mul_add y, ih] }
end

end semiring

@[simp] lemma neg_one_geom_sum [ring α] {n : ℕ} :
  ∑ i in range n, (-1 : α) ^ i = if even n then 0 else 1 :=
begin
  induction n with k hk,
  { simp },
  { simp only [geom_sum_succ', nat.even_succ, hk],
    split_ifs,
    { rw [h.neg_one_pow, add_zero] },
    { rw [(nat.odd_iff_not_even.2 h).neg_one_pow, neg_add_self] } }
end

theorem geom_sum₂_self {α : Type*} [comm_ring α] (x : α) (n : ℕ) :
  ∑ i in range n, x ^ i * (x ^ (n - 1 - i)) = n * x ^ (n-1) :=
calc  ∑ i in finset.range n, x ^ i * x ^ (n - 1 - i)
    = ∑ i in finset.range n, x ^ (i + (n - 1 - i)) : by simp_rw [← pow_add]
... = ∑ i in finset.range n, x ^ (n - 1) : finset.sum_congr rfl
  (λ i hi, congr_arg _ $ add_tsub_cancel_of_le $ nat.le_pred_of_lt $ finset.mem_range.1 hi)
... = (finset.range n).card • (x ^ (n - 1)) : finset.sum_const _
... = n * x ^ (n - 1) : by rw [finset.card_range, nsmul_eq_mul]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [comm_semiring α] (x y : α) (n : ℕ) :
  (∑ i in range n, (x + y) ^ i * (y ^ (n - 1 - i))) * x + y ^ n = (x + y) ^ n :=
(commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [semiring α] (x : α) (n : ℕ) :
  (∑ i in range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n :=
begin
  have := (commute.one_right x).geom_sum₂_mul_add n,
  rw [one_pow, geom_sum₂_with_one] at this,
  exact this
end

protected theorem commute.geom_sum₂_mul [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) * (x - y) = x ^ n - y ^ n :=
begin
  have := (h.sub_left (commute.refl y)).geom_sum₂_mul_add n,
  rw [sub_add_cancel] at this,
  rw [← this, add_sub_cancel]
end

lemma commute.mul_neg_geom_sum₂ [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (y - x) * (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) = y ^ n - x ^ n :=
begin
  apply op_injective,
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow],
  exact (commute.op h.symm).geom_sum₂_mul n
end

lemma commute.mul_geom_sum₂ [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (x - y) * (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) = x ^ n - y ^ n :=
by rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]

theorem geom_sum₂_mul [comm_ring α] (x y : α) (n : ℕ) :
  (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) * (x - y) = x ^ n - y ^ n :=
(commute.all x y).geom_sum₂_mul n

theorem geom_sum_mul [ring α] (x : α) (n : ℕ) :
  (∑ i in range n, x ^ i) * (x - 1) = x ^ n - 1 :=
begin
  have := (commute.one_right x).geom_sum₂_mul n,
  rw [one_pow, geom_sum₂_with_one] at this,
  exact this
end

lemma mul_geom_sum [ring α] (x : α) (n : ℕ) :
  (x - 1) * (∑ i in range n, x ^ i) = x ^ n - 1 :=
op_injective $ by simpa using geom_sum_mul (op x) n

theorem geom_sum_mul_neg [ring α] (x : α) (n : ℕ) :
  (∑ i in range n, x ^ i) * (1 - x) = 1 - x ^ n :=
begin
  have := congr_arg has_neg.neg (geom_sum_mul x n),
  rw [neg_sub, ← mul_neg, neg_sub] at this,
  exact this
end

lemma mul_neg_geom_sum [ring α] (x : α) (n : ℕ) :
  (1 - x) * (∑ i in range n, x ^ i) = 1 - x ^ n :=
op_injective $ by simpa using geom_sum_mul_neg (op x) n

protected theorem commute.geom_sum₂ [division_ring α] {x y : α} (h' : commute x y) (h : x ≠ y)
  (n : ℕ) : (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) = (x ^ n - y ^ n) / (x - y) :=
have x - y ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← h'.geom_sum₂_mul, mul_div_cancel _ this]

theorem geom₂_sum [field α] {x y : α} (h : x ≠ y) (n : ℕ) :
  (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) = (x ^ n - y ^ n) / (x - y) :=
(commute.all x y).geom_sum₂ h n

theorem geom_sum_eq [division_ring α] {x : α} (h : x ≠ 1) (n : ℕ) :
  (∑ i in range n, x ^ i) = (x ^ n - 1) / (x - 1) :=
have x - 1 ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← geom_sum_mul, mul_div_cancel _ this]

protected theorem commute.mul_geom_sum₂_Ico [ring α] {x y : α} (h : commute x y) {m n : ℕ}
  (hmn : m ≤ n) :
  (x - y) * (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
begin
  rw [sum_Ico_eq_sub _ hmn],
  have : ∑ k in range m, x ^ k * y ^ (n - 1 - k)
    = ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)),
  { refine sum_congr rfl (λ j j_in, _),
    rw ← pow_add,
    congr,
    rw [mem_range, nat.lt_iff_add_one_le, add_comm] at j_in,
    have h' : n - m + (m - (1 + j)) = n - (1 + j) := tsub_add_tsub_cancel hmn j_in,
    rw [← tsub_add_eq_tsub_tsub m, h', ← tsub_add_eq_tsub_tsub] },
  rw this,
  simp_rw pow_mul_comm y (n-m) _,
  simp_rw ← mul_assoc,
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc,
    h.mul_geom_sum₂, sub_mul, ← pow_add, add_tsub_cancel_of_le hmn,
    sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)],
end

protected theorem commute.geom_sum₂_succ_eq {α : Type u} [ring α] {x y : α}
  (h : commute x y) {n : ℕ} :
  ∑ i in range (n + 1), x ^ i * (y ^ (n - i)) =
    x ^ n + y * (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) :=
begin
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ←mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ←pow_succ],
  refine sum_congr rfl (λ i hi, _),
  suffices : n - 1 - i + 1 = n - i, { rw this },
  cases n,
  { exact absurd (list.mem_range.mp hi) i.not_lt_zero },
  { rw [tsub_add_eq_add_tsub (nat.le_pred_of_lt (list.mem_range.mp hi)),
        tsub_add_cancel_of_le (nat.succ_le_iff.mpr n.succ_pos)] },
end

theorem geom_sum₂_succ_eq {α : Type u} [comm_ring α] (x y : α)  {n : ℕ} :
  ∑ i in range (n + 1), x ^ i * (y ^ (n - i)) =
    x ^ n + y * (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) :=
(commute.all x y).geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [comm_ring α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
  (x - y) * (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
(commute.all x y).mul_geom_sum₂_Ico hmn

protected theorem commute.geom_sum₂_Ico_mul [ring α] {x y : α} (h : commute x y) {m n : ℕ}
  (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n -  y ^ (n - m) * x ^ m :=
begin
  apply op_injective,
  simp only [op_sub, op_mul, op_pow, op_sum],
  have : ∑ k in Ico m n, op y ^ (n - 1 - k) * op x ^ k
    = ∑ k in Ico m n, op x ^ k * op y ^ (n - 1 - k),
  { refine sum_congr rfl (λ k k_in, _),
    apply commute.pow_pow (commute.op h.symm) },
  rw this,
  exact (commute.op h).mul_geom_sum₂_Ico hmn
end

theorem geom_sum_Ico_mul [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (x - 1) = x^n - x^m :=
by rw [sum_Ico_eq_sub _ hmn, sub_mul,
  geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (1 - x) = x^m - x^n :=
by rw [sum_Ico_eq_sub _ hmn, sub_mul,
  geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

protected theorem commute.geom_sum₂_Ico [division_ring α] {x y : α} (h : commute x y) (hxy : x ≠ y)
  {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m ) / (x - y) :=
have x - y ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel _ this]

theorem geom_sum₂_Ico [field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m ) / (x - y) :=
(commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [division_ring α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) :=
by simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same,
  sub_sub_sub_cancel_right]

theorem geom_sum_Ico' [division_ring α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) :=
by { simp only [geom_sum_Ico hx hmn], convert neg_div_neg_eq (x^m - x^n) (1-x); abel }

lemma geom_sum_Ico_le_of_lt_one [linear_ordered_field α]
  {x : α} (hx : 0 ≤ x) (h'x : x < 1) {m n : ℕ} :
  ∑ i in Ico m n, x ^ i ≤ x ^ m / (1 - x) :=
begin
  rcases le_or_lt m n with hmn | hmn,
  { rw geom_sum_Ico' h'x.ne hmn,
    apply div_le_div (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl,
    simpa using pow_nonneg hx _ },
  { rw [Ico_eq_empty, sum_empty],
    { apply div_nonneg (pow_nonneg hx _),
      simpa using h'x.le },
    { simpa using hmn.le } },
end

lemma geom_sum_inv [division_ring α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
  (∑ i in range n, x⁻¹ ^ i) = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) :=
have h₁ : x⁻¹ ≠ 1, by rwa [inv_eq_one_div, ne.def, div_eq_iff_mul_eq hx0, one_mul],
have h₂ : x⁻¹ - 1 ≠ 0, from mt sub_eq_zero.1 h₁,
have h₃ : x - 1 ≠ 0, from mt sub_eq_zero.1 hx1,
have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
  nat.rec_on n (by simp)
  (λ n h, by rw [pow_succ, mul_inv_rev, ←mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc,
    inv_mul_cancel hx0]),
begin
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel h₃],
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm,
    add_left_comm],
end

variables {β : Type*}

theorem ring_hom.map_geom_sum [semiring α] [semiring β] (x : α) (n : ℕ) (f : α →+* β) :
  f (∑ i in range n, x ^ i) = ∑ i in range n, (f x) ^ i :=
by simp [f.map_sum]

theorem ring_hom.map_geom_sum₂ [semiring α] [semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
  f (∑ i in range n, x ^ i * (y ^ (n - 1 - i))) =
    ∑ i in range n, (f x) ^ i * ((f y) ^ (n - 1 - i)) :=
by simp [f.map_sum]

/-! ### Geometric sum with `ℕ`-division -/

lemma nat.pred_mul_geom_sum_le (a b n : ℕ) :
  (b - 1) * ∑ i in range n.succ, a/b^i ≤ a * b - a/b^n :=
calc
  (b - 1) * (∑ i in range n.succ, a/b^i)
      = ∑ i in range n, a/b^(i + 1) * b + a * b
        - (∑ i in range n, a/b^i + a/b^n)
      : by rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ',
          sum_range_succ, pow_zero, nat.div_one]
  ... ≤ ∑ i in range n, a/b^i + a * b - (∑ i in range n, a/b^i + a/b^n)
      : begin
        refine tsub_le_tsub_right (add_le_add_right (sum_le_sum $ λ i _, _) _) _,
        rw [pow_succ', ←nat.div_div_eq_div_mul],
        exact nat.div_mul_le_self _ _,
      end
  ... = a * b - a/b^n : add_tsub_add_eq_tsub_left _ _ _

lemma nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in range n, a/b^i ≤ a * b/(b - 1) :=
begin
  refine (nat.le_div_iff_mul_le _ _ $ tsub_pos_of_lt hb).2 _,
  cases n,
  { rw [sum_range_zero, zero_mul],
    exact nat.zero_le _ },
  rw mul_comm,
  exact (nat.pred_mul_geom_sum_le a b n).trans tsub_le_self,
end

lemma nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in Ico 1 n, a/b^i ≤ a/(b - 1) :=
begin
  cases n,
  { rw [Ico_eq_empty_of_le zero_le_one, sum_empty],
    exact nat.zero_le _ },
  rw ←add_le_add_iff_left a,
  calc
    a + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i
        = a/b^0 + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i : by rw [pow_zero, nat.div_one]
    ... = ∑ i in range n.succ, a/b^i : begin
          rw [range_eq_Ico, ←nat.Ico_insert_succ_left (nat.succ_pos _), sum_insert],
          exact λ h, zero_lt_one.not_le (mem_Ico.1 h).1,
        end
    ... ≤ a * b/(b - 1) : nat.geom_sum_le hb a _
    ... = (a * 1 + a * (b - 1))/(b - 1)
        : by rw [←mul_add, add_tsub_cancel_of_le (one_le_two.trans hb)]
    ... = a + a/(b - 1)
        : by rw [mul_one, nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]
end

section order

variables {n : ℕ} {x : α}

lemma geom_sum_pos [ordered_semiring α] (hx : 0 < x) (hn : n ≠ 0) : 0 < ∑ i in range n, x ^ i :=
begin
  refine nat.le_induction _ _ _ (show 1 ≤ n, from hn.bot_lt),
  { simp [@@zero_lt_one _ (nontrivial_of_lt _ _ hx)] },
  intros k hk,
  rw [geom_sum_succ'],
  apply add_pos (pow_pos hx _)
end

lemma geom_sum_pos_and_lt_one [ordered_ring α] (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
  0 < ∑ i in range n, x ^ i ∧ ∑ i in range n, x ^ i < 1 :=
begin
  refine nat.le_induction _ _ n (show 2 ≤ n, from hn),
  { rw geom_sum_two,
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩ },
  clear hn n,
  intros n hn ihn,
  rw [geom_sum_succ, add_lt_iff_neg_right, ← neg_lt_iff_pos_add', neg_mul_eq_neg_mul],
  exact ⟨mul_lt_one_of_nonneg_of_lt_one_left (neg_nonneg.2 hx.le)
    (neg_lt_iff_pos_add'.2 hx') ihn.2.le, mul_neg_of_neg_of_pos hx ihn.1⟩
end

lemma geom_sum_alternating_of_lt_neg_one [ordered_ring α] (hx : x + 1 < 0) (hn : 1 < n) :
  if even n then ∑ i in range n, x ^ i < 0 else 1 < ∑ i in range n, x ^ i  :=
begin
  have hx0 : x < 0, from ((le_add_iff_nonneg_right _).2 (@zero_le_one α _)).trans_lt hx,
  refine nat.le_induction _ _ n (show 2 ≤ n, from hn),
  { simp only [geom_sum_two, hx, true_or, even_bit0, if_true_left_eq_or] },
  clear hn n,
  intros n hn ihn,
  simp only [nat.even_succ, geom_sum_succ],
  by_cases hn' : even n,
  { rw [if_pos hn'] at ihn, rw [if_neg, lt_add_iff_pos_left],
    exact mul_pos_of_neg_of_neg hx0 ihn, exact not_not_intro hn', },
  { rw [if_neg hn'] at ihn, rw [if_pos], swap, { exact hn' },
    have := add_lt_add_right (mul_lt_mul_of_neg_left ihn hx0) 1,
    rw mul_one at this,
    exact this.trans hx }
end

lemma geom_sum_pos_of_odd [linear_ordered_ring α] (h : odd n) :
  0 < ∑ i in range n, x ^ i :=
begin
  rcases n with (_ | _ | k),
  { exact ((show ¬ odd 0, from dec_trivial) h).elim },
  { simp only [geom_sum_one, zero_lt_one] },
  rw nat.odd_iff_not_even at h,
  rcases lt_trichotomy (x + 1) 0 with hx | hx | hx,
  { have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ,
    simp only [h, if_false] at this,
    exact zero_lt_one.trans this },
  { simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, if_false, zero_lt_one] },
  rcases lt_trichotomy x 0 with hx' | rfl | hx',
  { exact (geom_sum_pos_and_lt_one hx' hx k.one_lt_succ_succ).1 },
  { simp only [zero_geom_sum, nat.succ_ne_zero, if_false, zero_lt_one] },
  { exact geom_sum_pos hx' (by simp only [nat.succ_ne_zero, ne.def, not_false_iff]) }
end

lemma geom_sum_pos_iff [linear_ordered_ring α] (hn : 1 < n) :
  0 < ∑ i in range n, x ^ i ↔ odd n ∨ 0 < x + 1 :=
begin
  refine ⟨λ h, _, _⟩,
  { suffices : ¬ 0 < x + 1 → odd n, by tauto,
    intro hx,
    rw not_lt at hx,
    contrapose! h,
    rw [←nat.even_iff_not_odd] at h,
    rcases hx.eq_or_lt with hx | hx,
    { rw [←neg_neg (1 : α), add_neg_eq_iff_eq_add, zero_add] at hx,
      simp only [hx, neg_one_geom_sum, h, if_true] },
    apply le_of_lt,
    simpa [h] using geom_sum_alternating_of_lt_neg_one hx hn },
  { rintro (hn | hx'),
    { exact geom_sum_pos_of_odd hn },
    rcases lt_trichotomy x 0 with hx | rfl | hx,
    { exact (geom_sum_pos_and_lt_one hx hx' hn).1 },
    { simp only [(zero_lt_one.trans hn).ne', zero_geom_sum, if_false, zero_lt_one] },
    { exact geom_sum_pos hx (zero_lt_one.trans hn).ne' } }
end

lemma geom_sum_eq_zero_iff_neg_one [linear_ordered_ring α] (hn : 1 < n) :
  ∑ i in range n, x ^ i = 0 ↔ x = -1 ∧ even n :=
begin
  refine ⟨λ h, _, λ ⟨h, hn⟩, by simp only [h, hn, neg_one_geom_sum, if_true]⟩,
  contrapose! h,
  rcases eq_or_ne x (-1) with rfl | h,
  { simp only [h rfl, neg_one_geom_sum, if_false, ne.def, not_false_iff, one_ne_zero] },
  rw [ne.def, eq_neg_iff_add_eq_zero, ←ne.def] at h,
  rcases h.lt_or_lt with h | h,
  { have := geom_sum_alternating_of_lt_neg_one h hn,
    split_ifs at this,
    { exact this.ne },
    { exact (zero_lt_one.trans this).ne' } },
  apply ne_of_gt,
  rcases lt_trichotomy x 0 with h' | rfl | h',
  { exact (geom_sum_pos_and_lt_one h' h hn).1 },
  { simp only [(pos_of_gt hn).ne', zero_geom_sum, if_false, zero_lt_one] },
  { exact geom_sum_pos h' (pos_of_gt hn).ne' }
end

lemma geom_sum_neg_iff [linear_ordered_ring α] (hn : 1 < n) :
  ∑ i in range n, x ^ i < 0 ↔ even n ∧ x + 1 < 0 :=
by rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
       or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), nat.odd_iff_not_even,
       ← add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm,
       ← imp_iff_not_or, or_comm, and_comm, decidable.and_or_imp, or_comm]

end order
