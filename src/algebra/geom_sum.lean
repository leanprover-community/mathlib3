/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

Sums of finite geometric series
-/
import algebra.group_with_zero_power
import algebra.big_operators

universe u
variable {α : Type u}

open finset

open_locale big_operators

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i$. -/
def geom_series [semiring α] (x : α) (n : ℕ) :=
∑ i in range n, x ^ i

theorem geom_series_def [semiring α] (x : α) (n : ℕ) :
  geom_series x n = ∑ i in range n, x ^ i := rfl

@[simp] theorem geom_series_zero [semiring α] (x : α) :
  geom_series x 0 = 0 := rfl

@[simp] theorem geom_series_one [semiring α] (x : α) :
  geom_series x 1 = 1 :=
by { rw [geom_series_def, sum_range_one, pow_zero] }

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i y^{n-1-i}$. -/
def geom_series₂ [semiring α] (x y : α) (n : ℕ) :=
∑ i in range n, x ^ i * (y ^ (n - 1 - i))

theorem geom_series₂_def [semiring α] (x y : α) (n : ℕ) :
  geom_series₂ x y n = ∑ i in range n, x ^ i * y ^ (n - 1 - i) := rfl

@[simp] theorem geom_series₂_zero [semiring α] (x y : α) :
  geom_series₂ x y 0 = 0 := rfl

@[simp] theorem geom_series₂_one [semiring α] (x y : α) :
  geom_series₂ x y 1 = 1 :=
by { have : 1 - 1 - 0 = 0 := rfl,
     rw [geom_series₂_def, sum_range_one, this, pow_zero, pow_zero, mul_one] }

@[simp] theorem geom_series₂_with_one [semiring α] (x : α) (n : ℕ) :
  geom_series₂ x 1 n = geom_series x n :=
sum_congr rfl (λ i _, by { rw [one_pow, mul_one] })

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem commute.geom_sum₂_mul_add [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_series₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
begin
  let f := λ (m i : ℕ), (x + y) ^ i * y ^ (m - 1 - i),
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n,
  induction n with n ih,
  { rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero] },
  { have f_last : f (n + 1) n = (x + y) ^ n :=
     by { dsimp [f],
          rw [nat.sub_sub, nat.add_comm, nat.sub_self, pow_zero, mul_one] },
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i :=
      λ i hi, by {
        dsimp [f],
        have : commute y ((x + y) ^ i) :=
         (h.symm.add_right (commute.refl y)).pow_right i,
        rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ y (n - 1 - i)],
        congr' 2,
        rw [nat.add_sub_cancel, nat.sub_sub, add_comm 1 i],
        have : i + 1 + (n - (i + 1)) = n := nat.add_sub_of_le (mem_range.mp hi),
        rw [add_comm (i + 1)] at this,
        rw [← this, nat.add_sub_cancel, add_comm i 1, ← add_assoc,
            nat.add_sub_cancel] },
    rw [pow_succ (x + y), add_mul, sum_range_succ, f_last, add_mul, add_assoc],
    rw [(((commute.refl x).add_right h).pow_right n).eq],
    congr' 1,
    rw[sum_congr rfl f_succ, ← mul_sum, pow_succ y],
    rw[mul_assoc, ← mul_add y, ih] }
end

theorem geom_series₂_self {α : Type*} [comm_ring α] (x : α) (n : ℕ) :
  geom_series₂ x x n = n * x ^ (n-1) :=
calc  ∑ i in finset.range n, x ^ i * x ^ (n - 1 - i)
    = ∑ i in finset.range n, x ^ (i + (n - 1 - i)) : by simp_rw [← pow_add]
... = ∑ i in finset.range n, x ^ (n - 1) : finset.sum_congr rfl
  (λ i hi, congr_arg _ $ nat.add_sub_cancel' $ nat.le_pred_of_lt $ finset.mem_range.1 hi)
... = (finset.range n).card •ℕ (x ^ (n - 1)) : finset.sum_const _
... = n * x ^ (n - 1) : by rw [finset.card_range, nsmul_eq_mul]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [comm_semiring α] (x y : α) (n : ℕ) :
  (geom_series₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
(commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [semiring α] (x : α) (n : ℕ) :
  (geom_series (x + 1) n) * x + 1 = (x + 1) ^ n :=
begin
  have := (commute.one_right x).geom_sum₂_mul_add n,
  rw [one_pow, geom_series₂_with_one] at this,
  exact this
end

theorem geom_sum₂_mul_comm [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_series₂ x y n) * (x - y) = x ^ n - y ^ n :=
begin
  have := (h.sub_left (commute.refl y)).geom_sum₂_mul_add n,
  rw [sub_add_cancel] at this,
  rw [← this, add_sub_cancel]
end

theorem geom_sum₂_mul [comm_ring α] (x y : α) (n : ℕ) :
  (geom_series₂ x y n) * (x - y) = x ^ n - y ^ n :=
geom_sum₂_mul_comm (commute.all x y) n

theorem geom_sum_mul [ring α] (x : α) (n : ℕ) :
  (geom_series x n) * (x - 1) = x ^ n - 1 :=
begin
  have := geom_sum₂_mul_comm (commute.one_right x) n,
  rw [one_pow, geom_series₂_with_one] at this,
  exact this
end

theorem geom_sum_mul_neg [ring α] (x : α) (n : ℕ) :
  (geom_series x n) * (1 - x) = 1 - x ^ n :=
begin
  have := congr_arg has_neg.neg (geom_sum_mul x n),
  rw [neg_sub, ← mul_neg_eq_neg_mul_symm, neg_sub] at this,
  exact this
end

theorem geom_sum [division_ring α] {x : α} (h : x ≠ 1) (n : ℕ) :
  (geom_series x n) = (x ^ n - 1) / (x - 1) :=
have x - 1 ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← geom_sum_mul, mul_div_cancel _ this]

theorem geom_sum_Ico_mul [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (x - 1) = x^n - x^m :=
by rw [sum_Ico_eq_sub _ hmn, ← geom_series_def, ← geom_series_def, sub_mul,
  geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (1 - x) = x^m - x^n :=
by rw [sum_Ico_eq_sub _ hmn, ← geom_series_def, ← geom_series_def, sub_mul,
  geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

theorem geom_sum_Ico [division_ring α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) :=
by simp only [sum_Ico_eq_sub _ hmn, (geom_series_def _ _).symm, geom_sum hx, div_sub_div_same,
  sub_sub_sub_cancel_right]

lemma geom_sum_inv [division_ring α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
  (geom_series x⁻¹ n) = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) :=
have h₁ : x⁻¹ ≠ 1, by rwa [inv_eq_one_div, ne.def, div_eq_iff_mul_eq hx0, one_mul],
have h₂ : x⁻¹ - 1 ≠ 0, from mt sub_eq_zero.1 h₁,
have h₃ : x - 1 ≠ 0, from mt sub_eq_zero.1 hx1,
have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
  nat.rec_on n (by simp)
  (λ n h, by rw [pow_succ, mul_inv_rev', ←mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc,
    inv_mul_cancel hx0]),
begin
  rw [geom_sum h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel h₃],
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm, add_left_comm],
end

variables {β : Type*}

theorem ring_hom.map_geom_series [semiring α] [semiring β] (x : α) (n : ℕ) (f : α →+* β) :
  f (geom_series x n) = geom_series (f x) n :=
by simp [geom_series_def, f.map_sum]

theorem ring_hom.map_geom_series₂ [semiring α] [semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
  f (geom_series₂ x y n) = geom_series₂ (f x) (f y) n :=
by simp [geom_series₂_def, f.map_sum]
