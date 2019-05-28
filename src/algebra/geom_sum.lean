import algebra.big_operators algebra.commute

universe u
variable {α : Type u}

open finset

def geom_series [semiring α] (x : α) (n : ℕ) :=
(range n).sum (λ i, x ^ i)

theorem geom_series_def [semiring α] (x : α) (n : ℕ) :
  geom_series x n = (range n).sum (λ i, x ^ i) := rfl

def geom_series₂ [semiring α] (x y : α) (n : ℕ) :=
(range n).sum (λ i, x ^ i * (y ^ (n - 1 - i)))

theorem geom_series₂_with_one [semiring α] (x : α) (n : ℕ) :
  geom_series₂ x 1 n = geom_series x n :=
sum_congr rfl (λ i _, by { rw [one_pow, mul_one] })

theorem geom_series₂_zero [semiring α] (x y : α) :
  geom_series₂ x y 0 = 0 :=
by simp [geom_series₂]

theorem geom_sum₂_mul_add_comm [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_series₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
begin
  let f := λ (m i : ℕ), (x + y) ^ i * y ^ (m - 1 - i),
  change ((range n).sum (f n)) * x + y ^ n = (x + y) ^ n,
  induction n with n ih,
  { rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero] },
  { have f_last : f n.succ n = (x + y) ^ n :=
     by { dsimp [f],
          rw [nat.sub_sub, nat.add_comm, nat.sub_self, pow_zero, mul_one] },
    have f_succ : ∀ i, i ∈ range n → f n.succ i = y * f n i :=
      λ i hi, by {
        dsimp [f],
        have : commute y ((x + y) ^ i) :=
         (h.symm.add (commute.refl y)).pow i,
        rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ y (n - 1 - i)],
        congr' 2,
        rw [nat.succ_eq_add_one, nat.add_sub_cancel, nat.sub_sub, add_comm 1 i],
        have := nat.add_sub_of_le (mem_range.mp hi),
        rw [add_comm, nat.succ_eq_add_one] at this,
        rw [← this, nat.add_sub_cancel, add_comm i 1, ← add_assoc,
            nat.add_sub_cancel] },
    rw [pow_succ (x + y), add_mul, sum_range_succ, f_last, add_mul, add_assoc],
    rw [(((commute.refl x).add h).pow n).eq],
    congr' 1,
    rw[sum_congr rfl f_succ, ← mul_sum, pow_succ y],
    rw[mul_assoc, ← mul_add y, ih] }
end

theorem geom_sum₂_mul_add [comm_semiring α] (x y : α) (n : ℕ) :
  (geom_series₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
geom_sum₂_mul_add_comm (all_commute x y) n

theorem geom_sum_mul_add [semiring α] (x : α) (n : ℕ) :
  (geom_series (x + 1) n) * x + 1 = (x + 1) ^ n :=
begin
  have := geom_sum₂_mul_add_comm (commute.one x) n,
  rw [one_pow, geom_series₂_with_one] at this,
  exact this
end

theorem geom_sum₂_mul_comm [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_series₂ x y n) * (x - y) = x ^ n - y ^ n :=
begin
  have := geom_sum₂_mul_add_comm (h.sub_left (commute.refl y)) n,
  rw [sub_add_cancel] at this,
  rw [← this, add_sub_cancel]
end

theorem geom_sum₂_mul [comm_ring α] (x y : α) (n : ℕ) :
  (geom_series₂ x y n) * (x - y) = x ^ n - y ^ n :=
geom_sum₂_mul_comm (all_commute x y) n

theorem geom_sum_mul [ring α] (x : α) (n : ℕ) :
  (geom_series x n) * (x - 1) = x ^ n - 1 :=
begin
  have := geom_sum₂_mul_comm (commute.one x) n,
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

lemma geom_sum_inv [division_ring α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
  (geom_series x⁻¹ n) = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) :=
have h₁ : x⁻¹ ≠ 1, by rwa [inv_eq_one_div, ne.def, div_eq_iff_mul_eq hx0, one_mul],
have h₂ : x⁻¹ - 1 ≠ 0, from mt sub_eq_zero.1 h₁,
have h₃ : x - 1 ≠ 0, from mt sub_eq_zero.1 hx1,
have h₄ : x * x⁻¹ ^ n = x⁻¹ ^ n * x,
  from nat.cases_on n (by simp)
  (λ _, by conv { to_rhs, rw [pow_succ', mul_assoc, inv_mul_cancel hx0, mul_one] };
    rw [pow_succ, ← mul_assoc, mul_inv_cancel hx0, one_mul]),
by rw [geom_sum h₁, div_eq_iff_mul_eq h₂, ← domain.mul_left_inj h₃,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel h₃];
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄]
