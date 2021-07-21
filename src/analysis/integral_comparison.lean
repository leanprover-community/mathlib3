import measure_theory.integral_eq_improper

open measure_theory set

open_locale nnreal ennreal big_operators

variables {f : ℝ → ℝ} (hpos : 0 ≤ᵐ[volume.restrict (Ici 0)] f)
          (hmono : ∀ ⦃x y⦄, 0 ≤ x → x ≤ y → f y ≤ f x)

include hmono

#check interval_integral.integral_const

lemma integral_le (n : ℕ) : ∫ (x : ℝ) in n..(n+1), f x ≤ f n :=
calc ∫ (x : ℝ) in n..(n+1), f x
      ≤ ∫ (x : ℝ) in n..(n+1), f n : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        sorry
        (continuous_const.interval_integrable _ _)
        (λ x hx, hmono n.cast_nonneg hx.1)
  ... = f n : by simp

lemma le_integral (n : ℕ) : f (n + 1) ≤ ∫ (x : ℝ) in n..(n+1), f x :=
calc f (n+1)
      = ∫ (x : ℝ) in n..(n+1), f (n+1) : by simp
  ... ≤ ∫ (x : ℝ) in n..(n+1), f x : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        (continuous_const.interval_integrable _ _)
        sorry
        (λ x hx, hmono (n.cast_nonneg.trans hx.1) hx.2)

lemma le_integral' (n : ℕ) (h : n ≠ 0) : f n ≤ ∫ (x : ℝ) in (n-1)..n, f x :=
begin
  rcases nat.exists_eq_succ_of_ne_zero h with ⟨k, rfl⟩,
  rw [nat.cast_succ, add_sub_cancel],
  exact le_integral hmono k,
end

lemma integral_le_sum (n : ℕ) : ∫ (x : ℝ) in 0..n, f x ≤ ∑ (k : ℕ) in finset.range n, f k :=
begin
  have : ∑ (k : ℕ) in finset.range n, ∫ (x : ℝ) in k..↑(k+1), f x
          ≤ ∑ (k : ℕ) in finset.range n, f k :=
    finset.sum_le_sum (λ (k : ℕ) (hk : k ∈ finset.range n), integral_le hmono k),
  rwa interval_integral.sum_integral_adjacent_intervals at this,
  intros k hk,
  sorry
end

include hpos

theorem goal : summable (λ (n : ℕ), f n) ↔ integrable_on f (Ici 0) :=
begin
  split; intro h,
  {  },
  {  }
end
