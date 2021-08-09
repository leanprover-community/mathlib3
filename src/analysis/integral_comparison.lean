import measure_theory.integral_eq_improper

open measure_theory set filter

open_locale nnreal ennreal big_operators topological_space

lemma forall_interval_ge_of_endpoints {α : Type} [linear_order α] {a b c x : α}
  (hab : a ≤ b) (hac : a ≤ c) (hx : x ∈ interval b c) : a ≤ x :=
begin
  rcases le_total b c with h|h;
  simp [h] at hx;
  rcases hx with ⟨hx, _⟩;
  [exact hab.trans hx, exact hac.trans hx]
end

variables {f : ℝ → ℝ} (hpos : 0 ≤ᵐ[volume.restrict (Ici 0)] f)
          (hmono : ∀ ⦃x y⦄, 0 ≤ x → x ≤ y → f y ≤ f x)

include hmono

private lemma f_integrable {n : ℕ} : interval_integrable f volume n (n+1) :=
interval_integrable_of_antimono_on
  (λ x y hx hy, hmono $ forall_interval_ge_of_endpoints n.cast_nonneg
    (n.cast_nonneg.trans (le_add_of_nonneg_right zero_le_one)) hx)

lemma integral_le (n : ℕ) : ∫ (x : ℝ) in n..(n+1), f x ≤ f n :=
calc ∫ (x : ℝ) in n..(n+1), f x
      ≤ ∫ (x : ℝ) in n..(n+1), f n : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        (f_integrable hmono)
        (continuous_const.interval_integrable _ _)
        (λ x hx, hmono n.cast_nonneg hx.1)
  ... = f n : by simp

lemma le_integral (n : ℕ) : f (n + 1) ≤ ∫ (x : ℝ) in n..(n+1), f x :=
calc f (n+1)
      = ∫ (x : ℝ) in n..(n+1), f (n+1) : by simp
  ... ≤ ∫ (x : ℝ) in n..(n+1), f x : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        (continuous_const.interval_integrable _ _)
        (f_integrable hmono)
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
  exact f_integrable hmono
end

lemma integral_le_tsum (n : ℕ) : ∫ (x : ℝ) in 0..n, f x ≤ ∑' k, f k :=
begin
  have : ∑ (k : ℕ) in finset.range n, ∫ (x : ℝ) in k..↑(k+1), f x
          ≤ ∑ (k : ℕ) in finset.range n, f k :=
    finset.sum_le_sum (λ (k : ℕ) (hk : k ∈ finset.range n), integral_le hmono k),
  rwa interval_integral.sum_integral_adjacent_intervals at this,
  intros k hk,
  exact f_integrable hmono
end

include hpos

theorem goal : summable (λ (n : ℕ), f n) ↔ integrable_on f (Ici 0) :=
begin
  split; intro h,
  { refine integrable_on.congr_set_ae _ Ioi_ae_eq_Ici.symm,
    refine integrable_on_Ioi_of_interval_integral_norm_tendsto
      at_top_countably_generated_of_archimedean _
      (ae_measurable_restrict_of_antimono_on measurable_set_Ioi (λ x y hx hy, hmono $ le_of_lt hx))
      (∑' n : ℕ, f n) sorry tendsto_coe_nat_at_top_at_top _, },
  {  }
end
