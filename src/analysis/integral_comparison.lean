/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import measure_theory.integral_eq_improper

/-!
TODO
-/

open measure_theory set filter finset

open_locale nnreal ennreal big_operators topological_space

lemma forall_interval_ge_of_endpoints {α : Type*} [linear_order α] {a b c x : α}
  (hab : a ≤ b) (hac : a ≤ c) (hx : x ∈ interval b c) : a ≤ x :=
begin
  rcases le_total b c with h|h;
  simp [h] at hx;
  rcases hx with ⟨hx, _⟩;
  [exact hab.trans hx, exact hac.trans hx]
end


lemma interval_integral.integral_mono_bounds {α : Type*} [linear_order α] [topological_space α]
  [order_closed_topology α] [measurable_space α] [opens_measurable_space α]
  {a a' b b' : α} {f : α → ℝ} {μ : measure α} (haa' : a' ≤ a) (hbb' : b ≤ b')
  (hint : interval_integrable f μ a b) (hint' : interval_integrable f μ a' b') (hf : 0 ≤ f) :
  ∫ x in a..b, f x ∂μ ≤ ∫ x in a'..b', f x ∂μ :=
have hinta : interval_integrable f μ a a',
  begin
    rw interval_integrable_iff at *,
    refine (hint.union hint').mono_set (λ x, _),
    rw [max_eq_left haa', min_eq_right haa'],
    rintro ⟨hxa', hxa⟩,
    rcases le_or_gt x b' with hxb'|hxb',
    { right,
      rw [max_eq_right (hxa'.le.trans hxb'), min_eq_left (hxa'.le.trans hxb')],
      exact ⟨hxa', hxb'⟩ },
    { left,
      have := hbb'.trans_lt hxb',
      rw [max_eq_left (this.le.trans hxa), min_eq_right (this.le.trans hxa)],
      exact ⟨this, hxa⟩ }
  end,
have hintb : interval_integrable f μ b b',
  from hint.symm.trans (hinta.trans hint'),
calc  ∫ x in a..b, f x ∂μ
    ≤ ∫ x in a..b, f x ∂μ + ∫ x in b..b', f x ∂μ :
        le_add_of_nonneg_right (interval_integral.integral_nonneg hbb' (λ x _, hf x))
... = ∫ x in a..b', f x ∂μ : interval_integral.integral_add_adjacent_intervals hint hintb
... ≤ ∫ x in a'..a, f x ∂μ + ∫ x in a..b', f x ∂μ :
        le_add_of_nonneg_left (interval_integral.integral_nonneg haa' (λ x _, hf x))
... = ∫ x in a'..b', f x ∂μ : interval_integral.integral_add_adjacent_intervals hinta.symm
        (hinta.trans hint')


variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E]
          {μ : measure E} {f : ℝ → E}
          (hmono : ∀ ⦃x y⦄, 0 ≤ x → x ≤ y → ∥f y∥ ≤ ∥f x∥)

include hmono

private lemma f_integrable {n : ℕ} : interval_integrable (λ x, ∥f x∥) volume n (n+1) :=
interval_integrable_of_antimono_on
  (λ x y hx hy, hmono $ forall_interval_ge_of_endpoints n.cast_nonneg
    (n.cast_nonneg.trans (le_add_of_nonneg_right zero_le_one)) hx)

lemma integral_le (n : ℕ) : ∫ (x : ℝ) in n..(n+1), ∥f x∥ ≤ ∥f n∥ :=
calc ∫ (x : ℝ) in n..(n+1), ∥f x∥
      ≤ ∫ (x : ℝ) in n..(n+1), ∥f n∥ : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        (f_integrable hmono)
        (continuous_const.interval_integrable _ _)
        (λ x hx, hmono n.cast_nonneg hx.1)
  ... = ∥f n∥ : by simp

lemma le_integral (n : ℕ) : ∥f (n + 1)∥ ≤ ∫ (x : ℝ) in n..(n+1), ∥f x∥ :=
calc ∥f (n+1)∥
      = ∫ (x : ℝ) in n..(n+1), ∥f (n+1)∥ : by simp
  ... ≤ ∫ (x : ℝ) in n..(n+1), ∥f x∥ : interval_integral.integral_mono_on
        (le_add_of_nonneg_right zero_le_one)
        (continuous_const.interval_integrable _ _)
        (f_integrable hmono)
        (λ x hx, hmono (n.cast_nonneg.trans hx.1) hx.2)

--lemma le_integral' (n : ℕ) (h : n ≠ 0) : ∥f n∥ ≤ ∫ (x : ℝ) in (n-1)..n, ∥f x∥ :=
--begin
--  rcases nat.exists_eq_succ_of_ne_zero h with ⟨k, rfl⟩,
--  rw [nat.cast_succ, add_sub_cancel],
--  exact le_integral hmono k,
--end

--lemma integral_le_sum (n : ℕ) : ∫ (x : ℝ) in 0..n, ∥f x∥ ≤ ∑ (k : ℕ) in range n, ∥f k∥ :=
--begin
--  have : ∑ (k : ℕ) in range n, ∫ (x : ℝ) in k..↑(k+1), ∥f x∥
--          ≤ ∑ (k : ℕ) in range n, ∥f k∥ :=
--    sum_le_sum (λ (k : ℕ) (hk : k ∈ range n), integral_le hmono k),
--  rwa interval_integral.sum_integral_adjacent_intervals at this,
--  intros k hk,
--  exact f_integrable hmono
--end

lemma integral_le_tsum (hsum : summable (λ n : ℕ, ∥f n∥)) (n : ℕ) :
  ∫ (x : ℝ) in 0..n, ∥f x∥ ≤ ∑' (k : ℕ), ∥f k∥ :=
calc  ∫ (x : ℝ) in 0..n, ∥f x∥
    = ∑ k in range n, ∫ (x : ℝ) in k..↑(k+1), ∥f x∥ :
        begin
          rw [interval_integral.sum_integral_adjacent_intervals, nat.cast_zero],
          exact (λ k hk, f_integrable hmono)
        end
... ≤ ∑ k in range n, ∥f k∥ :
        sum_le_sum (λ (k : ℕ) (hk : k ∈ range n), integral_le hmono k)
... ≤ ∑' (k : ℕ), ∥f k∥ : sum_le_tsum _ (λ n hn, norm_nonneg _) hsum

lemma sum_le_integral [opens_measurable_space E] (hint : integrable_on f (Ici 0)) (n : ℕ) :
  ∑ k in range n, ∥f k∥ ≤ (∫ x in Ici 0, ∥f x∥) + ∥f 0∥ :=
match n with
| 0 :=
  begin
    rw [range_zero, sum_empty],
    exact add_nonneg (integral_nonneg $ λ _, norm_nonneg _) (norm_nonneg _)
  end
| (n+1) :=
  calc  ∑ k in range (n+1), ∥f k∥
      = ∑ k in range n, ∥f (k+1)∥ + ∥f 0∥ : sum_range_succ' _ _
  ... ≤ (∑ k in range n, ∫ (x : ℝ) in k..↑(k+1), ∥f x∥) + ∥f 0∥ :
          add_le_add_right (sum_le_sum $ λ k hk, le_integral hmono k) _
  ... = (∫ (x : ℝ) in 0..n, ∥f x∥) + ∥f 0∥ :
          begin
            rw [interval_integral.sum_integral_adjacent_intervals, nat.cast_zero],
            exact (λ k hk, f_integrable hmono)
          end
  ... = (∫ (x : ℝ) in (Ioc 0 n : set ℝ), ∥f x∥) + ∥f 0∥ :
          by {rw interval_integral.integral_of_le, exact n.cast_nonneg}
  ... ≤ (∫ (x : ℝ) in Ici 0, ∥f x∥) + ∥f 0∥ :
          add_le_add_right (set_integral_mono_set hint.norm (ae_of_all _ (λ _, norm_nonneg _))
            (ae_of_all _ (λ x ⟨h, _⟩, h.le))) _
end

#check ae_measurable_restrict_of_antimono_on

theorem goal [borel_space E] (hf : ae_measurable f (volume.restrict $ Ici 0)) :
  summable (λ (n : ℕ), ∥f n∥) ↔ integrable_on f (Ici 0) :=
begin
  split; intro h,
  { rw [integrable_on, ← integrable_norm_iff hf, ← integrable_on],
    refine integrable_on.congr_set_ae _ Ioi_ae_eq_Ici.symm,
    refine integrable_on_Ioi_of_interval_integral_norm_tendsto
      at_top_countably_generated_of_archimedean _
      (ae_measurable_restrict_of_antimono_on measurable_set_Ioi (λ x y hx hy, hmono $ le_of_lt hx))
      (⨆ (n : ℕ), ∫ (x : ℝ) in 0..n, ∥f x∥) sorry tendsto_coe_nat_at_top_at_top _,
    simp_rw norm_norm,
    refine tendsto_at_top_csupr
      (λ i j hij, interval_integral.integral_mono_bounds
        (le_refl (0 : ℝ)) (nat.cast_le.mpr hij) sorry sorry (λ x, norm_nonneg _))
      ⟨∑' (k : ℕ), ∥f k∥, forall_range_iff.mpr (integral_le_tsum hmono h)⟩ },
  { exact summable_of_sum_range_le (λ n, norm_nonneg _) (sum_le_integral hmono h) }
end
