import measure_theory.measure.lebesgue
import number_theory.liouville.residual
import number_theory.liouville.liouville_with

/-!
-/

open_locale filter big_operators ennreal
open filter set metric measure_theory

lemma volume_set_of_frequently_lt_rpow {r : ℝ} (hr : r < -2) :
  volume {x : ℝ | ∃ᶠ b : ℕ in at_top, ∃ a : ℤ, x ≠ a / b ∧ |x - a / b| < b ^ r} = 0 :=
begin
  suffices H : ∀ m : ℕ, volume {x : ℝ | ∃ᶠ b : ℕ in at_top, ∃ a : ℤ, x ≠ a / b ∧
    |x - a / b| < b ^ r ∧ x ∈ Icc (-m : ℝ) m} = 0,
  { have A : (⋃ m : ℕ, Icc (-m : ℝ) m) = univ,
      by simpa [real.closed_ball_eq] using Union_closed_ball_nat (0 : ℝ),
    simpa only [← measure_Union_null_iff, frequently_and_distrib_right, exists_and_distrib_left,
      ← and_assoc, exists_and_distrib_right, set_of_and, ← inter_Union, A, inter_univ,
      set_of_mem_eq] using H },
  rw ← map_add_at_top_eq_nat 1, simp only [frequently_map],
  refine λ m, measure_set_of_frequently_eq_zero (ne_of_lt _),
  suffices H : ∀ b : ℕ, {x : ℝ | ∃ a : ℤ, x ≠ a / b ∧ |x - a / b| < b ^ r ∧ x ∈ Icc (-m : ℝ) m} ⊆
    ⋃ a ∈ finset.Icc (-(m * b) : ℤ) (m * b), ball (a / b : ℝ) (b ^ r),
  { calc ∑' b : ℕ, volume {x : ℝ | ∃ a : ℤ, x ≠ a / ↑(b + 1) ∧ |x - a / ↑(b + 1)| < ↑(b + 1) ^ r ∧
      x ∈ Icc (-m : ℝ) m}
        ≤ ∑' b : ℕ, volume (⋃ a ∈ finset.Icc (-(m * ↑(b + 1)) : ℤ) (m * ↑(b + 1)),
            ball (a / ↑(b + 1) : ℝ) (↑(b + 1) ^ r)) :
      ennreal.tsum_le_tsum (λ b, measure_mono $ H (b + 1))
    ... ≤ ∑' b : ℕ, ∑ a in finset.Icc (-(m * ↑(b + 1)) : ℤ) (m * ↑(b + 1)),
            volume (ball (a / ↑(b + 1) : ℝ) (↑(b + 1) ^ r)) :
      ennreal.tsum_le_tsum (λ b, measure_bUnion_finset_le _ _)
    ... < ∞ : ne.lt_top _,
    simp
 }
  
end
/-lemma volume_liouville : volume {x | liouville x} = 0 :=
begin
  suffices : volume ({x | liouville x} ∩ Ico 0 1) = 0,
  { rw [← liouville.Union_image_inter_Ico_01, measure_Union_null_iff],
    intro n,
    rwa [image_add_right, real.volume_preimage_add_right] },
  set S : ℕ → ℕ → set ℝ := λ n b, ⋃ a ∈ finset.range (b + 1), ball (↑a / b) (1 / b ^ n),
  have : ∀ n, {x | liouville x} ∩ Ico 0 1 ⊆ ⋃ b > 1, S (n + 1) b,
  { rintro n x ⟨hx, h₀, h₁⟩,
    rcases hx (n + 1) with ⟨a, b, hb, hne, hmem⟩,
    simp only [S, mem_Union, exists_prop, finset.mem_range, nat.lt_add_one_iff],
    lift b to ℕ using le_trans zero_le_one hb.le, norm_cast at hb,
    have hb₀ : (0 : ℝ) < b := nat.cast_pos.2 (zero_lt_one.trans hb),
    have hpow : 1 / (b ^ (n + 1) : ℝ) ≤ 1 / b,
      by simpa only [pow_one] using (one_div_le_one_div (pow_pos hb₀ _) (pow_pos hb₀ 1)).2
        (pow_le_pow (by exact_mod_cast hb.le) n.succ_pos),
    have ha : 0 ≤ a,
    { contrapose! hmem,
      rw [← int.add_one_le_iff, ← le_neg_iff_add_nonpos_right] at hmem,
      calc 1 / (b ^ (n + 1) : ℝ) ≤ 1 / b : hpow
      ... ≤ - (a / b) :
        begin
          rw ← neg_div,
          refine div_le_div_of_le hb₀.le _,
          rw le_neg, exact_mod_cast hmem
        end
      ... ≤ x - a / b : by simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, h₀]
      ... ≤ |x - a / b| : le_abs_self _ },
    lift a to ℕ using ha,
    refine ⟨b, hb, a, _, hmem⟩,
    contrapose! hmem, rw abs_sub_comm, rw [← nat.add_one_le_iff] at hmem,
    calc 1 / (b ^ (n + 1) : ℝ) ≤ 1 / b : hpow
    ... = (b + 1) / b - b / b : by rw [← sub_div, add_sub_cancel']
    ... = (b + 1) / b - 1 : by rw [div_self hb₀.ne']
    ... ≤ a / b - x : sub_le_sub (div_le_div_of_le hb₀.le $ by exact_mod_cast hmem) h₁.le
    ... ≤ |a / b - x| : le_abs_self _ },
  have : ∀ n (b > 1), volume (S n b) ≤ (b + 1) * (2 / b ^ n),
  { intros n b hb,
    refine (measure_bUnion_finset_le _ _).trans_eq _,
    have : (0 : ℝ) < b, by exact_mod_cast zero_lt_one.trans hb,
    simp [← div_eq_mul_inv, ennreal.of_real_div_of_pos (pow_pos this n),
      ennreal.of_real_pow this.le] },
  
end-/
