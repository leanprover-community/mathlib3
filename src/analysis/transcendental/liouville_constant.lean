import analysis.transcendental.liouville
import data.nat.factorial

namespace is_liouville

noncomputable theory
open_locale nat big_operators
open set real finset

variable (m : ℕ)

local notation `α` := ∑' (i : ℕ), 1 / (m : ℝ) ^ i!
local notation `α_first` k `terms` :=  ∑ i in range (k+1), 1 / (m : ℝ) ^ i!
local notation `α_terms_after` k := ∑' i, 1 / (m : ℝ) ^ (i + (k+1))!

lemma summable_inv_pow_fact {hm : 2 < m} : summable (λ i, 1 / (m : ℝ) ^ i!) :=
begin
  apply @summable_of_nonneg_of_le _ (λ n, (1 / m : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, norm_num },
  { intro b, dsimp only [],
    rw [one_div, div_pow, one_pow, one_div, inv_le_inv],
    { apply pow_le_pow _ (nat.self_le_factorial b),
      norm_num, linarith },
    repeat { apply pow_pos, norm_num, linarith } },
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg,
    { rw div_lt_one (by {norm_num, linarith} : 0 < (m : ℝ)), norm_num, linarith },
    { rw one_div_nonneg, norm_num } }
end

lemma summable_inv_pow_n_add_fact {hm : 2 < m} : ∀ n : ℕ, summable (λ i, 1 / (m : ℝ) ^ (i + (n + 1))!) :=
λ n, begin
  apply @summable_of_nonneg_of_le _ (λ n, (1 / m : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, norm_num },
  { intro b, dsimp only [],
    rw [one_div, div_pow, one_pow, one_div, inv_le_inv],
    apply pow_le_pow,
    repeat { apply pow_pos <|> norm_num <|> linarith },
    transitivity b!,
    { exact nat.self_le_factorial _ },
    { exact nat.factorial_le (nat.le.intro rfl) }},
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg,
    { rw div_lt_one (by {norm_num, linarith} : 0 < (m : ℝ)), norm_num, linarith },
    { rw one_div_nonneg, norm_num } }
end

lemma rat_of_α_k {hm : 2 < m} : ∀ k, ∃ p : ℕ, α_first k terms = p / ((m : ℝ) ^ k!) :=
λ k, begin
  induction k with k h,
  { use 1,
    simp only [sum_singleton, nat.cast_one, range_one] },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    rw mul_ne_zero_iff, split,
    all_goals { refine pow_ne_zero _ _, norm_num, linarith } }
end

lemma α_terms_after_pos {hm : 2 < m} : ∀ k, 0 < α_terms_after k := λ n,
calc 0 < 1 / (m : ℝ) ^ (n + 1)! : by { rw one_div_pos, apply pow_pos, norm_num, linarith }
  ... = 1 / (m : ℝ) ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / (m : ℝ) ^ (i + (n + 1))! :
      begin
        refine le_tsum (@summable_inv_pow_n_add_fact _ hm _) 0 (λ _ _, _),
        rw one_div_nonneg, apply pow_nonneg, norm_num
      end

lemma α_eq_first_k_terms_add_rest {hm : 2 < m} : ∀ k, α = α_first k terms + α_terms_after k :=
λ k, (sum_add_tsum_nat_add _ (@summable_inv_pow_fact m hm)).symm

theorem is_liouville_of_α {hm : 2 < m} : is_liouville α :=
begin
  intro n,
  have h_truncation_wd := α_eq_first_k_terms_add_rest m n,
  rcases @rat_of_α_k _ hm n with ⟨p, hp⟩,
  use [p, m ^ n!],
  rw hp at h_truncation_wd,
  push_cast,
  rw [h_truncation_wd, add_sub_cancel', abs_of_pos (α_terms_after_pos _ _)],
  repeat { split },
  { apply one_lt_pow, norm_num, linarith, exact nat.factorial_pos _ },
  { exact @α_terms_after_pos _ hm _ },
  { exact calc (∑' i, 1 / (m : ℝ) ^ (i + (n + 1))!)
      ≤ ∑' i, 1 / (m : ℝ) ^ (i + (n + 1)!) :
      begin
        refine tsum_le_tsum (λ b, _) (summable_inv_pow_n_add_fact _ _)
          (summable_of_nonneg_of_le (λ b, _) (λ b, _) (@summable_geometric_of_abs_lt_1 (1 / m : ℝ)
            (show abs (1 / m : ℝ) < 1,
             by { rw [abs_of_pos (show 0 < 1/(m:ℝ), by {rw one_div_pos, norm_num, linarith}),
                      one_div_lt, one_div_one]; norm_num; linarith }))),
        { rw one_div_le_one_div,
          { apply pow_le_pow,
            { norm_num, linarith },
            { exact nat.add_factorial_le_factorial_add _ _ (nat.succ_ne_zero _) }},
          repeat { apply pow_pos, norm_num, linarith }},
        { exact hm },
        { rw one_div_nonneg, apply pow_nonneg, norm_num },
        { rw [div_pow, one_pow, one_div_le_one_div],
          apply pow_le_pow,
          repeat { exact nat.le.intro rfl <|> linarith <|> apply pow_pos <|>
            apply pow_nonneg <|> norm_num <|> linarith <|> rw le_add_iff_nonneg_right }}
      end
  ... = ∑' i, (1 / m : ℝ) ^ i * (1 / m ^ (n + 1)!) :
      by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
  ... = (∑' i, (1 / m : ℝ) ^ i) * (1 / m ^ (n + 1)!) :
      begin
        rw tsum_mul_right,
        apply summable_geometric_of_abs_lt_1,
        rw [abs_of_nonneg (show 0 ≤ 1/(m:ℝ), by {rw one_div_nonneg, norm_num}), one_div_lt, one_div_one];
        norm_num; linarith
      end
  ... = m / (m-1) * (1 / m ^ (n + 1)!) :
      begin
        congr,
        rw [tsum_geometric_of_abs_lt_1, show (m/(m-1):ℝ) = ((m-1)/(m:ℝ))⁻¹,
          by rw inv_div, sub_div, div_self],
        repeat { rw [abs_of_nonneg] <|> norm_num <|> linarith  <|> rw one_div_nonneg <|> rw one_div_lt},
      end
  ... < 2 * (1 / m ^ (n + 1)!) :
      by { apply mul_lt_mul,
        rw [div_lt_iff, mul_sub, mul_one, lt_sub_iff_add_lt, two_mul, real.add_lt_add_iff_left],
        norm_cast,
        repeat { rw one_div_le_one_div <|> rw one_div_pos <|>
          apply pow_pos <|> apply pow_nonneg <|> norm_num <|> linarith }}
  ... = 2 / m ^ (n + 1)! : by field_simp
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / m ^ (n! * n) :
      begin
        rw [div_lt_div_iff, one_mul],
        conv_rhs {rw mul_add, rw pow_add, rw mul_one, rw pow_mul, rw mul_comm},
        apply mul_lt_mul;
        norm_cast,
        { refine lt_of_lt_of_le hm _,
          conv_lhs { rw show m = m ^ 1, by rw pow_one },
          apply pow_le_pow (show 1 ≤ m, by linarith) (nat.factorial_pos _), },
        repeat { norm_cast <|> linarith <|> apply pow_pos <|> apply pow_nonneg <|> rw pow_mul },
      end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul },
  exact hm, exact hm
end

lemma is_transcendental_of_α {hm : 2 < m} : is_transcendental ℤ α :=
  real.is_liouville.transcendental_of_is_liouville (@is_liouville_of_α _ hm)

end is_liouville
