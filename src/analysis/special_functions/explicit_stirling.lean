import data.nat.choose.bounds
import data.nat.choose.central
import data.nat.choose.cast
import analysis.special_functions.stirling
import analysis.special_functions.exponential
import topology.metric_space.cau_seq_filter

noncomputable theory

open_locale topology real nat
open finset filter nat real

lemma central_binom_ratio {α : Type*} [field α] [char_zero α] (n : ℕ) :
  (central_binom (n + 1) : α) / central_binom n = 4 * ((n + 1 / 2) / (n + 1)) :=
begin
  rw [mul_div_assoc', mul_add, eq_div_iff, ←cast_add_one, div_mul_eq_mul_div, mul_comm, ←cast_mul,
    succ_mul_central_binom_succ, cast_mul, mul_div_cancel],
  { rw [mul_add_one, ←mul_assoc, cast_add, cast_mul],
    norm_num1,
    refl },
  { rw nat.cast_ne_zero,
    exact (central_binom_ne_zero _) },
  exact nat.cast_add_one_ne_zero _,
end

lemma upper_monotone_aux (n : ℕ) :
  ((n : ℝ) + 1 / 2) / (n + 1) ≤ sqrt (n + 1 / 3) / sqrt ((n + 1) + 1 / 3) :=
begin
  rw [←real.sqrt_div],
  refine real.le_sqrt_of_sq_le _,
  rw [div_pow, div_le_div_iff],
  { ring_nf,
    rw [add_le_add_iff_right],
    refine mul_le_mul_of_nonneg_right _ (by positivity),
    rw [add_le_add_iff_left],
    norm_num1 },
  all_goals { positivity },
end

lemma lower_monotone_aux (n : ℕ) :
  real.sqrt (n + 1 / 4) / real.sqrt ((n + 1) + 1 / 4) ≤ (n + 1 / 2) / (n + 1) :=
begin
  rw [←real.sqrt_div, sqrt_le_left, div_pow, div_le_div_iff],
  { ring_nf,
    rw add_le_add_iff_left,
    norm_num1 },
  all_goals { positivity },
end

def central_binomial_lower (n : ℕ) : ℝ := central_binom n * sqrt (n + 1 / 4) / 4 ^ n

lemma central_binomial_lower_monotone : monotone central_binomial_lower :=
begin
  refine monotone_nat_of_le_succ _,
  intro n,
  rw [central_binomial_lower, central_binomial_lower, pow_succ, ←div_div],
  refine div_le_div_of_le (by positivity) _,
  rw [le_div_iff, mul_assoc, mul_comm, ←div_le_div_iff, central_binom_ratio, mul_comm,
    mul_div_assoc, nat.cast_add_one],
  refine mul_le_mul_of_nonneg_left (lower_monotone_aux n) (by positivity),
  { positivity },
  { rw nat.cast_pos,
    exact central_binom_pos _ },
  { positivity }
end

def central_binomial_upper (n : ℕ) : ℝ := central_binom n * sqrt (n + 1 / 3) / 4 ^ n

lemma central_binomial_upper_monotone : antitone central_binomial_upper :=
begin
  refine antitone_nat_of_succ_le _,
  intro n,
  rw [central_binomial_upper, central_binomial_upper, pow_succ, ←div_div],
  refine div_le_div_of_le (by positivity) _,
  rw [div_le_iff, mul_assoc, mul_comm _ (_ * _), ←div_le_div_iff, mul_comm, mul_div_assoc,
    central_binom_ratio, nat.cast_add_one],
  refine mul_le_mul_of_nonneg_left (upper_monotone_aux _) (by positivity),
  { rw nat.cast_pos,
    exact central_binom_pos _ },
  { positivity },
  { positivity },
end

lemma central_binom_limit :
  tendsto (λ n, (central_binom n : ℝ) * sqrt n / 4 ^ n) at_top (𝓝 (sqrt π)⁻¹) :=
begin
  have := real.pi_pos,
  have : (sqrt π)⁻¹ = sqrt π / sqrt π ^ 2,
  { rw [inv_eq_one_div, sq, ←div_div, div_self], positivity },
  rw this,
  have : tendsto (λ n, stirling.stirling_seq (2 * n)) at_top (𝓝 (sqrt π)),
  { refine tendsto.comp stirling.tendsto_stirling_seq_sqrt_pi _,
    exact tendsto_id.const_mul_at_top' two_pos },
  refine (this.div (stirling.tendsto_stirling_seq_sqrt_pi.pow 2) (by positivity)).congr' _,
  filter_upwards [eventually_gt_at_top (0 : ℕ)] with n hn,
  dsimp,
  rw [stirling.stirling_seq, stirling.stirling_seq, central_binom, two_mul n, cast_add_choose,
    ←two_mul, nat.cast_mul, nat.cast_two, ←mul_assoc, sqrt_mul' _ (nat.cast_nonneg _),
    sqrt_mul_self, div_mul_eq_mul_div, div_div, mul_div_assoc, mul_pow, div_pow (n! : ℝ),
    mul_pow, pow_mul, ←pow_mul (_ / _), mul_comm n, sq_sqrt, mul_div_assoc', ←mul_assoc,
    mul_right_comm, mul_div_mul_right, mul_assoc, mul_comm (_ * _), ←div_div_eq_mul_div,
    mul_div_mul_left, div_sqrt, div_div_eq_mul_div, div_div, sq, sq, mul_comm _ (_ * _),
    ←bit0_eq_two_mul (2 : ℝ)],
  all_goals { positivity },
end

lemma central_binomial_upper_limit :
  tendsto central_binomial_upper at_top (𝓝 (sqrt π)⁻¹) :=
begin
  have : (sqrt π)⁻¹ = (sqrt π)⁻¹ / sqrt 1,
  { rw [real.sqrt_one, div_one] },
  have h : real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one,
  rw this,
  refine (central_binom_limit.div (tendsto_coe_nat_div_add_at_top (1 / 3 : ℝ)).sqrt h).congr' _,
  filter_upwards [eventually_gt_at_top 0] with n hn,
  dsimp,
  rw [sqrt_div, central_binomial_upper, div_div, mul_div_assoc', div_div_eq_mul_div, mul_right_comm,
    mul_div_mul_right],
  { positivity },
  { positivity },
end

lemma central_binomial_lower_limit :
  tendsto central_binomial_lower at_top (𝓝 (sqrt π)⁻¹) :=
begin
  have : (sqrt π)⁻¹ = (sqrt π)⁻¹ / sqrt 1,
  { rw [real.sqrt_one, div_one] },
  have h : real.sqrt 1 ≠ 0 := sqrt_ne_zero'.2 zero_lt_one,
  rw this,
  refine (central_binom_limit.div (tendsto_coe_nat_div_add_at_top (1 / 4 : ℝ)).sqrt h).congr' _,
  filter_upwards [eventually_gt_at_top 0] with n hn,
  dsimp,
  rw [sqrt_div, central_binomial_lower, div_div, mul_div_assoc', div_div_eq_mul_div, mul_right_comm,
    mul_div_mul_right],
  { positivity },
  { positivity },
end

lemma central_binomial_upper_bound (n : ℕ) :
  (n.central_binom : ℝ) ≤ 4 ^ n / sqrt (π * (n + 1 / 4)) :=
begin
  have := pi_pos,
  have := central_binomial_lower_monotone.ge_of_tendsto central_binomial_lower_limit n,
  rwa [sqrt_mul, ←div_div, le_div_iff, div_eq_mul_one_div (4 ^ n : ℝ), ←div_le_iff',
    one_div (sqrt π)],
  all_goals { positivity },
end

lemma central_binomial_lower_bound (n : ℕ) :
  4 ^ n / sqrt (π * (n + 1 / 3)) ≤ n.central_binom :=
begin
  have := pi_pos,
  have := central_binomial_upper_monotone.le_of_tendsto central_binomial_upper_limit n,
  rwa [sqrt_mul, ←div_div, div_le_iff, div_eq_mul_one_div, ←le_div_iff', one_div (sqrt π)],
  all_goals { positivity },
end

lemma cexp_eq_tsum {x : ℂ} : complex.exp x = ∑' i, x ^ i / i! :=
by rw [complex.exp_eq_exp_ℂ, exp_eq_tsum_div]

lemma rexp_eq_tsum {x : ℝ} : real.exp x = ∑' i, x ^ i / i! :=
by rw [exp_eq_exp_ℝ, exp_eq_tsum_div]

lemma exp_factorial_bound {n : ℕ} : (n : ℝ) ^ n / n! ≤ exp n :=
begin
  rw rexp_eq_tsum,
  refine (sum_le_tsum {n} _ (real.summable_pow_div_factorial _)).trans' _,
  { intros x hx,
    positivity },
  rw sum_singleton
end

lemma exp_factorial_bound_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : ℝ) ^ n / n! < exp n :=
begin
  rw rexp_eq_tsum,
  refine (sum_le_tsum {n, 0} _ (real.summable_pow_div_factorial _)).trans_lt' _,
  { intros x hx,
    positivity },
  rw [sum_pair hn],
  simp,
end

lemma factorial_bound_exp {n : ℕ} : ((n : ℝ) / real.exp 1) ^ n ≤ n! :=
begin
  rw [div_pow, ←rpow_nat_cast (exp 1), exp_one_rpow, div_le_iff, ←div_le_iff'],
  { exact exp_factorial_bound },
  { positivity },
  { positivity },
end

lemma factorial_bound_exp_of_ne_zero {n : ℕ} (hn : n ≠ 0) : ((n : ℝ) / real.exp 1) ^ n < n! :=
begin
  rw [div_pow, ←rpow_nat_cast (exp 1), exp_one_rpow, div_lt_iff, ←div_lt_iff'],
  { exact exp_factorial_bound_of_ne_zero hn },
  { positivity },
  { positivity },
end

lemma choose_upper_bound {n t : ℕ} : (n.choose t : ℝ) ≤ ((exp 1 * n) / t) ^ t :=
begin
  cases nat.eq_zero_or_pos t,
  { simp [h] },
  refine (nat.choose_le_pow t n).trans _,
  refine (div_le_div_of_le_left _ _ factorial_bound_exp).trans _,
  { positivity },
  { positivity },
  rw [←div_pow, div_div_eq_mul_div, mul_comm],
end

lemma choose_upper_bound_of_pos {n t : ℕ} (hn : n ≠ 0) (ht : t ≠ 0) :
  (n.choose t : ℝ) < ((exp 1 * n) / t) ^ t :=
begin
  refine (nat.choose_le_pow t n).trans_lt _,
  refine (div_lt_div_of_lt_left _ _ (factorial_bound_exp_of_ne_zero ht)).trans_eq _,
  { positivity },
  { positivity },
  rw [←div_pow, div_div_eq_mul_div, mul_comm],
end

lemma choose_upper_bound' {n t : ℕ} : (n.choose t : ℝ) ≤ exp t * (n / t) ^ t :=
choose_upper_bound.trans_eq $ by rw [mul_div_assoc, mul_pow, ←exp_one_rpow t, rpow_nat_cast]

-- example {a b c : ℕ → ℝ} {L : ℝ} (ha : monotone a) (hb : tendsto b at_top (𝓝 L)) (hc : antitone c)
--   (hab : tendsto (λ x, a x / b x) at_top (𝓝 1))
--   (hbc : tendsto (λ x, b x / c x) at_top (𝓝 1))
--   (ha_pos : ∀ n, 0 < a n) (hb_pos : ∀ n, 0 < b n) (hc_pos : ∀ n, 0 < c n) :
--   ∀ n, a n ≤ b n ∧ b n ≤ c n :=
-- begin

-- end
