/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import data.nat.factorial
import data.real.irrational
import ring_theory.algebraic
import algebra.big_operators
import data.polynomial.degree
import data.set.intervals.infinite
import topology.algebra.polynomial
import analysis.calculus.mean_value
import analysis.real.polynomial

/-!
# Liouville's theorem

This file contains the proof of Liouville's theorem stating that all Liouville numbers are
transcendental.
-/

open_locale big_operators
open polynomial real set finset

namespace real

/--
A Liouville number `x` is a number such that for every natural number `n`, there exists `a, b ∈ ℤ`
such that `0 < |x - a/b| < 1/bⁿ`. We can assume without loss of generality that `1 < b`.
-/
def is_liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ 0 < abs (x - a / b) ∧ abs (x - a / b) < 1 / b ^ n

namespace is_liouville

lemma not_liouville_zero : ¬ is_liouville 0 :=
begin
  classical,
  intro h,
  rcases h 1 with ⟨a, b, h_b_gt_1, h_abs_sub_pos, h_abs_sub_small⟩,
  simp only [one_div, zero_sub, abs_neg, pow_one] at h_abs_sub_pos h_abs_sub_small,
  set a' := abs a,
  have h_a'_ineq : 0 ≤ a' := abs_nonneg _,
  have : abs (a' / b : ℝ) = abs (a / b), { simp only [int.cast_abs, abs_div, abs_abs] },
  rw ← this at h_abs_sub_pos h_abs_sub_small,
  rw [abs_of_nonneg, inv_eq_one_div, div_lt_div_iff, one_mul, mul_lt_iff_lt_one_left]
    at h_abs_sub_small,
  { norm_cast at h_abs_sub_small,
    rw [(by linarith : a' = 0), int.cast_zero, zero_div, abs_zero] at h_abs_sub_pos,
    revert h_abs_sub_pos, simp only [forall_prop_of_false, not_lt] },
  repeat { apply div_nonneg <|> norm_cast <|> linarith <|> assumption }
end

lemma abs_eval_rat_ge_one_div_denom_pow_n (f : polynomial ℤ) (a b : ℤ)
  (h_b_pos : 0 < b) (h_not_root : (f.map (algebra_map ℤ ℝ)).eval (a / b) ≠ 0) :
  1 / (b : ℝ) ^ f.nat_degree ≤ abs ((f.map (algebra_map ℤ ℝ)).eval (a / b)) :=
begin
  have h_b0 : (b : ℝ) ≠ 0, { exact_mod_cast ne_of_gt h_b_pos },
  have h_pos : 0 < 1 / (b : ℝ) ^ f.nat_degree,
  { exact div_pos zero_lt_one (pow_pos (by exact_mod_cast h_b_pos) _) },
  have h_eq₁ : ((f.map (algebra_map ℤ ℝ)).eval (a / b)) =
    1 / b ^ f.nat_degree * (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)),
  { -- we give a rough outline of the calculation, and prove two obligations below
    calc  ((f.map (algebra_map ℤ ℝ)).eval (a / b))
        = ∑ i in f.support, f.coeff i * (a / b) ^ i : _ -- (1)
    ... = ∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i) / b ^ f.nat_degree :
          sum_congr rfl _ -- (2)
    ... = (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)) / b ^ f.nat_degree :
            by rw [sum_div]
    ... = 1 / b ^ f.nat_degree * (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)) :
            by ring,
    { -- proof of (1)
      conv_lhs { rw [eval_map, as_sum_support f, eval₂_finset_sum] },
      congr, funext, simp only [ring_hom.eq_int_cast, eval₂_monomial] },
    { -- proof of (2)
      intros i hi,
      suffices : (b ^ f.nat_degree : ℝ) = b ^ (f.nat_degree - i) * b ^ i,
      { field_simp [h_b0, this, mul_assoc] },
      rw [← pow_add, nat.sub_add_cancel (le_nat_degree_of_mem_support hi)] }},
  have h_cast_eq : ∑ i in f.support, (f.coeff i : ℝ) * a ^ i * b ^ (f.nat_degree - i) =
                 ↑(∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)),
  { simp only [← int.coe_cast_ring_hom, ring_hom.map_sum, ring_hom.map_mul, ring_hom.map_pow] },
  rw [h_eq₁, h_cast_eq, abs_mul, abs_of_pos h_pos, le_mul_iff_one_le_right h_pos],
  rw [h_eq₁, mul_ne_zero_iff, h_cast_eq] at h_not_root,
  norm_cast at ⊢ h_not_root,
  exact abs_pos.mpr h_not_root.2
end


lemma exists_pos_real_of_irrational_root (α : ℝ) (hα : irrational α) (f : polynomial ℤ)
  (h_f_deg : 1 < f.nat_degree) (h_α_root : (f.map (algebra_map ℤ ℝ)).eval α = 0) :
  ∃ A : ℝ, 0 < A ∧ ∀ a b : ℤ, 0 < b → (A / b ^ (f.nat_degree)) < abs(α - a / b)  :=
begin
  classical,
  set fR := f.map (algebra_map ℤ ℝ),
  have h_fR_deg : 1 < fR.nat_degree, { rwa nat_degree_map', exact int.cast_injective },
  have h_f_nonzero : fR ≠ 0 := λ h, (ne_zero_of_nat_degree_gt h_fR_deg)
    begin
      ext m, rw polynomial.ext_iff at h, specialize h m, exact h
    end,
  obtain ⟨M, ⟨h_m_pos, h_max⟩⟩ :=
    exists_forall_ge_of_polynomial_deriv α fR (nat.lt_of_succ_lt h_fR_deg),
  obtain ⟨B, ⟨hB_pos, hB_M, hB_one, hB_root⟩⟩ :=
    non_root_small_interval_of_polynomial α fR h_f_nonzero M h_m_pos,
  -- Then `B/2` satisfies all the requirement.
  use (B / 2),
  have hB₂ : 0 < B / 2 := half_pos hB_pos,
  apply and.intro hB₂,
  -- `∀ (a b : ℤ), 0 < b → B / 2 / b ^ f.nat_degree < abs (α - a/b)`
  intros a b h_b_pos, rw ← not_le, intro h_abs_lt,
  have hb : 1 ≤ b ^ f.nat_degree := pow_pos h_b_pos f.nat_degree,
  have hb₁ : abs (α - a / b) ≤ B / 2,
  { refine le_trans h_abs_lt _,
    rw [div_le_iff, le_mul_iff_one_le_right],
    repeat { norm_cast <|> assumption, assumption <|> exact pow_pos h_b_pos _ }},
  have hb₂ : abs (α - a / b) < B := lt_of_le_of_lt hb₁ (by linarith),
  have hab₁ : α ≠ a/b := (irrational_iff_ne_rational _).mp hα a b,
  have hab₂ : fR.eval (a/b) ≠ 0 := hB_root _ hb₂ hab₁.symm,
  obtain ⟨x₀, hx₀⟩ := exists_deriv_eq_slope_of_polynomial_root α fR h_α_root ((a : ℝ) / b) hab₂,
  apply lt_irrefl (B / 2 / b ^ f.nat_degree),
  calc  B / 2 / b ^ f.nat_degree
      ≥ abs (α - ↑a / ↑b) : ge_iff_le.2 h_abs_lt
  ... = abs (fR.eval (a / b) / fR.derivative.eval x₀) : by rw [hx₀.1, abs_neg]
  ... = abs (fR.eval (a / b)) / abs (fR.derivative.eval x₀) : by rw abs_div
  ... ≥ 1 / b ^ f.nat_degree / abs (fR.derivative.eval x₀) :
      begin
        rw ge_iff_le,
        exact div_le_div (abs_nonneg _)
          (abs_eval_rat_ge_one_div_denom_pow_n f a b h_b_pos hab₂)
          (abs_pos.mpr hx₀.2.1) (le_refl _)
      end
  ... ≥ 1 / b ^ f.nat_degree / M :
      begin
        rw ge_iff_le,
        refine div_le_div _ (le_refl _) (abs_pos.mpr hx₀.2.1) _,
        { rw one_div_nonneg, apply pow_nonneg, norm_cast, exact le_of_lt h_b_pos },
        { refine h_max x₀ _, rw abs_sub,
          apply le_trans (le_of_lt hx₀.2.2.1) (le_trans (le_of_lt hb₂) hB_one) }
      end
  ... = 1 / M / b ^ f.nat_degree : by ring
  ... ≥ B / b ^ f.nat_degree :
      begin
        rw ge_iff_le,
        refine div_le_div _ hB_M _ (le_refl _),
        { rw one_div_nonneg, exact le_of_lt h_m_pos },
        { apply pow_pos, norm_cast, exact h_b_pos },
      end
  ... > B / 2 / b ^ f.nat_degree :
      begin
        rw [gt_iff_lt, div_lt_div_right],
        { exact half_lt_self hB_pos },
        { apply pow_pos, norm_cast, exact h_b_pos },
      end
end

lemma irrational_of_is_liouville {x : ℝ} (h : is_liouville x) : irrational x :=
begin
  rw irrational_iff_ne_rational,
  suffices : ∀ (a b : ℤ), 0 < b → x ≠ ↑a / ↑b,
  { intros a b,
    rcases lt_trichotomy 0 b with b_gt | b_0 | b_lt,
    { exact this a b b_gt },
    { intro hrid, rw [←b_0, int.cast_zero, div_zero] at hrid,
      rw hrid at h,
      exact not_liouville_zero h },
    { specialize this (-a) (-b) (neg_pos.mpr b_lt),
      rw [int.cast_neg, int.cast_neg, neg_div_neg_eq] at this, exact this }},
  { intros a b h_b_pos h_rid,
    lift b to ℕ using le_of_lt h_b_pos,
    rw ←coe_coe at h_rid,
    norm_cast at h_b_pos,
    set n := b + 1 with hn,
    have h_b_ineq : b < 2 ^ (n-1) := nat.lt_two_pow b,
    rcases h n with ⟨p, q, h_q_gt_1, h_abs_sub_pos, h_abs_sub_small⟩,
    have h_q_pos : 0 < q := by linarith,
    lift q to ℕ using le_of_lt h_q_pos,
    rw [←coe_coe, h_rid] at *,
    norm_cast at h_q_gt_1 h_q_pos,
    rw [div_sub_div, abs_div] at h_abs_sub_pos h_abs_sub_small,
    -- We need to consider separately if `aq - bp` is zero or not
    by_cases h0 : (abs ((a:ℝ) * q - b * p) = 0),
    { rw h0 at h_abs_sub_pos h_abs_sub_small, rw zero_div at h_abs_sub_pos, linarith },
    { replace h0 : 0 < abs ((a:ℝ) * q - b * p) := lt_of_le_of_ne (abs_nonneg _) (ne.symm h0),
      have h' : 1 ≤ abs ((a:ℝ) * q - b * p),
      { norm_cast at h0 ⊢, linarith },
      rw (show abs (b * q : ℝ) = b * q,
        by { rw abs_of_nonneg, norm_cast, refine mul_nonneg bot_le bot_le }) at *,
      exact lt_irrefl _
        (calc 1
            ≤ abs ((a:ℝ) * q - b * p) : h'
        ... < (b : ℝ) * q / q ^ n :
            begin
              rw [div_lt_iff] at h_abs_sub_small,
              convert h_abs_sub_small using 1,
              { ring },
              { norm_cast, exact mul_pos h_b_pos h_q_pos }
            end
        ... = (b : ℝ) * q / q ^ (n : ℤ) : by tidy
        ... = (b : ℝ) / (q : ℝ) ^ (n - 1 : ℤ) :
            begin
              rw [div_eq_div_iff, mul_assoc,
                  show (q : ℝ) * (q : ℝ) ^ (n - 1 : ℤ) = q ^ (1 + (n - 1) : ℤ),
                      by { rw [fpow_add, fpow_one], norm_cast, linarith },
                  show (1 + (n - 1) : ℤ) = n, by ring],
              repeat {apply fpow_ne_zero, norm_cast, linarith }
            end
        ... ≤ (b : ℝ) / 2 ^ (n - 1 : ℤ) :
            begin
              rw div_le_div_iff,
              refine mul_le_mul (le_refl _) _
                (fpow_nonneg_of_nonneg (show (0 : ℝ) ≤ 2, by linarith) _)
                (show (0 : ℝ) ≤ b, by { norm_cast, exact bot_le }),
              { rw [int.coe_nat_succ, add_sub_cancel, fpow_coe_nat, fpow_coe_nat],
                apply pow_le_pow_of_le_left (show (0 : ℝ) ≤ 2, by linarith),
                norm_cast, linarith },
              repeat { apply fpow_pos_of_pos, norm_cast, assumption <|> linarith }
            end
        ... < (2 : ℝ) ^ (n - 1 : ℤ) / 2 ^ (n - 1 : ℤ) :
            begin
              rw [show (2 : ℝ) ^ (n - 1 : ℤ) = 2 ^ (n - 1 : ℕ),
                  by simp only [nat.add_succ_sub_one, add_zero, int.coe_nat_succ,
                      add_sub_cancel, fpow_coe_nat], div_lt_div_iff],
              norm_cast,
              refine mul_lt_mul h_b_ineq (le_refl _) _ _,
              repeat { apply pow_pos <|> apply pow_nonneg, linarith }
            end
        ... = 1 : by { rw div_self, apply fpow_ne_zero_of_ne_zero, linarith } ) },
    repeat { norm_cast, assumption <|> linarith }}
end

theorem transcendental_of_is_liouville {x : ℝ} (liouville_x : is_liouville x) :
  is_transcendental ℤ x :=
begin
  have h_irr_x : irrational x := irrational_of_is_liouville liouville_x,
  rintros ⟨f : polynomial ℤ, h_f_nonzero, h_root⟩,
  have h_f_deg : 1 < f.nat_degree :=
    one_lt_nat_degree_of_irrational_root x f h_irr_x h_f_nonzero h_root,
  replace h_root : (f.map (algebra_map ℤ ℝ)).eval x = 0, { rw aeval_def at h_root, rwa [eval_map] },
  obtain ⟨A, hA, h⟩ := exists_pos_real_of_irrational_root x h_irr_x f h_f_deg h_root,
  have h_pow_big_enough : ∃ (r : ℕ), 1 / A ≤ 2 ^ r,
  { rcases pow_unbounded_of_one_lt (1 / A) (lt_add_one 1) with ⟨n, hn⟩,
    exact ⟨n, le_of_lt hn⟩ },
  obtain ⟨r, hr⟩ := h_pow_big_enough,
  have hr' : 1 / (2 ^ r) ≤ A,
  { rw [div_le_iff, mul_comm, ←div_le_iff], repeat { assumption <|> apply pow_pos <|> linarith }},
  obtain ⟨a, b, h_b_gt_1, h_abs_sub_pos, h_abs_sub_small⟩ := liouville_x (r + f.nat_degree),
  specialize h a b (by linarith),
  exact lt_irrefl _
    (calc abs (x - a/b)
        < 1 / b ^ (r + f.nat_degree) : h_abs_sub_small
    ... = 1 / (b ^ r * b ^ f.nat_degree) : by rw pow_add
    ... = 1 / b ^ r * (1 / b ^ f.nat_degree) : by rw one_div_mul_one_div
    ... ≤ 1 / 2 ^ r * (1 / b ^ f.nat_degree) :
        begin
          refine mul_le_mul _ (le_refl _) _ _,
          { rw [div_le_div_iff, one_mul, one_mul],
            refine pow_le_pow_of_le_left _ _ r,
            repeat { norm_cast, linarith <|> apply pow_nonneg <|> apply pow_pos }},
          repeat { rw one_div_nonneg, apply pow_nonneg, norm_cast, linarith }
        end
    ... ≤ A * (1 / b ^ f.nat_degree) :
        begin
          apply mul_le_mul,
          repeat { linarith <|> assumption },
          rw one_div_nonneg, apply pow_nonneg, norm_cast, linarith
        end
    ... = A / b ^ f.nat_degree : by rw ←div_eq_mul_one_div
    ... < abs (x - a/b) : h)
end

end is_liouville

end real
