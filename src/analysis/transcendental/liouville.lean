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

lemma exists_forall_ge_of_polynomial_deriv (α : ℝ) (f : polynomial ℝ)
  (h_f_deg : 0 < f.nat_degree) :
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f.derivative) ≤ M :=
begin
  have h_f_nonzero : f ≠ 0 := ne_zero_of_nat_degree_gt h_f_deg,
  obtain ⟨x_max, ⟨h_x_max_range, hM⟩⟩ := is_compact.exists_forall_ge (@compact_Icc (α-1) (α+1))
    begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
    (continuous_abs.comp f.derivative.continuous_eval).continuous_on,
  replace hM : ∀ (y : ℝ), y ∈ Icc (α - 1) (α + 1) →
    abs (eval y f.derivative) ≤ abs (eval x_max f.derivative),
    { simpa only [function.comp_app abs] },
  set M := abs (f.derivative.eval x_max),
  use M,
  split,
  { apply lt_of_le_of_ne (abs_nonneg _),
    intro hM0, change 0 = M at hM0, rw hM0.symm at hM,
    replace hM := nat_degree_eq_zero_of_derivative_eq_zero
      (f.derivative.eq_zero_of_infinite_is_root
        (infinite_mono (λ y hy, _)
        (Icc.infinite (show α - 1 < α + 1, by linarith)))),
    { linarith only [h_f_deg, hM] },
    { simp only [mem_set_of_eq, is_root.def, abs_nonpos_iff.1 (hM y hy)] }},
  intros y hy,
  have hy' : y ∈ Icc (α - 1) (α + 1),
  { apply mem_Icc.mpr,
    have h1 := le_abs_self (y - α),
    have h2 := neg_le_abs_self (y - α),
    split; linarith },
  exact hM y hy'
end

lemma non_root_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) :
  ∃ B : ℝ, 0 < B ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (f_roots.image (λ x, abs (α - x))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { rw [finset.mem_erase] at h,
      rw [abs_pos, sub_ne_zero], exact h.1.symm }},
  use [B, (h_allpos B (distances.min'_mem h_nonempty))],
  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_image], right, exact ⟨x, ⟨h₁, rfl⟩⟩ },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂
end

lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨B0, ⟨h_B0_pos, h_B0_root⟩⟩ := non_root_interval_of_polynomial α f h_f_nonzero,
  have h1M : 0 < 1 / M := one_div_pos.mpr hM,
  obtain ⟨B1, ⟨hB11, hB12, hB13⟩⟩ : ∃ B1 : ℝ, 0 < B1 ∧ B1 ≤ 1 / M ∧ B1 ≤ B0,
  { cases le_or_gt (1 / M) B0,
    { use 1 / M, tauto },
    { exact ⟨B0, h_B0_pos, le_of_lt h, le_refl B0⟩ }},
  obtain ⟨B, ⟨hB1, hB2, hB3, hB4⟩⟩ : ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1 ∧ B ≤ B0,
  { cases le_or_gt 1 B1,
    { use 1, split, norm_num, split, linarith, split, norm_num, linarith },
    { use B1, exact ⟨hB11, ⟨hB12, ⟨le_of_lt h, hB13⟩⟩⟩ }},
  refine ⟨B, hB1, hB2, hB3, λ (x : ℝ) (hx : abs (α - x) < B), h_B0_root x _ ⟩,
  linarith
end

lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  have h₀ : x ≠ α, { intro h₁, rw ← h₁ at h_α_root, rw h_α_root at h, tauto },
  rcases ne_iff_lt_or_gt.1 h₀ with h_α_gt | h_α_lt,
  { -- When `x < α`
    have h_cont : continuous_on (λ x, f.eval x) (Icc x α) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo x α) :=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_gt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval α f - eval x f) / (α - x) at hx₀,
    rw [h_α_root, zero_sub] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin
      rwa [hc, neg_div, neg_eq_zero, div_eq_iff (show α - x ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢, rwa mul_comm,
      exact h_Df_nonzero,
      rw sub_ne_zero, exact h₀.symm },
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_pos (sub_pos.mpr h_α_gt), abs_of_pos (sub_pos.mpr x₀_range.2),
      abs_of_neg (sub_lt_zero.mpr x₀_range.1)],
    split; linarith },
  { -- When `α < x`
    have h_cont : continuous_on (λ x, f.eval x) (Icc α x) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo α x):=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_lt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval x f - eval α f) / (x - α) at hx₀,
    rw [h_α_root, sub_zero] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin rwa [hc, div_eq_iff (show x - α ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢,
      {rw hx₀, ring },
      { exact h_Df_nonzero },
      { rwa sub_ne_zero }},
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_neg (sub_lt_zero.mpr x₀_range.1), abs_of_neg (sub_lt_zero.mpr h_α_lt),
      abs_of_pos (sub_pos.mpr x₀_range.2)],
    split; linarith }
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

section construction

noncomputable theory
open_locale nat

local notation `α` := ∑' (i : ℕ), 1 / (10 : ℝ) ^ i!
local notation `α_first` k `terms` :=  ∑ i in range (k+1), 1 / (10 : ℝ) ^ i!
local notation `α_terms_after` k := ∑' i, 1 / (10 : ℝ) ^ (i + (k+1))!

lemma summable_inv_pow_fact : summable (λ i, 1 / (10 : ℝ) ^ i!) :=
begin
  apply @summable_of_nonneg_of_le _ (λ n, (1 / 10 : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, norm_num },
  { intro b, dsimp only [],
    rw [one_div, (by norm_num : (1 : ℝ) / 10 = 10⁻¹), inv_pow', inv_le_inv],
    { apply pow_le_pow _ (nat.self_le_factorial b),
      norm_num },
    repeat { apply pow_pos, norm_num }},
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg; norm_num }
end

lemma summable_inv_pow_n_add_fact : ∀ n : ℕ, summable (λ i, 1 / (10 : ℝ) ^ (i + (n + 1))!) := λ n,
begin
  apply @summable_of_nonneg_of_le _ (λ n, (1 / 10 : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, norm_num },
  { intro b, dsimp only [],
    rw [one_div, (by norm_num : (1 : ℝ) / 10 = 10⁻¹), inv_pow', inv_le_inv],
    apply pow_le_pow,
    repeat { apply pow_pos <|> linarith },
    transitivity b!,
    { exact nat.self_le_factorial _ },
    { exact nat.factorial_le (nat.le.intro rfl) }},
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg; norm_num }
end

lemma rat_of_α_k : ∀ k, ∃ p : ℕ, α_first k terms = p / ((10 : ℝ) ^ k!) := λ k,
begin
  induction k with k h,
  { use 1,
    simp only [sum_singleton, nat.cast_one, range_one] },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (10 ^ ((k + 1)! - k!)) + 1,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    rw mul_ne_zero_iff, split,
    all_goals { refine pow_ne_zero _ _, norm_num }}
end

lemma α_terms_after_pos : ∀ k, 0 < α_terms_after k := λ n,
calc 0 < 1 / (10 : ℝ) ^ (n + 1)! : by { rw one_div_pos, apply pow_pos, norm_num }
  ... = 1 / (10 : ℝ) ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / (10 : ℝ) ^ (i + (n + 1))! :
      begin
        refine le_tsum (summable_inv_pow_n_add_fact _) 0 (λ _ _, _),
        rw one_div_nonneg, apply pow_nonneg, norm_num
      end

lemma α_eq_first_k_terms_add_rest : ∀ k, α = α_first k terms + α_terms_after k :=
λ k, (sum_add_tsum_nat_add _ summable_inv_pow_fact).symm

theorem is_liouville_of_α : is_liouville α :=
begin
  intro n,
  have h_truncation_wd := α_eq_first_k_terms_add_rest n,
  rcases rat_of_α_k n with ⟨p, hp⟩,
  use [p, 10 ^ n!],
  rw hp at h_truncation_wd,
  push_cast,
  rw [h_truncation_wd, add_sub_cancel', abs_of_pos (α_terms_after_pos _)],
  repeat { split },
  { apply one_lt_pow, norm_num, exact nat.factorial_pos _ },
  { exact α_terms_after_pos _ },
  { exact calc (∑' i, 1 / (10 : ℝ) ^ (i + (n + 1))!)
      ≤ ∑' i, 1 / (10 : ℝ) ^ (i + (n + 1)!) :
      begin
        refine tsum_le_tsum (λ b, _) (summable_inv_pow_n_add_fact _)
          (summable_of_nonneg_of_le (λ b, _) (λ b, _) (@summable_geometric_of_abs_lt_1 (1 / 10 : ℝ)
            (show abs (1 / 10 : ℝ) < 1, by { rw abs_of_pos; norm_num }))),
        { rw one_div_le_one_div,
          { apply pow_le_pow,
            { norm_num },
            { exact nat.add_factorial_le_factorial_add _ _ (nat.succ_ne_zero _) }},
          repeat { apply pow_pos, norm_num }},
        { rw one_div_nonneg, apply pow_nonneg, norm_num },
        { rw [div_pow, one_pow, one_div_le_one_div],
          apply pow_le_pow,
          repeat { exact nat.le.intro rfl <|> linarith <|> apply pow_pos <|> apply pow_nonneg }}
      end
  ... = ∑' i, (1 / 10 : ℝ) ^ i * (1 / 10 ^ (n + 1)!) :
      by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
  ... = (∑' i, (1 / 10 : ℝ) ^ i) * (1 / 10 ^ (n + 1)!) :
      begin
        rw tsum_mul_right,
        apply summable_geometric_of_abs_lt_1, rw [abs_of_nonneg]; norm_num
      end
  ... = 10 / 9 * (1 / 10 ^ (n + 1)!) :
      begin
        congr,
        rw tsum_geometric_of_abs_lt_1, repeat { rw [abs_of_nonneg] <|> norm_num }
      end
  ... < 2 * (1 / 10 ^ (n + 1)!) :
      by { apply mul_lt_mul,
        repeat { rw one_div_le_one_div <|> apply pow_pos <|> apply pow_nonneg <|> norm_num }}
  ... = 2 / 10 ^ (n + 1)! : by field_simp
  ... = 2 / 10 ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / 10 ^ (n! * n) :
      begin
        rw [div_lt_div_iff, one_mul],
        conv_rhs {rw mul_add, rw pow_add, rw mul_one, rw pow_mul, rw mul_comm},
        apply mul_lt_mul;
        norm_cast,
        { refine lt_of_lt_of_le (show 2 < 10, by norm_num) _,
          conv_lhs { rw show 10 = 10 ^ 1, by rw pow_one },
          apply pow_le_pow (show 1 ≤ 10, by norm_num) (nat.factorial_pos _), },
        repeat { linarith <|> apply pow_pos <|> apply pow_nonneg <|> rw pow_mul },
      end
  ... = 1 / (10 ^ n!) ^ n : by rw pow_mul }
end

lemma is_transcendental_of_α : is_transcendental ℤ α :=
  transcendental_of_is_liouville is_liouville_of_α

end construction

end is_liouville

end real
