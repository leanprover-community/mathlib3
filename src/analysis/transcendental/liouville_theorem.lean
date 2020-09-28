/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value
import data.real.irrational
import data.set.intervals.infinite
import algebra.big_operators

open_locale big_operators
open polynomial real set finset

/-!
# Liouville's theorem

This file contains the proof of Liouville's theorem stating that all Liouville's numbers are
transcendental.
-/

notation `transcendental` x := ¬ is_algebraic ℤ x

/--
- a number is transcendental ↔ a number is not algebraic
- a Liouville's number `x` is a number such that
  for every natural number `n`, there is a `a/b ∈ ℚ - ℤ` such that `0 < |x - a/b| < 1/bⁿ`
-/

def liouville_number (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n

namespace liouville

lemma not_liouville_zero : ¬ liouville_number 0 :=
begin
  classical,
  intro rid,
  rcases rid 1 with ⟨a, b, b_gt_1, abs_sub_pos, abs_sub_small⟩,
  simp only [one_div, zero_sub, abs_neg, pow_one] at abs_sub_pos abs_sub_small,
  set a' := abs a,
  have a'_ineq : 0 ≤ a' := abs_nonneg _,
  have : abs (a' / b : ℝ) = abs (a / b), simp only [int.cast_abs, abs_div, abs_abs],
  rw ←this at abs_sub_pos abs_sub_small,
  rw [abs_of_nonneg, inv_eq_one_div, div_lt_div_iff, one_mul, mul_lt_iff_lt_one_left] at abs_sub_small,
  norm_cast at abs_sub_small,
  have : a' = 0, linarith,
  simp only [this, int.cast_zero, zero_div, abs_zero] at abs_sub_pos, linarith,
  repeat { norm_cast, linarith },
  { apply div_nonneg, norm_cast, assumption, norm_cast, linarith }
end

lemma abs_eval_rat_ge_one_div_denom_pow_n (f : polynomial ℤ) (a b : ℤ)
  (b_pos : 0 < b) (not_root : (f.map (algebra_map ℤ ℝ)).eval (a/b) ≠ 0) :
  1/(b : ℝ)^f.nat_degree ≤ abs ((f.map (algebra_map ℤ ℝ)).eval (a/b)) :=
have b_nonzero : b ≠ 0, from ne_of_gt b_pos,
have pos : 0 < 1 / (b : ℝ) ^ f.nat_degree, from
begin
  refine div_pos (show 0 < (1 : ℝ), from by linarith) (pow_pos _ _),
  norm_cast, exact b_pos,
end,
have eq₁ : (f.map (algebra_map ℤ ℝ)).eval (a/b) =
  1 / b ^ f.nat_degree * ∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i), from
calc ((f.map (algebra_map ℤ ℝ)).eval (a/b))
          = ∑ i in f.support, f.coeff i * (a / b) ^ i
          : begin
              conv_lhs { rw [eval_map, as_sum' f, eval₂_finset_sum] },
              simp only [coeff_map, eval₂_X_pow, div_pow, eval₂_mul, eval₂_C],
              congr
            end
      ... = 1/b^f.nat_degree * (∑ i in f.support, f.coeff i*a^i*b^(f.nat_degree - i)) :
            begin
              rw mul_sum, apply sum_congr rfl,
              intros n h,
              rw [calc (f.coeff n : ℝ) * (a/b)^n
                      = f.coeff n * (a ^ n / b ^ n) : by rw div_pow
                  ... = f.coeff n * a ^ n * (b ^ n)⁻¹ : by ring
                  ... = f.coeff n * a ^ n * b ^ (- n : ℤ) : by simp only [fpow_neg, fpow_coe_nat],
                  calc 1/(b : ℝ) ^ f.nat_degree * (f.coeff n * a ^ n * b ^ (f.nat_degree - n))
                      = f.coeff n * a ^ n * (b^(f.nat_degree - n) / (b ^ f.nat_degree)) : by ring
                  ... = f.coeff n * a ^ n * (b ^ ((f.nat_degree - n : ℕ) - f.nat_degree : ℤ))
                      : by {rw fpow_sub, simp only [fpow_coe_nat], norm_cast, exact b_nonzero}
                  ],
              congr,
              rw [neg_eq_iff_neg_eq, neg_sub, sub_eq_iff_eq_add],
              norm_cast,
              rw calc n + (f.nat_degree - n) = n + f.nat_degree - n
                  : begin
                      rw ←nat.add_sub_assoc, by_contra a,
                      simp only [gt_iff_lt, not_le, finsupp.mem_support_iff, ne.def] at a,
                      rw mem_support_iff_coeff_ne_zero at h,
                      refine h _, rw coeff_eq_zero_of_nat_degree_lt a
                    end
                ...  = f.nat_degree + n - n : by rw add_comm
                ...  = f.nat_degree + (n - n) : by rw nat.add_sub_assoc (rfl.ge)
                ...  = f.nat_degree + 0 : by rw nat.sub_self
                ...  = f.nat_degree : by rw add_zero,
            end,
have cast_eq : ∑ i in f.support, (f.coeff i : ℝ) * a ^ i * b ^ (f.nat_degree - i)
            = ↑(∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)), from
begin
  induction f.support using finset.induction_on with a s H ih,
  { simp only [int.cast_zero, sum_empty] },
  { rw [sum_insert H, sum_insert H, ih],
    simp only [int.cast_pow, int.cast_add, int.cast_mul] }
end,
begin
  rw [eq₁, cast_eq, abs_mul, abs_of_pos pos, le_mul_iff_one_le_right pos],
  norm_cast,
  suffices : 0 < abs (∑ (i : ℕ) in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)),
  { omega },
  { rw abs_pos_iff,
    rw [eq₁, mul_ne_zero_iff, cast_eq] at not_root,
    norm_cast at not_root,
    exact not_root.2 }
end

lemma about_irrational_root (α : ℝ) (hα : irrational α) (f : polynomial ℤ)
  (f_deg : 1 < f.nat_degree) (α_root : (f.map (algebra_map ℤ ℝ)).eval α = 0) :
  ∃ A : ℝ, 0 < A ∧ ∀ a b : ℤ, 0 < b → (A / b ^ (f.nat_degree)) < abs(α - a / b)  :=
have f_nonzero : f ≠ 0, from
begin
  intro rid,
  have : f.nat_degree = 0 := (congr_arg polynomial.nat_degree rid).trans rfl,
  rw this at f_deg, linarith,
end,
have f_ℝ_nonzero : (f.map (algebra_map ℤ ℝ)) ≠ 0, from
begin
  intro rid, refine f_nonzero _,
  ext m, rw polynomial.ext_iff at rid, specialize rid m,
  simp only [coeff_map, int.cast_eq_zero, ring_hom.eq_int_cast, coeff_zero] at ⊢ rid,
  exact rid
end,
begin
  classical, rw irrational_iff_ne_rational at hα,
  set Df_ℝ := (f.map (algebra_map ℤ ℝ)).derivative with h_Df,
  have H := is_compact.exists_forall_ge (@compact_Icc (α-1) (α+1))
            begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
            (show continuous_on (λ x, abs (Df_ℝ.eval x)) _,
            begin apply continuous.continuous_on, continuity, exact continuous_abs end),

  rcases H with ⟨x_max, ⟨x_max_range, hM⟩⟩,
  simp only [and_imp, id.def] at hM,
  set M := abs (Df_ℝ.eval x_max) with M_def,
  have M_nonzero : M ≠ 0,
  { intro absurd, rw absurd at hM,
    replace hM : ∀ (y : ℝ), y ∈ Icc (α - 1) (α + 1) → (polynomial.eval y Df_ℝ) = 0,
    { intros y hy, specialize hM _ hy,simp only [abs_nonpos_iff] at hM, exact hM },
    replace hM := Df_ℝ.eq_zero_of_infinite_is_root
                    (infinite_mono (λ y hy, by simp only [mem_set_of_eq, is_root.def, hM y hy])
                      (Icc.infinite (show α - 1 < α + 1, by linarith))),
    replace hM := nat_degree_eq_zero_of_derivative_eq_zero hM,
    rw ←degree_eq_iff_nat_degree_eq f_ℝ_nonzero at hM,
    simp only [with_top.coe_zero] at hM,
    replace hM := eq_C_of_degree_eq_zero hM,
    replace hM : f = C (f.coeff 0),
    { ext, rw polynomial.ext_iff at hM,
      simp only [coeff_map, coeff_C] at hM ⊢,
      specialize hM n,
      split_ifs,
      { rwa h },
      { simp only [h, int.cast_eq_zero, ring_hom.eq_int_cast, if_false] at hM, exact hM } },
    replace hM : f.nat_degree = 0,
    { rw [hM, nat_degree_C] }, linarith },
  have M_pos : 0 < M,
  { rw [M_def] at M_nonzero ⊢, exact lt_of_le_of_ne (abs_nonneg _) M_nonzero.symm },

  set f_roots := (f.map (algebra_map ℤ ℝ)).roots.to_finset with roots_def,
  set f_roots' := f_roots.erase α with roots'_def,
  set distances := f_roots'.image (λ x, abs (α - x)) with roots_distance_to_α,
  set distances' := insert (1/M) (insert (1:ℝ) distances) with hdistances',
  have h_nonempty: distances'.nonempty,
  { rw [hdistances', finset.nonempty],
    use (1/M), simp only [true_or, eq_self_iff_true, finset.mem_insert] },

  set B := distances'.min' h_nonempty with hB,
  have allpos : ∀ x : ℝ, x ∈ distances' → 0 < x,
  { intros x hx, rw [hdistances', finset.mem_insert, finset.mem_insert] at hx,
    rcases hx with hx | hx | hx,
    { rw hx, simp only [one_div, gt_iff_lt, inv_pos], exact M_pos },
    { rw hx, exact zero_lt_one },
    { rw [roots_distance_to_α] at hx,
      simp only [exists_prop, finset.mem_image] at hx,
      rcases hx with ⟨α₀, hα₀⟩,
      rw [roots'_def, finset.mem_erase] at hα₀,
      rw [←hα₀.2, abs_pos_iff, sub_ne_zero], exact hα₀.1.1.symm } },
  have B_pos : 0 < B := hB.symm ▸ allpos (min' distances' h_nonempty) (min'_mem distances' h_nonempty),

  use (B / 2),
  have hB₂ : 0 < B / 2 := half_pos B_pos,
  split,
  { exact hB₂ },
  { by_contra absurd, simp only [exists_prop, not_lt, not_forall] at absurd,
    rcases absurd with ⟨a, b, b_pos, abs_lt⟩,
    have hb : 1 ≤ b ^ f.nat_degree,
    { change 0 < b ^ f.nat_degree, exact pow_pos b_pos f.nat_degree },
    have hb₁ : abs (α - a / b) ≤ B / 2,
    { refine le_trans abs_lt _,
      rw [div_le_iff, le_mul_iff_one_le_right],
      { norm_cast, exact hb },
      { exact hB₂ },
      { norm_cast, exact pow_pos b_pos _ } },
    have hb₂ : abs (α - a / b) < B := lt_of_le_of_lt hb₁ (by linarith),

    have hab₀ : (a / b : ℝ) ∈ Icc (α - 1) (α + 1),
    { suffices : abs (α - a/b) ≤ 1,
      { rw [←closed_ball_Icc, metric.mem_closed_ball, real.dist_eq, abs_sub],
        exact this, },
      suffices : B ≤ 1, linarith,
      rw hB, refine finset.min'_le distances' 1 _,
      rw [hdistances', finset.mem_insert, finset.mem_insert], tauto },
    have hab₁ : α ≠ a/b := hα a b,
    have hab₂ : (a/b:ℝ) ∉ f_roots,
    { intro absurd,
      have H₁ : (a/b:ℝ) ∈ f_roots',
      { rw [roots'_def, finset.mem_erase], exact ⟨hab₁.symm, absurd⟩ },
      have H₂ : abs (α - a/b) ∈ distances',
      { rw [hdistances', finset.mem_insert, finset.mem_insert], right, right,
        rw [roots_distance_to_α, finset.mem_image], use (a/b:ℝ), exact ⟨H₁, rfl⟩ },
      have H₃ := finset.min'_le distances' (abs (α - a/b)) H₂,
      erw ←hB at H₃, linarith },
    have hab₂' : (f.map (algebra_map ℤ ℝ)).eval (a/b) ≠ 0,
    { rwa [multiset.mem_to_finset, mem_roots f_ℝ_nonzero, is_root.def] at hab₂ },
    have hab₃ := ne_iff_lt_or_gt.1 hab₁.symm,

    rcases hab₃ with α_gt | α_lt,
    { have cont_eval : continuous_on (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Icc (a/b) α),
      { refine continuous.continuous_on _, continuity },
      have diff_eval : differentiable_on ℝ (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Ioo (a/b) α),
      { refine differentiable.differentiable_on _, exact (map (algebra_map ℤ ℝ) f).differentiable},
      rcases (exists_deriv_eq_slope (λ x, (f.map (algebra_map ℤ ℝ)).eval x)
                α_gt cont_eval diff_eval) with ⟨x₀, x₀_range, hx₀⟩,
      clear cont_eval diff_eval,
      simp only [polynomial.deriv, α_root, zero_sub] at hx₀,

      have Df_x₀_nonzero : (f.map (algebra_map ℤ ℝ)).derivative.eval x₀ ≠ 0,
      { rw hx₀, intro rid,
        rw [neg_div, neg_eq_zero, div_eq_iff (show α - a/b ≠ 0, by linarith), zero_mul] at rid,
        exact hab₂' rid },

      replace hx₀ := hx₀.symm,
      replace hx₀ : (α - ↑a / ↑b) = -(f.map (algebra_map ℤ ℝ)).eval (a/b) / (f.map (algebra_map ℤ ℝ)).derivative.eval x₀,
      { symmetry, rw div_eq_iff at hx₀ ⊢,  rw mul_comm, exact hx₀,
        exact Df_x₀_nonzero,
        rwa sub_ne_zero },

      have ineq :=
        calc B / 2 / b^f.nat_degree
          ≥ abs (α - ↑a / ↑b) : ge_iff_le.2 abs_lt
      ... = abs((f.map (algebra_map ℤ ℝ)).eval (a/b) / (Df_ℝ.eval x₀))
          : by rw [congr_arg abs hx₀, neg_div, abs_neg]
      ... = abs ((f.map (algebra_map ℤ ℝ)).eval (a/b)) / abs (Df_ℝ.eval x₀)
          : by rw abs_div
      ... ≥ 1/b^f.nat_degree / abs (Df_ℝ.eval x₀)
          : begin
              rw ge_iff_le,
              refine div_le_div (abs_nonneg _)
                (abs_eval_rat_ge_one_div_denom_pow_n f a b b_pos hab₂')
                (abs_pos_of_ne_zero Df_x₀_nonzero) (le_refl _),
            end
      ... ≥ 1/b^f.nat_degree / M
          : begin
              rw ge_iff_le,
              refine div_le_div _ (le_refl _) (abs_pos_of_ne_zero Df_x₀_nonzero) _,
              { rw one_div_nonneg, apply pow_nonneg, norm_cast, exact le_of_lt b_pos },
              { refine hM x₀ _, simp only [mem_Ioo, mem_Icc] at x₀_range hab₀ ⊢, split,
                { exact le_trans hab₀.1 (le_of_lt x₀_range.1) },
                { exact le_trans (le_of_lt x₀_range.2) (by linarith) } }
            end
      ... = 1/M / b^f.nat_degree
          : by ring
      ... ≥ B / b^f.nat_degree
          : begin
              rw ge_iff_le,
              refine div_le_div _ _ _ (le_refl _),
              { rw one_div_nonneg, exact le_of_lt M_pos },
              { refine finset.min'_le distances' (1/M) (mem_insert_self _ _) },
              { apply pow_pos, norm_cast, exact b_pos },
            end
      ... > B / 2 / b^f.nat_degree
          : begin
              rw [gt_iff_lt, div_lt_div_right],
              { exact half_lt_self B_pos },
              { apply pow_pos, norm_cast, exact b_pos },
            end,

      linarith only [ineq] },
    { have cont_eval : continuous_on (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Icc α (a/b)),
      { refine continuous.continuous_on _, continuity },
      have diff_eval : differentiable_on ℝ (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Ioo α (a/b)),
      { refine differentiable.differentiable_on _, exact (map (algebra_map ℤ ℝ) f).differentiable },
      rcases (exists_deriv_eq_slope (λ x, (f.map (algebra_map ℤ ℝ)).eval x)
                α_lt cont_eval diff_eval) with ⟨x₀, x₀_range, hx₀⟩,
      clear cont_eval diff_eval,
      simp only [polynomial.deriv, α_root, sub_zero] at hx₀,

      have Df_x₀_nonzero : (f.map (algebra_map ℤ ℝ)).derivative.eval x₀ ≠ 0,
      { rw hx₀, intro rid,
        rw [div_eq_iff (show (a/b:ℝ) - α ≠ 0, by linarith), zero_mul] at rid,
        exact hab₂' rid },

      replace hx₀ := hx₀.symm,
      replace hx₀ : (↑a / ↑b - α) = (f.map (algebra_map ℤ ℝ)).eval (a/b) / (f.map (algebra_map ℤ ℝ)).derivative.eval x₀,
      { symmetry, rw div_eq_iff at hx₀ ⊢,  rw mul_comm, exact hx₀,
        exact Df_x₀_nonzero,
        rw sub_ne_zero, exact hab₁.symm },

      have ineq :=
        calc B / 2 / b^f.nat_degree
          ≥ abs (↑a / ↑b - α) : abs_sub α (a/b:ℝ) ▸ ge_iff_le.2 abs_lt
      ... = abs((f.map (algebra_map ℤ ℝ)).eval (a/b) / (Df_ℝ.eval x₀))
          : by rw congr_arg abs hx₀
      ... = abs ((f.map (algebra_map ℤ ℝ)).eval (a/b)) / abs (Df_ℝ.eval x₀)
          : by rw abs_div
      ... ≥ 1/b^f.nat_degree / abs (Df_ℝ.eval x₀)
          : begin
              rw ge_iff_le,
              refine div_le_div (abs_nonneg _)
                (abs_eval_rat_ge_one_div_denom_pow_n f a b b_pos hab₂')
                (abs_pos_of_ne_zero Df_x₀_nonzero) (le_refl _),
            end
      ... ≥ 1/b^f.nat_degree / M
          : begin
              rw ge_iff_le,
              refine div_le_div _ (le_refl _) (abs_pos_of_ne_zero Df_x₀_nonzero) _,
              { rw one_div_nonneg, apply pow_nonneg, norm_cast, exact le_of_lt b_pos },
              { refine hM x₀ _, simp only [mem_Ioo, mem_Icc] at x₀_range hab₀ ⊢, split,
                { exact le_trans (by linarith) (le_of_lt x₀_range.1) },
                { exact le_trans (le_of_lt x₀_range.2) (by linarith) } }
            end
      ... = 1/M / b^f.nat_degree
          : by ring
      ... ≥ B / b^f.nat_degree
          : begin
              rw ge_iff_le,
              refine div_le_div _ _ _ (le_refl _),
              { rw one_div_nonneg, exact le_of_lt M_pos },
              { refine finset.min'_le distances' (1/M) (mem_insert_self _ _) },
              { apply pow_pos, norm_cast, exact b_pos },
            end
      ... > B / 2 / b^f.nat_degree
          : begin
              rw [gt_iff_lt, div_lt_div_right],
              { exact half_lt_self B_pos },
              { apply pow_pos, norm_cast, exact b_pos },
            end,

      linarith only [ineq] } }
end

lemma irrational_of_liouville (x : ℝ) (liouvilleₓ : liouville_number x) : irrational x :=
begin
  rw irrational_iff_ne_rational,
  suffices : ∀ (a b : ℤ), 0 < b → x ≠ ↑a / ↑b,
  { intros a b,
    rcases lt_trichotomy 0 b with b_gt | b_0 | b_lt,
    { exact this a b b_gt },
    { intro rid, rw ←b_0 at rid,
      simp only [div_zero, int.cast_zero] at rid,
      rw rid at liouvilleₓ,
      exact not_liouville_zero liouvilleₓ },
    { specialize this (-a) (-b) (neg_pos.mpr b_lt),
      simp only [ne.def, int.cast_neg, neg_div_neg_eq] at this ⊢, exact this } },

  { intros a b b_pos rid,
    have b_nonneg : 0 ≤ b := le_of_lt b_pos,
    lift b to ℕ using b_nonneg,
    replace rid : x = (a/b:ℝ) := by tidy,
    set n := b + 1 with hn,
    have b_ineq : b < 2 ^ (n-1),
    { simp only [nat.add_succ_sub_one, add_zero],
      exact nat.lt_two_pow b },

    rcases liouvilleₓ n with ⟨p, q, q_gt_1, abs_sub_pos, abs_sub_small⟩,
    have q_pos : 0 < q := by linarith,
    have q_nonneg : 0 ≤ q := le_of_lt q_pos,
    lift q to ℕ using q_nonneg,
    rw [←coe_coe, rid] at *,
    norm_cast at b_pos q_gt_1 q_pos,
    rw [div_sub_div, abs_div] at abs_sub_pos abs_sub_small,

    by_cases (abs ((a:ℝ) * q - b * p) = 0),
    { rw h at abs_sub_pos abs_sub_small,
      simp only [one_div, zero_div, inv_pos] at abs_sub_pos abs_sub_small,
      linarith [abs_sub_pos] },

    { replace h : 0 < abs ((a:ℝ) * q - b * p),
      { apply abs_pos_of_ne_zero, intro rid, refine h _, rw rid, exact abs_zero },
      have h' : 1 ≤ abs ((a:ℝ) * q - b * p),
      { norm_cast at h ⊢, linarith },
      rw (show abs (b * q : ℝ) = b * q,
        by { rw abs_of_nonneg, norm_cast, refine mul_nonneg bot_le bot_le }) at *,
      have ineq := calc
              1 ≤ abs ((a:ℝ) * q - b * p) : h'
            ... < (b : ℝ) * q / q ^ n :
                begin
                  rw [div_lt_iff] at abs_sub_small,
                  convert abs_sub_small using 1,
                  ring,
                  norm_cast, exact mul_pos b_pos q_pos
                end
            ... = (b : ℝ) * q / q ^ (n : ℤ) : by tidy
            ... = (b : ℝ) / (q : ℝ) ^ (n - 1 : ℤ) :
                begin
                  rw [div_eq_div_iff, mul_assoc,
                      show (q : ℝ) * (q : ℝ) ^ (n - 1 : ℤ) = q ^ (1 + (n - 1) : ℤ),
                      begin rw [fpow_add, fpow_one], norm_cast, linarith end,
                      show (1 + (n - 1) : ℤ) = n, by ring],
                  repeat {apply fpow_ne_zero, norm_cast, linarith }
                end
            ... ≤ (b : ℝ) / 2 ^ (n - 1 : ℤ) :
                begin
                  rw div_le_div_iff,
                  refine mul_le_mul (le_refl _) _
                    (fpow_nonneg_of_nonneg (show (0 : ℝ) ≤ 2, by linarith) _)
                    (show (0 : ℝ) ≤ b, by { norm_cast, exact bot_le }),
                  { simp only [int.coe_nat_succ, add_sub_cancel, fpow_coe_nat],
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
                  refine mul_lt_mul b_ineq (le_refl _) _ _,
                  repeat { apply pow_pos <|> apply pow_nonneg, linarith }
                end
            ... = 1 :
                begin
                  rw div_self, apply fpow_ne_zero_of_ne_zero, linarith
                end,
      linarith only [ineq] },

    repeat { norm_cast, assumption <|> linarith } }
end

end liouville
