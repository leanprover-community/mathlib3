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

open_locale big_operators
open polynomial real set finset

namespace real

/-!
# Liouville's theorem

This file contains the proof of Liouville's theorem stating that all Liouville numbers are
transcendental.
-/

/--
A Liouville's number `x` is a number such that for every natural number `n`, there exists `a, b ∈ ℤ`
such that `0 < |x - a/b| < 1/bⁿ`. We can assume without lose of generality that `1 < b`.
-/

def is_liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ 0 < abs(x - a / b) ∧ abs(x - a / b) < 1/b^n

namespace is_liouville

lemma not_liouville_zero : ¬ is_liouville 0 :=
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
  repeat { apply div_nonneg <|> norm_cast <|> linarith <|> assumption }
end

lemma abs_eval_rat_ge_one_div_denom_pow_n (f : polynomial ℤ) (a b : ℤ)
  (b_pos : 0 < b) (not_root : (f.map (algebra_map ℤ ℝ)).eval (a/b) ≠ 0) :
  1/(b : ℝ)^f.nat_degree ≤ abs ((f.map (algebra_map ℤ ℝ)).eval (a/b)) :=
begin
  have b_nonzero : b ≠ 0, from ne_of_gt b_pos,
  have b0 : (b : ℝ) ≠ 0, { exact_mod_cast ne_of_gt b_pos },
  have pos : 0 < 1 / (b : ℝ) ^ f.nat_degree,
  { exact div_pos zero_lt_one (pow_pos (by exact_mod_cast b_pos) _) },
  have eq₁ : ((f.map (algebra_map ℤ ℝ)).eval (a / b)) =
    1 / b ^ f.nat_degree * (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)),
  -- we give a rough outline of the calculation, and prove two obligations below
  calc  ((f.map (algebra_map ℤ ℝ)).eval (a / b))
      = ∑ i in f.support, f.coeff i * (a / b) ^ i : _ -- (1)
  ... = ∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i) / b ^ f.nat_degree :
        sum_congr rfl _ -- (2)
  ... = (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)) / b ^ f.nat_degree : by rw [sum_div]
  ... = 1 / b ^ f.nat_degree * (∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)) : by ring,
  { -- proof of (1)
    conv_lhs { rw [eval_map, as_sum_support f, eval₂_finset_sum] },
    simp only [coeff_map, eval₂_X_pow, div_pow, eval₂_mul, eval₂_C],
    congr },
  { -- proof of (2)
    intros i hi,
    suffices : (b ^ f.nat_degree : ℝ) = b ^ (f.nat_degree - i) * b ^ i,
    { field_simp [b0, this, mul_assoc] },
    rw [← pow_add, nat.sub_add_cancel (le_nat_degree_of_mem_support hi)] },
  have cast_eq : ∑ i in f.support, (f.coeff i : ℝ) * a ^ i * b ^ (f.nat_degree - i) =
                 ↑(∑ i in f.support, f.coeff i * a ^ i * b ^ (f.nat_degree - i)),
  { simp only [← int.coe_cast_ring_hom, ring_hom.map_sum, ring_hom.map_mul, ring_hom.map_pow] },
  rw [eq₁, cast_eq, abs_mul, abs_of_pos pos, le_mul_iff_one_le_right pos],
  rw [eq₁, mul_ne_zero_iff, cast_eq] at not_root,
  norm_cast at ⊢ not_root,
  exact abs_pos_iff.2 not_root.2
end

lemma exists_pos_real_of_irrational_root (α : ℝ) (hα : irrational α) (f : polynomial ℤ)
  (f_deg : 1 < f.nat_degree) (α_root : (f.map (algebra_map ℤ ℝ)).eval α = 0) :
  ∃ A : ℝ, 0 < A ∧ ∀ a b : ℤ, 0 < b → (A / b ^ (f.nat_degree)) < abs(α - a / b)  :=
begin
  -- find the maximum `M` of `abs Df` on `Icc (α - 1) (α + 1)`
  classical, rw irrational_iff_ne_rational at hα,
  have f_nonzero : f ≠ 0 := ne_zero_of_nat_degree_gt f_deg,
  have f_ℝ_nonzero : (f.map (algebra_map ℤ ℝ)) ≠ 0 := λ rid, f_nonzero
  begin
    ext m, rw polynomial.ext_iff at rid, specialize rid m,
    simp only [coeff_map, int.cast_eq_zero, ring_hom.eq_int_cast, coeff_zero] at ⊢ rid,
    exact rid
  end,
  rcases is_compact.exists_forall_ge (@compact_Icc (α-1) (α+1))
    begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
    (show continuous_on (λ x, abs ((f.map (algebra_map ℤ ℝ)).derivative.eval x)) _,
    begin apply continuous.continuous_on, continuity, exact continuous_abs end) with ⟨x_max, ⟨x_max_range, hM⟩⟩,
  simp only at hM,
  set M := abs ((f.map (algebra_map ℤ ℝ)).derivative.eval x_max),
  have M_nonzero : M ≠ 0,
  { intro absurd, rw absurd at hM,
    replace hM := nat_degree_eq_zero_of_derivative_eq_zero
      ((f.map (algebra_map ℤ ℝ)).derivative.eq_zero_of_infinite_is_root
        (infinite_mono (λ y hy, by simp only [mem_set_of_eq, is_root.def, abs_nonpos_iff.1 (hM y hy)])
        (Icc.infinite (show α - 1 < α + 1, by linarith)))),
    rw [nat_degree_map' (show function.injective (algebra_map ℤ ℝ), from int.cast_injective)] at hM,
    linarith only [f_deg, hM] },
  have M_pos : 0 < M := lt_of_le_of_ne (abs_nonneg _) M_nonzero.symm,
  clear M_nonzero,

  -- Let `B` be the minimum of `{|α - x| : x ∈ roots f ∧ x ≠ α} ∪ {1/M, 1}`.
  set f_roots' := (f.map (algebra_map ℤ ℝ)).roots.to_finset.erase α,
  set distances' := insert (1/M) (insert (1 : ℝ) (f_roots'.image (λ x, abs (α - x)))),
  have h_nonempty: distances'.nonempty := ⟨1/M, by simp only [true_or, eq_self_iff_true, finset.mem_insert]⟩,
  set B := distances'.min' h_nonempty with hB,
  have allpos : ∀ x : ℝ, x ∈ distances' → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_insert] at hx,
    rcases hx with hx | hx | hx,
    { rw hx, simp only [one_div, gt_iff_lt, inv_pos], exact M_pos },
    { rw hx, exact zero_lt_one },
    { simp only [exists_prop, finset.mem_image] at hx,
      rcases hx with ⟨α₀, hα₀⟩,
      rw [finset.mem_erase] at hα₀,
      rw [←hα₀.2, abs_pos_iff, sub_ne_zero], exact hα₀.1.1.symm } },
  have B_pos : 0 < B := hB.symm ▸ allpos (min' distances' h_nonempty) (min'_mem distances' h_nonempty),

  -- Then `B/2` satisfies all the requirement.
  use (B / 2),
  have hB₂ : 0 < B / 2 := half_pos B_pos,
  split,
  -- `0 < B/2`
  { exact hB₂ },
  -- `∀ (a b : ℤ), 0 < b → B / 2 / b ^ f.nat_degree < abs (α - a/b)`
  { by_contra absurd, simp only [exists_prop, not_lt, not_forall] at absurd,
    rcases absurd with ⟨a, b, b_pos, abs_lt⟩,
    have hb : 1 ≤ b ^ f.nat_degree := pow_pos b_pos f.nat_degree,
    have hb₁ : abs (α - a / b) ≤ B / 2,
    { refine le_trans abs_lt _,
      rw [div_le_iff, le_mul_iff_one_le_right],
      repeat { norm_cast <|> assumption, assumption <|> exact pow_pos b_pos _} },
    have hb₂ : abs (α - a / b) < B := lt_of_le_of_lt hb₁ (by linarith),
    have hab₀ : (a / b : ℝ) ∈ Icc (α - 1) (α + 1),
    { suffices : abs (α - a/b) ≤ 1,
      { rwa [←closed_ball_Icc, metric.mem_closed_ball, real.dist_eq, abs_sub] },
      suffices : B ≤ 1, linarith,
      rw hB, refine finset.min'_le distances' 1 _,
      rw [finset.mem_insert, finset.mem_insert], right, left, refl },
    have hab₁ : α ≠ a/b := hα a b,
    have hab₂ : (a/b:ℝ) ∉ (f.map (algebra_map ℤ ℝ)).roots.to_finset,
    { intro absurd,
      have H₁ : (a/b:ℝ) ∈ f_roots',
      { rw [finset.mem_erase], exact ⟨hab₁.symm, absurd⟩ },
      have H₂ : abs (α - a/b) ∈ distances',
      { rw [finset.mem_insert, finset.mem_insert, finset.mem_image], right, right,
        exact ⟨a/b, ⟨H₁, rfl⟩⟩ },
      have H₃ := finset.min'_le distances' (abs (α - a/b)) H₂,
      erw ←hB at H₃, linarith only [lt_of_lt_of_le hb₂ H₃] },
    have hab₂' : (f.map (algebra_map ℤ ℝ)).eval (a/b) ≠ 0,
    { rwa [multiset.mem_to_finset, mem_roots f_ℝ_nonzero, is_root.def] at hab₂ },

    -- We need to consider separately when `a/b < α` and when `α < a/b`. But two cases are similar
    rcases ne_iff_lt_or_gt.1 hab₁.symm with α_gt | α_lt,

    -- When `a/b < α`
    have cont_eval : continuous_on (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Icc (a/b) α) :=
      (map (algebra_map ℤ ℝ) f).continuous_eval.continuous_on,
    have diff_eval : differentiable_on ℝ (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Ioo (a/b) α) :=
      differentiable.differentiable_on (map (algebra_map ℤ ℝ) f).differentiable,
    rcases (exists_deriv_eq_slope (λ x, (f.map (algebra_map ℤ ℝ)).eval x)
      α_gt cont_eval diff_eval) with ⟨x₀, x₀_range, hx₀⟩,
    clear cont_eval diff_eval,
    simp only [polynomial.deriv, α_root, zero_sub] at hx₀,

    replace hx₀ := hx₀.symm,
    have Df_x₀_nonzero : (f.map (algebra_map ℤ ℝ)).derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ rid, hab₂'
      begin rwa [rid, neg_div, neg_eq_zero, div_eq_iff (show α - a/b ≠ 0, by linarith), zero_mul] at hx₀ end,

    replace hx₀ : (α - ↑a / ↑b) = -(f.map (algebra_map ℤ ℝ)).eval (a/b) / (f.map (algebra_map ℤ ℝ)).derivative.eval x₀,
    { symmetry, rw div_eq_iff at hx₀ ⊢,  rwa mul_comm,
      exact Df_x₀_nonzero,
      rwa sub_ne_zero },

    swap,
    -- When `α < a/b`
    have cont_eval : continuous_on (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Icc α (a/b)),
      { refine continuous.continuous_on _, continuity },
      have diff_eval : differentiable_on ℝ (λ x, (f.map (algebra_map ℤ ℝ)).eval x) (Ioo α (a/b)),
      { refine differentiable.differentiable_on _, exact (map (algebra_map ℤ ℝ) f).differentiable },
      rcases (exists_deriv_eq_slope (λ x, (f.map (algebra_map ℤ ℝ)).eval x)
                α_lt cont_eval diff_eval) with ⟨x₀, x₀_range, hx₀⟩,
      clear cont_eval diff_eval,
      simp only [polynomial.deriv, α_root, sub_zero] at hx₀,

      replace hx₀ := hx₀.symm,
      have Df_x₀_nonzero : (f.map (algebra_map ℤ ℝ)).derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ rid, hab₂'
        begin rwa [rid, div_eq_iff (show (a / b : ℝ) - α ≠ 0, by linarith), zero_mul] at hx₀ end,

      replace hx₀ : (↑a / ↑b - α) = (f.map (algebra_map ℤ ℝ)).eval (a/b) / (f.map (algebra_map ℤ ℝ)).derivative.eval x₀,
      { symmetry, rw div_eq_iff at hx₀ ⊢,  rwa mul_comm,
        exact Df_x₀_nonzero,
        rw sub_ne_zero, exact hab₁.symm },

    -- The rest are the same for two different cases
    repeat { exact lt_irrefl _
      (calc
          B / 2 / b^f.nat_degree
        ≥ abs (α - ↑a / ↑b) : ge_iff_le.2 abs_lt
    ... = abs((f.map (algebra_map ℤ ℝ)).eval (a/b) / ((f.map (algebra_map ℤ ℝ)).derivative.eval x₀)) :
        by rw [congr_arg abs hx₀, neg_div, abs_neg] <|>
          rw [show abs (α - a / b) = abs (a / b - α), from abs_sub α (a/b), congr_arg abs hx₀]
    ... = abs ((f.map (algebra_map ℤ ℝ)).eval (a/b)) /
          abs ((f.map (algebra_map ℤ ℝ)).derivative.eval x₀) : by rw abs_div
    ... ≥ 1/b^f.nat_degree / abs ((f.map (algebra_map ℤ ℝ)).derivative.eval x₀) :
        begin
          rw ge_iff_le,
          exact div_le_div (abs_nonneg _)
            (abs_eval_rat_ge_one_div_denom_pow_n f a b b_pos hab₂')
            (abs_pos_of_ne_zero Df_x₀_nonzero) (le_refl _)
        end
    ... ≥ 1/b^f.nat_degree / M :
        begin
          rw ge_iff_le,
          refine div_le_div _ (le_refl _) (abs_pos_of_ne_zero Df_x₀_nonzero) _,
          { rw one_div_nonneg, apply pow_nonneg, norm_cast, exact le_of_lt b_pos },
          { refine hM x₀ _, simp only [mem_Ioo, mem_Icc] at x₀_range hab₀ ⊢, split,
            { exact le_trans hab₀.1 (le_of_lt x₀_range.1) <|>
              exact le_trans (by linarith) (le_of_lt x₀_range.1) },
            { exact le_trans (le_of_lt x₀_range.2) (by linarith) } }
        end
    ... = 1/M / b^f.nat_degree : by ring
    ... ≥ B / b^f.nat_degree :
        begin
          rw ge_iff_le,
          refine div_le_div _ _ _ (le_refl _),
          { rw one_div_nonneg, exact le_of_lt M_pos },
          { refine finset.min'_le distances' (1/M) (mem_insert_self _ _) },
          { apply pow_pos, norm_cast, exact b_pos },
        end
    ... > B / 2 / b^f.nat_degree :
        begin
          rw [gt_iff_lt, div_lt_div_right],
          { exact half_lt_self B_pos },
          { apply pow_pos, norm_cast, exact b_pos },
        end) } }
end

lemma irrational_of_is_liouville {x : ℝ} (x_is_liouville : is_liouville x) : irrational x :=
begin
  rw irrational_iff_ne_rational,
  suffices : ∀ (a b : ℤ), 0 < b → x ≠ ↑a / ↑b,
  { intros a b,
    rcases lt_trichotomy 0 b with b_gt | b_0 | b_lt,
    { exact this a b b_gt },
    { intro rid, rw ←b_0 at rid,
      simp only [div_zero, int.cast_zero] at rid,
      rw rid at x_is_liouville,
      exact not_liouville_zero x_is_liouville },
    { specialize this (-a) (-b) (neg_pos.mpr b_lt),
      simp only [ne.def, int.cast_neg, neg_div_neg_eq] at this ⊢, exact this } },

  { intros a b b_pos rid,
    lift b to ℕ using le_of_lt b_pos,
    rw ←coe_coe at rid,
    norm_cast at b_pos,
    set n := b + 1 with hn,
    have b_ineq : b < 2 ^ (n-1) := nat.lt_two_pow b,
    rcases x_is_liouville n with ⟨p, q, q_gt_1, abs_sub_pos, abs_sub_small⟩,
    have q_pos : 0 < q := by linarith,
    lift q to ℕ using le_of_lt q_pos,
    rw [←coe_coe, rid] at *,
    norm_cast at q_gt_1 q_pos,
    rw [div_sub_div, abs_div] at abs_sub_pos abs_sub_small,

    -- We need to consider separately if `aq - bp = 0`
    by_cases (abs ((a:ℝ) * q - b * p) = 0),
    { rw h at abs_sub_pos abs_sub_small,
      simp only [one_div, zero_div, inv_pos] at abs_sub_pos abs_sub_small,
      linarith [abs_sub_pos] },

    { replace h : 0 < abs ((a:ℝ) * q - b * p) := abs_pos_of_ne_zero (λ rid, h begin rw [rid, abs_zero] end),
      have h' : 1 ≤ abs ((a:ℝ) * q - b * p),
      { norm_cast at h ⊢, linarith },
      rw (show abs (b * q : ℝ) = b * q,
        by { rw abs_of_nonneg, norm_cast, refine mul_nonneg bot_le bot_le }) at *,
      exact lt_irrefl _
        (calc 1
            ≤ abs ((a:ℝ) * q - b * p) : h'
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
        ... = 1 : by { rw div_self, apply fpow_ne_zero_of_ne_zero, linarith } ) },
    repeat { norm_cast, assumption <|> linarith } }
end

theorem transcendental_of_is_liouville {x : ℝ} (liouville_x : is_liouville x) : is_transcendental ℤ x :=
begin
  have irr_x : irrational x := irrational_of_is_liouville liouville_x,
  rintros ⟨f : polynomial ℤ, f_nonzero, root⟩,
  replace root : (f.map (algebra_map ℤ ℝ)).eval x = 0,
  { rw aeval_def at root, rwa [eval_map] },
  have root' : (f.map (algebra_map ℤ ℝ)).is_root x,
  { rwa is_root.def },
  have f_deg : 1 < f.nat_degree := nat_degree_gt_one_of_irrational_root x f irr_x f_nonzero root',
  rcases exists_pos_real_of_irrational_root x irr_x f f_deg root with ⟨A, A_pos, h⟩,
  have pow_big_enough : ∃ r : ℕ, 1/A ≤ 2 ^ r,
  { rcases pow_unbounded_of_one_lt (1/A) (lt_add_one 1) with ⟨n, hn⟩,
    exact ⟨n, le_of_lt hn⟩, },
  rcases pow_big_enough with ⟨r, hr⟩,
  have hr' : 1/(2^r) ≤ A,
  { rw [div_le_iff, mul_comm, ←div_le_iff], repeat { assumption <|> apply pow_pos <|> linarith } },
  rcases liouville_x (r + f.nat_degree) with ⟨a, b, b_gt_1, abs_sub_pos, abs_sub_small⟩,
  specialize h a b (by linarith),
  exact lt_irrefl _
    (calc abs (x - a/b)
        < 1 / b ^ (r + f.nat_degree) : abs_sub_small
    ... = 1 / (b ^ r * b ^ f.nat_degree) : by rw pow_add
    ... = 1 / b ^ r * (1 / b ^ f.nat_degree) : by rw one_div_mul_one_div
    ... ≤ 1 / 2 ^ r * (1 / b ^ f.nat_degree) :
        begin
          refine mul_le_mul _ (le_refl _) _ _,
          { rw [div_le_div_iff, one_mul, one_mul],
            refine pow_le_pow_of_le_left _ _ r,
            repeat { norm_cast, linarith <|> apply pow_nonneg <|> apply pow_pos } },
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
  apply @summable_of_nonneg_of_le _ (λ n, (1/10 : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, linarith },
  { intro b,
    simp only [one_div, inv_pow'],
    rw [inv_le_inv],
    apply pow_le_pow,
    repeat { exact nat.self_le_factorial b <|> apply pow_pos <|> linarith } },
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg; norm_num }
end

lemma summable_inv_pow_n_add_fact : ∀ n : ℕ, summable (λ i, 1 / (10 : ℝ) ^ (i + (n + 1))!) := λ n,
begin
  apply @summable_of_nonneg_of_le _ (λ n, (1/10 : ℝ) ^ n),
  { intro b, rw one_div_nonneg, apply pow_nonneg, linarith },
  { intro b,
    simp only [one_div, inv_pow'],
    rw [inv_le_inv],
    apply pow_le_pow,
    repeat { apply pow_pos <|> linarith },
    transitivity b!,
    { exact nat.self_le_factorial _ },
    { exact nat.factorial_le (nat.le.intro rfl) } },
  { apply summable_geometric_of_abs_lt_1, rw abs_of_nonneg; norm_num }
end

lemma rat_of_α_k : ∀ k, ∃ p : ℕ, α_first k terms = p / ((10:ℝ) ^ k!) := λ k,
begin
  induction k with k ih,
  { use 1,
    simp only [sum_singleton, nat.cast_one, range_one] },
  { rcases ih with ⟨p_k, h_k⟩,
    use p_k * (10^((k+1)! - k!)) + 1,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    norm_cast,
    rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring,
    rw mul_ne_zero_iff, split,
    all_goals { refine pow_ne_zero _ _, linarith } }
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
  have truncation_wd := α_eq_first_k_terms_add_rest n,
  rcases rat_of_α_k n with ⟨p, hp⟩,
  use [p, 10^n!],
  rw hp at truncation_wd,
  push_cast,
  rw [truncation_wd, add_sub_cancel', abs_of_pos (α_terms_after_pos _)],
  repeat { split },
  { apply one_lt_pow, norm_num, exact nat.factorial_pos _ },
  { exact α_terms_after_pos _ },
  { exact calc (∑' i, 1 / (10 : ℝ) ^ (i + (n+1))!)
      ≤ ∑' i, 1 / (10 : ℝ) ^ (i + (n+1)!) :
      begin
        refine tsum_le_tsum (λ b, _) (summable_inv_pow_n_add_fact _)
          (summable_of_nonneg_of_le (λ b, _) (λ b, _) (@summable_geometric_of_abs_lt_1 (1/10:ℝ)
            (show abs (1/10 : ℝ) < 1, by { rw abs_of_pos; linarith }))),
        { rw one_div_le_one_div,
          { apply pow_le_pow,
            { norm_num },
            { exact nat.add_factorial_le_factorial_add _ _ } },
          repeat { apply pow_pos, norm_num } },
        { rw one_div_nonneg, apply pow_nonneg, norm_num },
        { rw [div_pow, one_pow, one_div_le_one_div],
          apply pow_le_pow,
          repeat { exact nat.le.intro rfl <|> linarith <|> apply pow_pos <|> apply pow_nonneg } }
      end
  ... = ∑' i, (1/10 : ℝ)^ i * (1/10^(n+1)!) :
      by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
  ... = (∑' i, (1/10 : ℝ)^ i) * (1/10^(n+1)!) :
      begin
        rw tsum_mul_right,
        apply summable_geometric_of_abs_lt_1, rw [abs_of_nonneg]; norm_num
      end
  ... = 10 / 9 * (1/10^(n+1)!) :
      begin
        congr,
        rw tsum_geometric_of_abs_lt_1, repeat { rw [abs_of_nonneg] <|> norm_num }
      end
  ... < 2 * (1/10^(n+1)!) :
      by { apply mul_lt_mul, repeat { rw one_div_le_one_div <|> apply pow_pos <|> apply pow_nonneg <|> norm_num } }
  ... = 2 / 10^(n+1)! : by field_simp
  ... = 2 / 10^(n! * (n+1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / 10^(n! * n) :
      begin
        rw [div_lt_div_iff, one_mul],
        conv_rhs {rw mul_add, rw pow_add, rw mul_one, rw pow_mul, rw mul_comm},
        apply mul_lt_mul;
        norm_cast,
        { refine lt_of_lt_of_le (show 2 < 10, by norm_num) _,
          conv_lhs { rw show 10 = 10 ^ 1, by rw pow_one },
          apply pow_le_pow (show 1 ≤ 10, by linarith) (nat.factorial_pos _), },
        repeat { linarith <|> apply pow_pos <|> apply pow_nonneg <|> rw pow_mul },
      end
  ... = 1 / (10^n!)^n : by rw pow_mul }
end

lemma is_transcendental_of_α : is_transcendental ℤ α := transcendental_of_is_liouville is_liouville_of_α

end construction

end is_liouville

end real
