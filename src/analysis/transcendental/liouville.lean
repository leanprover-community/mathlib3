/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.real.irrational
import data.polynomial.denoms_clearable
import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value

/-!
# Liouville's theorem

This file contains the proof of Liouville's theorem stating that all Liouville numbers are
transcendental.
-/

lemma int.mul_lt_mul_pow_succ {n : ℕ} {a q : ℤ}
 (a0 : 0 < a)
 (q1 : 1 < q) :
 (n : ℤ) * q < a * q ^ (n + 1) :=
begin
  have q2 : a * 2 ^ n ≤ a * q ^ n := (mul_le_mul_left a0).mpr
    (pow_le_pow_of_le_left zero_le_two ((int.lt_iff_add_one_le 1 q).mp q1) n),
  have a2 : 2 ^n ≤ a * 2 ^ n :=
    (le_mul_iff_one_le_left (pow_pos zero_lt_two n)).mpr ((int.lt_iff_add_one_le 0 a).mp a0),
  rw [pow_succ', ← mul_assoc],
  refine (mul_lt_mul_right (lt_trans zero_lt_one q1)).mpr (lt_of_lt_of_le (lt_of_lt_of_le _ a2) q2),
  exact_mod_cast nat.lt_two_pow n,
end

namespace real
/--
A Liouville number `x` is a number such that for every natural number `n`, there exists `a, b ∈ ℤ`
with `b > 1` such that `0 < |x - a/b| < 1/bⁿ`.
-/
def is_liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ 0 < abs (x - a / b) ∧ abs (x - a / b) < 1 / b ^ n

lemma not_liouville_zero : ¬ is_liouville 0 :=
begin
  intro h,
  rcases h 1 with ⟨a, b, h_b_gt_1, ab0, ald⟩,
  rw [zero_sub, abs_neg, abs_pos, ne.def, div_eq_zero_iff, not_or_distrib] at ab0,
  rw [pow_one, zero_sub, abs_neg, abs_div, @abs_of_pos _ _ (b : ℝ), div_lt_div_iff,
    mul_lt_mul_right] at ald,
  cases ab0 with a0 b0,
  refine a0 _,
  any_goals { exact_mod_cast lt_trans zero_lt_one h_b_gt_1 },
  norm_cast at ald ⊢,
  exact abs_eq_zero.mp ((int.sub_one_lt_iff.mp (sub_lt_zero.mpr ald)).antisymm (abs_nonneg _)),
end

lemma irrational_of_is_liouville {x : ℝ} (h : is_liouville x) : irrational x :=
begin
  rintros ⟨r, rfl⟩,
  cases r with a b bN0 cop,
  change (is_liouville (a / b)) at h,
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩,
  have qR0 : (0 : ℝ) < q, exact_mod_cast (lt_trans zero_lt_one q1),
  have b0 : (b : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast bN0),
  have bq0 : (0 : ℝ) < b * q := mul_pos (by exact_mod_cast bN0) qR0,
  rw [div_sub_div (a : ℝ) (p : ℝ) b0 (ne_of_gt qR0), abs_div] at a0 a1,
  rw [lt_div_iff (abs_pos.mpr (mul_ne_zero b0 (ne_of_gt qR0))), zero_mul] at a0,
  rw [div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0)) (pow_pos qR0 _), abs_of_pos bq0, one_mul] at a1,
  norm_cast at a1 a0,
  exact not_le.mpr a1 (le_of_lt (int.mul_lt_mul_pow_succ a0 q1)),
end

end real

lemma pow_mul_lt_c {ab A b c : ℝ} {r d : ℕ} (A0 : 0 < A)
  (c0 : 0 < c) (b2 : c ≤ b) (hl : (b : ℝ) ^ (r + d) * ab < 1) (A2 : 1 ≤ c ^ r * A) :
  (b : ℝ) ^ d * ab < A :=
begin
  rw [pow_add, mul_assoc] at hl,
  refine lt_of_lt_of_le ((lt_div_iff' _).mpr hl) ((div_le_iff' _).mpr (le_trans A2 _)),
  any_goals { exact pow_pos (lt_of_lt_of_le c0 b2) r },
  exact (mul_le_mul_right A0).mpr (pow_le_pow_of_le_left (le_of_lt c0) b2 r),
end

open set ring_hom

namespace polynomial

lemma one_le_denom_pow_eval_rat {f : polynomial ℤ} {a b : ℤ}
  (b0 : (0 : ℝ) < b) (fab : eval ((a : ℝ) / b) (f.map (algebra_map ℤ ℝ)) ≠ 0) :
  (1 : ℝ) ≤ b ^ f.nat_degree * abs (eval ((a : ℝ) / b) (f.map (algebra_map ℤ ℝ))) :=
begin
  obtain ⟨ev, bi, bu, hF⟩ := @denoms_clearable_nat_degree ℤ ℝ _ _ b (1 / b : ℝ) (algebra_map ℤ ℝ)
    f a (by { rw [eq_int_cast, one_div_mul_cancel], exact (ne_of_gt b0) }),
  obtain Fa := congr_arg abs hF,
  rw [eq_one_div_of_mul_eq_one_left bu, eq_int_cast, eq_int_cast, abs_mul,
    (abs_of_pos (pow_pos b0 _)), one_div, eq_int_cast] at Fa,
  rw [div_eq_mul_inv, ← Fa],
  apply_mod_cast int.le_of_lt_add_one ((lt_add_iff_pos_left 1).mpr (abs_pos.mpr (λ F0, fab _))),
  rw [eq_one_div_of_mul_eq_one_left bu, F0, one_div, eq_int_cast, int.cast_zero, zero_eq_mul] at hF,
  cases hF with hF hF,
  { exact (not_le.mpr b0 (le_of_eq (pow_eq_zero hF))).elim },
  { exact hF }
end

end polynomial

section inequality_and_intervals

lemma le_mul_of_le_and {R : Type*} [linear_ordered_semiring R] {a b : R} (c : R)
  (ha   : 1 ≤ a)
  (key  : b ≤ 1 → 1 ≤ a * c ∧ c ≤ b) :
  1 ≤ a * b :=
begin
  by_cases A : b ≤ 1,
  { exact le_trans (key A).1 ((mul_le_mul_left (lt_of_lt_of_le zero_lt_one ha)).mpr (key A).2) },
  { rw ← mul_one (1 : R),
    exact mul_le_mul ha (le_of_lt (not_le.mp A)) zero_le_one (le_trans zero_le_one ha) }
end

lemma mem_Icc_of_abs_le {R : Type*} [linear_ordered_add_comm_group R]
  {x y z : R} (h : abs (x - y) ≤ z) : y ∈ Icc (x - z) (x + z) :=
⟨sub_le.mp (abs_le.mp h).2, neg_le_sub_iff_le_add.mp (abs_le.mp h).1⟩

lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R]
  {x y z : R} : abs (x - y) ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
⟨mem_Icc_of_abs_le, λ hy, abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr hy.2, sub_le.mp hy.1⟩⟩

end inequality_and_intervals

--namespace is_liouville

open polynomial metric

lemma with_metr_max {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ} {n : ℕ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε →
    (1 : ℝ) ≤ (d a) ^ n * dist (f α) (f (j z a))) :
  ∃ e : ℝ, 0 < e ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) ^ n * (dist α (j z a) * e) :=
begin
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr e0)),
  refine ⟨max (1 / ε) M, me0, λ z a, _⟩,
  refine le_mul_of_le_and (dist (f α) (f (j z a))) (one_le_pow_of_one_le (d0 a) _) (λ p, _),
  have jd : j z a ∈ closed_ball α ε := mem_closed_ball'.mp
    (le_trans ((le_div_iff me0).mpr p) ((one_div_le me0 e0).mpr (le_max_left _ _))),
  exact ⟨L jd, le_trans (B jd) (mul_le_mul_of_nonneg_left (le_max_right (1 / ε) M) dist_nonneg)⟩,
end

lemma exists_pos_real_of_irrational_root {α : ℝ} (ha : irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b.succ) ^ f.nat_degree * (abs (α - (a / (b.succ))) * ε) :=
begin
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
  have ami : function.injective (algebra_map ℤ ℝ) :=
    λ _ _ A, by simpa only [ring_hom.eq_int_cast, int.cast_inj] using A,
  obtain fR0 : fR ≠ 0 := by simpa using (map_injective (algebra_map ℤ ℝ) ami).ne f0,
  have ar : α ∈ (fR.roots.to_finset : set ℝ) := finset.mem_coe.mpr (multiset.mem_to_finset.mpr $
    (mem_roots (fR0)).mpr (is_root.def.mpr fa)),
  obtain ⟨ζ, z0, U⟩ :=
    @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar,
  obtain ⟨xm, ⟨h_x_max_range, hM⟩⟩ := is_compact.exists_forall_ge (@compact_Icc (α - ζ) (α + ζ))
    ⟨α, le_of_lt $ sub_lt_self α z0, le_of_lt $ lt_add_of_pos_right α z0⟩
    (continuous_abs.comp fR.derivative.continuous_aeval).continuous_on,
  apply @with_metr_max ℤ ℕ ℝ _ _ _ (λ y, eval y fR) α ζ (abs (eval xm fR.derivative)) _ _ z0
    (λ y hy, _) (λ z a hq, _),
  { exact (λ a : ℕ, (le_add_iff_nonneg_left _).mpr a.cast_nonneg) }, --simp
  { rw [mul_comm],
    rw [closed_ball_Icc] at hy,
    refine convex.norm_image_sub_le_of_norm_deriv_le (λ _ _, fR.differentiable_at)
      (λ y h, by { rw fR.deriv, exact hM _ h }) (convex_Icc _ _) hy (mem_Icc_of_abs_le _),
    exact @mem_closed_ball_self ℝ _ α ζ (le_of_lt z0) },
  { show (1 : ℝ) ≤ (a + 1) ^ f.nat_degree * abs (eval α fR - eval (z / (a + 1)) fR),
    rw [fa, zero_sub, abs_neg],
    refine @one_le_denom_pow_eval_rat f z (a + 1) (by exact_mod_cast a.succ_pos) (λ hy, _),
    refine (irrational_iff_ne_rational α).mp ha z (a + 1) (eq.symm (mem_singleton_iff.mp _)),
    rw ← U,
    refine ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩,
    exact (mem_roots (fR0)).mpr (is_root.def.mpr hy) },
end

open real

theorem transcendental_of_is_liouville {x : ℝ} (liouville_x : is_liouville x) :
  is_transcendental ℤ x :=
begin
  rintros ⟨f : polynomial ℤ, f0, ef0⟩,
  replace ef0 : (f.map (algebra_map ℤ ℝ)).eval x = 0, { rw aeval_def at ef0, rwa [eval_map] },
  obtain ⟨A, hA, h⟩ :=
    exists_pos_real_of_irrational_root (irrational_of_is_liouville liouville_x) f0 ef0,
  rcases pow_unbounded_of_one_lt A (lt_add_one 1) with ⟨r, hn⟩,
  obtain ⟨a, b, b1, -, a1⟩ := liouville_x (r + f.nat_degree),
  have b0 : (0 : ℝ) < b := lt_trans zero_lt_one (by exact_mod_cast b1),
  have : (b : ℝ) ^ f.nat_degree * abs (x - a / b) < 1 / A,
  { refine pow_mul_lt_c (one_div_pos.mpr hA) (zero_lt_two) _ ((lt_div_iff' (pow_pos b0 _)).mp a1) _,
    { exact_mod_cast int.add_one_le_iff.mpr b1 },
    { rw [mul_one_div, (le_div_iff hA), one_mul],
      exact le_of_lt hn } },
  refine lt_irrefl ((b : ℝ) ^ f.nat_degree * abs (x - ↑a / ↑b)) (lt_of_lt_of_le this _),
  lift b to ℕ using le_trans zero_le_one (le_of_lt b1),
  specialize h a b.pred,
  rwa [nat.succ_pred_eq_of_pos (lt_trans zero_lt_one _), ← mul_assoc, ← (div_le_iff hA)] at h,
  exact_mod_cast b1,
end
