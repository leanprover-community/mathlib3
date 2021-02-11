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

namespace real

-- PR liouville_def contains the definition `is_liouville` and the lemma that
-- a liouville number is irrational
/--
A Liouville number `x` is a number such that for every natural number `n`, there exists `a, b ∈ ℤ`
with `b > 1` such that `0 < |x - a/b| < 1/bⁿ`.
-/
def is_liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ,
  1 < b ∧ x ≠ a / b ∧ abs (x - a / b) < 1 / b ^ n

lemma irrational_of_is_liouville {x : ℝ} (h : is_liouville x) : irrational x :=
begin
  rintros ⟨⟨a, b, bN0, cop⟩, rfl⟩,
  change (is_liouville (a / b)) at h,
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩,
  have qR0 : (0 : ℝ) < q := int.cast_pos.mpr (zero_lt_one.trans q1),
  have b0 : (b : ℝ) ≠ 0 := ne_of_gt (nat.cast_pos.mpr bN0),
  have bq0 : (0 : ℝ) < b * q := mul_pos (nat.cast_pos.mpr bN0) qR0,
  rw [div_sub_div _ _ b0 (ne_of_gt qR0), abs_div, div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0))
    (pow_pos qR0 _), abs_of_pos bq0, one_mul] at a1,
  rw [← int.cast_pow, ← int.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul,
    ← int.cast_sub, ← int.cast_abs, ← int.cast_mul, int.cast_lt] at a1,
  rw [ne.def, div_eq_div_iff b0 (ne_of_gt qR0), mul_comm ↑p, ← sub_eq_zero_iff_eq] at a0,
  rw [← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, int.cast_eq_zero] at a0,
  lift q to ℕ using (zero_lt_one.trans q1).le,
  have ap : 0 < abs (a * ↑q - ↑b * p) := abs_pos.mpr a0,
  lift (abs (a * ↑q - ↑b * p)) to ℕ using (abs_nonneg (a * ↑q - ↑b * p)),
  rw [← int.coe_nat_mul, ← int.coe_nat_pow, ← int.coe_nat_mul, int.coe_nat_lt] at a1,
  exact not_le.mpr a1 (nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le,
end

lemma not_liouville_zero : ¬ is_liouville 0 :=
λ h, irrational_of_is_liouville h ⟨0, rat.cast_zero⟩

end real

open set ring_hom real

namespace polynomial

end polynomial

section inequality_and_intervals

/-- This inequality streamlines the argument in `exists_one_le_pow_mul_dist`. -/
lemma le_mul_of_le_and {R : Type*} [linear_ordered_semiring R] {a b : R} (c : R)
  (ha   : 1 ≤ a)
  (key  : b ≤ 1 → 1 ≤ a * c ∧ c ≤ b) :
  1 ≤ a * b :=
begin
  by_cases A : b ≤ 1,
  { exact (key A).1.trans ((mul_le_mul_left (zero_lt_one.trans_le ha)).mpr (key A).2) },
  { rw ← mul_one (1 : R),
    exact mul_le_mul ha (not_le.mp A).le zero_le_one (zero_le_one.trans ha) }
end

lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R] {x y z : R} :
  abs (x - y) ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
⟨λ h, ⟨sub_le.mp (abs_le.mp h).2, neg_le_sub_iff_le_add.mp (abs_le.mp h).1⟩,
 λ hy, abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr hy.2, sub_le.mp hy.1⟩⟩

end inequality_and_intervals

--namespace is_liouville

open polynomial metric

/-- This lemma collects the properties needed to prove `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d n = n`, `j z n  = z / (n + 1)`, `f ∈ ℤ[x]`, `α` is an irrational root of `f`, `ε` is
small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is the degree of the
polynomial `f`.
-/
lemma exists_one_le_pow_mul_dist {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ} {n : ℕ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε → 1 ≤ (d a) ^ n * dist (f α) (f (j z a))) :
  ∃ e : ℝ, 0 < e ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) ^ n * (dist α (j z a) * e) :=
begin
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr e0)),
  refine ⟨max (1 / ε) M, me0, λ z a, _⟩,
  refine le_mul_of_le_and (dist (f α) (f (j z a))) (one_le_pow_of_one_le (d0 a) _) (λ p, _),
  refine ⟨L _, (B _).trans (mul_le_mul_of_nonneg_left (le_max_right (1 / ε) M) dist_nonneg)⟩;
  { refine mem_closed_ball'.mp _,
    exact ((le_div_iff me0).mpr p).trans ((one_div_le me0 e0).mpr (le_max_left _ _)) }
end

/-- This lemma collects the properties needed to prove `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = a ^ f.nat_degree`, `j z a  = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
lemma exists_one_le_pow_mul_dist_no_pow {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε → 1 ≤ (d a) * dist (f α) (f (j z a))) :
  ∃ e : ℝ, 0 < e ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) * (dist α (j z a) * e) :=
begin
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr e0)),
  refine ⟨max (1 / ε) M, me0, λ z a, _⟩,
  refine le_mul_of_le_and (dist (f α) (f (j z a))) ((d0) _) (λ p, _),
  refine ⟨L _, (B _).trans (mul_le_mul_of_nonneg_left (le_max_right (1 / ε) M) dist_nonneg)⟩;
  { refine mem_closed_ball'.mp _,
    exact ((le_div_iff me0).mpr p).trans ((one_div_le me0 e0).mpr (le_max_left _ _)) }
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
  have ar : α ∈ (fR.roots.to_finset : set ℝ) :=
    finset.mem_coe.mpr (multiset.mem_to_finset.mpr ((mem_roots fR0).mpr (is_root.def.mpr fa))),
  obtain ⟨ζ, z0, U⟩ :=
    @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar,
  obtain ⟨xm, ⟨h_x_max_range, hM⟩⟩ := is_compact.exists_forall_ge (@compact_Icc (α - ζ) (α + ζ))
    ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
    (continuous_abs.comp fR.derivative.continuous_aeval).continuous_on,
  refine @exists_one_le_pow_mul_dist_no_pow ℤ ℕ ℝ _ _ _ (λ y, fR.eval y) α ζ
    (abs (fR.derivative.eval xm)) _ z0 (λ y hy, _) (λ z a hq, _),
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _ }, --simp
  { rw mul_comm,
    rw closed_ball_Icc at hy,
    refine convex.norm_image_sub_le_of_norm_deriv_le (λ _ _, fR.differentiable_at)
      (λ y h, by { rw fR.deriv, exact hM _ h }) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _),
    exact @mem_closed_ball_self ℝ _ α ζ (le_of_lt z0) },
  { show 1 ≤ (a + 1 : ℝ) ^ f.nat_degree * abs (eval α fR - eval (z / (a + 1)) fR),
    rw [fa, zero_sub, abs_neg],
    refine one_le_pow_mul_abs_eval_div (int.coe_nat_succ_pos a) (λ hy, _),
    refine (irrational_iff_ne_rational α).mp ha z (a + 1) ((mem_singleton_iff.mp _).symm),
    rw ← U,
    refine ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩,
    exact (mem_roots fR0).mpr (is_root.def.mpr hy) }
end

theorem transcendental_of_is_liouville {x : ℝ} (liouville_x : is_liouville x) :
  is_transcendental ℤ x :=
begin
  rintros ⟨f : polynomial ℤ, f0, ef0⟩,
  replace ef0 : (f.map (algebra_map ℤ ℝ)).eval x = 0, { rwa [aeval_def, ← eval_map] at ef0 },
  obtain ⟨A, hA, h⟩ :=
    exists_pos_real_of_irrational_root (irrational_of_is_liouville liouville_x) f0 ef0,
  rcases pow_unbounded_of_one_lt A (lt_add_one 1) with ⟨r, hn⟩,
  obtain ⟨a, b, b1, -, a1⟩ := liouville_x (r + f.nat_degree),
  have b0 : (0 : ℝ) < b := zero_lt_one.trans (by { rw ← int.cast_one, exact int.cast_lt.mpr b1 }),
  refine lt_irrefl ((b : ℝ) ^ f.nat_degree * abs (x - ↑a / ↑b)) _,
  rw [lt_div_iff' (pow_pos b0 _), pow_add, mul_assoc] at a1,
  refine ((_  : (b : ℝ) ^ f.nat_degree * abs (x - a / b) < 1 / A).trans_le _),
  { refine (lt_div_iff' hA).mpr _,
    refine lt_of_le_of_lt _ a1,
    refine mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg b0.le _) (abs_nonneg _)),
    refine hn.le.trans _,
    refine pow_le_pow_of_le_left zero_le_two _ _,
    exact int.cast_two.symm.le.trans (int.cast_le.mpr (int.add_one_le_iff.mpr b1)) },
  { lift b to ℕ using zero_le_one.trans b1.le,
    specialize h a b.pred,
    rwa [nat.succ_pred_eq_of_pos (zero_lt_one.trans _), ← mul_assoc, ← (div_le_iff hA)] at h,
    exact int.coe_nat_lt.mp b1 }
end
