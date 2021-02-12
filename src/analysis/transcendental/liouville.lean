/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial.denoms_clearable
import ring_theory.algebraic
import topology.algebra.polynomial
import analysis.calculus.mean_value
import data.real.liouville
/-!
# Liouville's theorem

This file contains the proof of Liouville's theorem stating that all Liouville numbers are
transcendental.
-/

open set ring_hom real

section inequality_and_intervals

lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R] {x y z : R} :
  abs (x - y) ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
⟨λ h, ⟨sub_le.mp (abs_le.mp h).2, neg_le_sub_iff_le_add.mp (abs_le.mp h).1⟩,
 λ hy, abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr hy.2, sub_le.mp hy.1⟩⟩

end inequality_and_intervals

--namespace is_liouville

open polynomial metric

/-- This lemma collects the properties needed to prove `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = a ^ f.nat_degree`, `j z a  = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
lemma exists_one_le_pow_mul_dist {Z N R : Type*} [metric_space R]
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
  by_cases dm1 : 1 ≤ (dist α (j z a) * max (1 / ε) M),
  { exact one_le_mul_of_one_le_of_one_le (d0 a) dm1 },
  { have : j z a ∈ closed_ball α ε,
    { refine mem_closed_ball'.mp (le_trans _ ((one_div_le me0 e0).mpr (le_max_left _ _))),
      exact ((le_div_iff me0).mpr (not_le.mp dm1).le) },
    refine (L this).trans _,
    refine mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a)),
    exact mul_le_mul_of_nonneg_left (le_max_right _ M) dist_nonneg }
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
  refine @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (λ y, fR.eval y) α ζ
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

theorem is_liouville.transcendental {x : ℝ} (liouville_x : is_liouville x) :
  is_transcendental ℤ x :=
begin
  rintros ⟨f : polynomial ℤ, f0, ef0⟩,
  replace ef0 : (f.map (algebra_map ℤ ℝ)).eval x = 0, { rwa [aeval_def, ← eval_map] at ef0 },
  obtain ⟨A, hA, h⟩ :=
    exists_pos_real_of_irrational_root liouville_x.irrational f0 ef0,
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

lemma not_liouville_zero : ¬ is_liouville 0 :=
λ h, h.irrational ⟨0, rat.cast_zero⟩
