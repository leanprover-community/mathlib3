/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import data.real.irrational
import analysis.calculus.mean_value
import topology.algebra.polynomial
import ring_theory.algebraic
import data.polynomial.denoms_clearable
/-!
# Liouville's theorem
This file will contain a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

At the moment, it contains the definition of a Liouville number and a proof that Liouville
numbers are irrational.

The commented imports below will appear as they are needed.  I (Damiano) leave them here for
ease of reference.
--import data.polynomial.denoms_clearable
--import ring_theory.algebraic
--import topology.algebra.polynomial
--import analysis.calculus.mean_value
-/

section irrational

/--
A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
def liouville (x : ℝ) := ∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ abs (x - a / b) < 1 / b ^ n

namespace liouville

lemma irrational {x : ℝ} (h : liouville x) : irrational x :=
begin
  rintros ⟨⟨a, b, bN0, cop⟩, rfl⟩,
  change (liouville (a / b)) at h,
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩,
  have qR0 : (0 : ℝ) < q := int.cast_pos.mpr (zero_lt_one.trans q1),
  have b0 : (b : ℝ) ≠ 0 := ne_of_gt (nat.cast_pos.mpr bN0),
  have bq0 : (0 : ℝ) < b * q := mul_pos (nat.cast_pos.mpr bN0) qR0,
  replace a1 : abs (a * q - b * p) * q ^ (b + 1) < b * q, by
    rwa [div_sub_div _ _ b0 (ne_of_gt qR0), abs_div, div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0))
      (pow_pos qR0 _), abs_of_pos bq0, one_mul, ← int.cast_pow, ← int.cast_mul, ← int.cast_coe_nat,
      ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, ← int.cast_abs, ← int.cast_mul, int.cast_lt]
        at a1,
  replace a0 : ¬a * q - ↑b * p = 0, by
    rwa [ne.def, div_eq_div_iff b0 (ne_of_gt qR0), mul_comm ↑p, ← sub_eq_zero_iff_eq,
      ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, int.cast_eq_zero] at a0,
  lift q to ℕ using (zero_lt_one.trans q1).le,
  have ap : 0 < abs (a * ↑q - ↑b * p) := abs_pos.mpr a0,
  lift (abs (a * ↑q - ↑b * p)) to ℕ using (abs_nonneg (a * ↑q - ↑b * p)),
  rw [← int.coe_nat_mul, ← int.coe_nat_pow, ← int.coe_nat_mul, int.coe_nat_lt] at a1,
  exact not_le.mpr a1 (nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le,
end

end liouville

open polynomial metric set real ring_hom

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

lemma exists_pos_real_of_irrational_root {α : ℝ} (ha : _root_.irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b.succ) ^ f.nat_degree * (abs (α - (a / (b.succ))) * ε) :=
begin
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
  obtain fR0 : fR ≠ 0 := λ fR0, (map_injective (algebra_map ℤ ℝ) (λ _ _ A, int.cast_inj.mp A)).ne
    f0 (fR0.trans (polynomial.map_zero _).symm),
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

end irrational
