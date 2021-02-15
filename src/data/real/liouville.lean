/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import analysis.calculus.mean_value
import data.polynomial.denoms_clearable
import data.real.irrational
import ring_theory.algebraic
import topology.algebra.polynomial
/-!
# Liouville's theorem
This file will contain a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

At the moment, it contains the definition of a Liouville number, a proof that Liouville
numbers are irrational and two technical lemmas.
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
  -- By contradiction, `x = a / b`, with `a ∈ ℤ`, `0 < b ∈ ℕ` is a Liouville number,
  rintros ⟨⟨a, b, bN0, cop⟩, rfl⟩,
  -- clear up the mess of constructions of rationals
  change (liouville (a / b)) at h,
  -- Since `a / b` is a Liouville number, there are `p, q ∈ ℤ`, with `q1 : 1 < q`,
  -- `a0 : a / b ≠ p / q` and `a1 : abs (a / b - p / q) < 1 / q ^ (b + 1)`
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩,
  -- A few useful inequalities
  have qR0 : (0 : ℝ) < q := int.cast_pos.mpr (zero_lt_one.trans q1),
  have b0 : (b : ℝ) ≠ 0 := ne_of_gt (nat.cast_pos.mpr bN0),
  have bq0 : (0 : ℝ) < b * q := mul_pos (nat.cast_pos.mpr bN0) qR0,
  -- At a1, clear denominators...
  replace a1 : abs (a * q - b * p) * q ^ (b + 1) < b * q, by
    rwa [div_sub_div _ _ b0 (ne_of_gt qR0), abs_div, div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0))
      (pow_pos qR0 _), abs_of_pos bq0, one_mul,
      -- ... and revert to integers
       ← int.cast_pow, ← int.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul,
       ← int.cast_sub, ← int.cast_abs, ← int.cast_mul, int.cast_lt] at a1,
  -- At a0, clear denominators...
  replace a0 : ¬a * q - ↑b * p = 0, by
    rwa [ne.def, div_eq_div_iff b0 (ne_of_gt qR0), mul_comm ↑p, ← sub_eq_zero_iff_eq,
      -- ... and revert to integers
      ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_mul, ← int.cast_sub, int.cast_eq_zero] at a0,
  -- Actually, `q` is a natural number
  lift q to ℕ using (zero_lt_one.trans q1).le,
  -- Looks innocuous, but we now have an integer with non-zero absolute value: this is at
  --least one away from zero.  The gain here is what gets the proof going.
  have ap : 0 < abs (a * ↑q - ↑b * p) := abs_pos.mpr a0,
  -- Actually, the absolute value of an integer is a natural number
  lift (abs (a * ↑q - ↑b * p)) to ℕ using (abs_nonneg (a * ↑q - ↑b * p)),
  -- At a1, revert to natural numbers
  rw [← int.coe_nat_mul, ← int.coe_nat_pow, ← int.coe_nat_mul, int.coe_nat_lt] at a1,
  -- Recall this is by contradiction: we obtained the inequality `b * q ≤ x * q ^ (b + 1)`, so
  -- we are done.
  exact not_le.mpr a1 (nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le,
end

end liouville

open polynomial metric set real ring_hom

/-- Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a "cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are interested in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 / A`: the intuition
is that approximating well `α` with the points in the image of `j` should come at a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the distance.
The second hypothesis is specific to the Liouville argument and provides the missing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a  = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
lemma exists_one_le_pow_mul_dist {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
-- denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
-- clear denominators
  (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε → 1 ≤ (d a) * dist (f α) (f (j z a))) :
  ∃ A : ℝ, 0 < A ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) * (dist α (j z a) * A) :=
begin
  -- A useful inequality to keep at hand
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr e0)),
  -- The maximum between `1 / ε` and `M` works
  refine ⟨max (1 / ε) M, me0, λ z a, _⟩,
  -- First, let's deal with the easy case in which we are far away from `α`
  by_cases dm1 : 1 ≤ (dist α (j z a) * max (1 / ε) M),
  { exact one_le_mul_of_one_le_of_one_le (d0 a) dm1 },
  { -- `j z a = z / (a + 1)`: we prove that this ratio is close to `α`
    have : j z a ∈ closed_ball α ε,
    { refine mem_closed_ball'.mp (le_trans _ ((one_div_le me0 e0).mpr (le_max_left _ _))),
      exact ((le_div_iff me0).mpr (not_le.mp dm1).le) },
    -- use the "separation from `1`" (assumption `L`) for numerators,
    refine (L this).trans _,
    -- remove a common factor and use the Lipschitz assumption `B`
    refine mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a)),
    exact mul_le_mul_of_nonneg_left (le_max_right _ M) dist_nonneg }
end

lemma exists_pos_real_of_irrational_root {α : ℝ} (ha : irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ A : ℝ, 0 < A ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b + 1) ^ f.nat_degree * (abs (α - (a / (b + 1))) * A) :=
begin
  -- `fR` is `f` viewed as a polynomial with `ℝ` coefficients.
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
  -- `fR` is non-zero, since `f` is non-zero.
  obtain fR0 : fR ≠ 0 := λ fR0, (map_injective (algebra_map ℤ ℝ) (λ _ _ A, int.cast_inj.mp A)).ne
    f0 (fR0.trans (polynomial.map_zero _).symm),
  -- reformulating assumption `fa`: `α` is a root of `fR`.
  have ar : α ∈ (fR.roots.to_finset : set ℝ) :=
    finset.mem_coe.mpr (multiset.mem_to_finset.mpr ((mem_roots fR0).mpr (is_root.def.mpr fa))),
  -- Since the polynomial `fR` has finitely many roots, there is a closed interval centered at `α`
  -- such that `α` is the only root of `fR` in the interval.
  obtain ⟨ζ, z0, U⟩ : ∃ ζ > 0, closed_ball α ζ ∩ (fR.roots.to_finset) = {α} :=
    @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar,
  -- Since `fR` is continuous, it is bounded on the interval above.
  obtain ⟨xm, -, hM⟩ : ∃ (xm : ℝ) (H : xm ∈ Icc (α - ζ) (α + ζ)), ∀ (y : ℝ),
    y ∈ Icc (α - ζ) (α + ζ) → abs (fR.derivative.eval y) ≤ abs (fR.derivative.eval xm) :=
    is_compact.exists_forall_ge compact_Icc
    ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
    (continuous_abs.comp fR.derivative.continuous_aeval).continuous_on,
  -- Use the key lemma `exists_one_le_pow_mul_dist`: we are left to show that ...
  refine @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (λ y, fR.eval y) α ζ
    (abs (fR.derivative.eval xm)) _ z0 (λ y hy, _) (λ z a hq, _),
  -- 1: the denominators are positive -- essentially by definition;
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _ },
  -- 2: the polynomial `fR` is Lipschitz at `α` -- as its derivative continuous;
  { rw mul_comm,
    rw closed_ball_Icc at hy,
    -- apply the Mean Value Theorem: the bound on the derivative comes from differentiability.
    refine convex.norm_image_sub_le_of_norm_deriv_le (λ _ _, fR.differentiable_at)
      (λ y h, by { rw fR.deriv, exact hM _ h }) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _),
    exact @mem_closed_ball_self ℝ _ α ζ (le_of_lt z0) },
  -- 3: the weird inequality of Liouville type with powers of the denominators.
  { show 1 ≤ (a + 1 : ℝ) ^ f.nat_degree * abs (eval α fR - eval (z / (a + 1)) fR),
    rw [fa, zero_sub, abs_neg],
    -- key observation: the right-hand side of the inequality is an *integer*.  Therefore,
    -- if its absolute value is not at least one, then it vanishes.  Proceed by contradiction
    refine one_le_pow_mul_abs_eval_div (int.coe_nat_succ_pos a) (λ hy, _),
    -- As the evaluation of the polynomial vanishes, we found a root of `fR` that is rational.
    -- We know that `α` is the only root of `fR` in our interval, and `α` is irrational:
    -- follow your nose.
    refine (irrational_iff_ne_rational α).mp ha z (a + 1) ((mem_singleton_iff.mp _).symm),
    refine U.subset _,
    refine ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩,
    exact (mem_roots fR0).mpr (is_root.def.mpr hy) }
end

end irrational
