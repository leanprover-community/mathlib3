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

end inequality_and_intervals

--namespace is_liouville

open polynomial metric

-- the next three lemmas are in PR #6201, liouville_exists_root
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
  -- A useful inequality to keep at hand
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr e0)),
  -- The maximum between `1 / ε` and `M` works
  refine ⟨max (1 / ε) M, me0, λ z a, _⟩,
  -- First, let's deal with the easy case in which we are far away from `α`
  by_cases dm1 : 1 ≤ (dist α (j z a) * max (1 / ε) M),
  { exact one_le_mul_of_one_le_of_one_le (d0 a) dm1 },
  { -- `j z a = z / (a + 1)`: we prove that this ratio number is close to `α`
    have : j z a ∈ closed_ball α ε,
    { refine mem_closed_ball'.mp (le_trans _ ((one_div_le me0 e0).mpr (le_max_left _ _))),
      exact ((le_div_iff me0).mpr (not_le.mp dm1).le) },
    -- use the separation after clearing denominators, assumption `L`
    refine (L this).trans _,
    -- remove a common factor and use Lipschitz assumption `B`
    refine mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a)),
    exact mul_le_mul_of_nonneg_left (le_max_right _ M) dist_nonneg }
end

lemma mem_Icc_iff_abs_le {R : Type*} [linear_ordered_add_comm_group R] {x y z : R} :
  abs (x - y) ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
⟨λ h, ⟨sub_le.mp (abs_le.mp h).2, neg_le_sub_iff_le_add.mp (abs_le.mp h).1⟩,
 λ hy, abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr hy.2, sub_le.mp hy.1⟩⟩

lemma exists_pos_real_of_irrational_root {α : ℝ} (ha : irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b.succ) ^ f.nat_degree * (abs (α - (a / (b.succ))) * ε) :=
begin
  -- fR is f viewed as a polynomial with ℝ coefficients.
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
  -- fR is non-zero, since f is non-zero.
  obtain fR0 : fR ≠ 0 := λ fR0, (map_injective (algebra_map ℤ ℝ) (λ _ _ A, int.cast_inj.mp A)).ne
    f0 (fR0.trans (polynomial.map_zero _).symm),
  -- reformulating assumption fa: α is a root of fR.
  have ar : α ∈ (fR.roots.to_finset : set ℝ) :=
    finset.mem_coe.mpr (multiset.mem_to_finset.mpr ((mem_roots fR0).mpr (is_root.def.mpr fa))),
  -- Since the fR has finitely many roots, there is a closed interval centered at α such that α is
  -- the only root of fR in the interval.
  obtain ⟨ζ, z0, U⟩ : ∃ ζ > 0, closed_ball α ζ ∩ (fR.roots.to_finset) = {α} :=
    @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar,
  -- Since fR is continuous, it is bounded on the interval above.
  obtain ⟨xm, -, hM⟩ : ∃ (xm : ℝ) (H : xm ∈ Icc (α - ζ) (α + ζ)), ∀ (y : ℝ),
    y ∈ Icc (α - ζ) (α + ζ) → abs (eval y (derivative fR)) ≤ abs (eval xm (derivative fR)) :=
    is_compact.exists_forall_ge (compact_Icc)
    ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
    (continuous_abs.comp fR.derivative.continuous_aeval).continuous_on,
  -- Use the key lemma `exists_one_le_pow_mul_dist`: we are left to show that
  -- 1: denominators are positive
  -- 2: the polynomial fR is Lipschitz at α
  -- 3: the weird inequality of Liouville type with powers of the denominators.
  refine @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (λ y, fR.eval y) α ζ
    (abs (fR.derivative.eval xm)) _ z0 (λ y hy, _) (λ z a hq, _),
  -- 1: the denominators are positive -- essentially by definition;
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _ },
  -- 2: the polynomial fR is Lipschits at α -- as it's derivative continuous;
  { rw mul_comm,
    rw closed_ball_Icc at hy,
    -- apply the Mean value theorem: the bound on the derivative comes from differentiability.
    refine convex.norm_image_sub_le_of_norm_deriv_le (λ _ _, fR.differentiable_at)
      (λ y h, by { rw fR.deriv, exact hM _ h }) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _),
    exact @mem_closed_ball_self ℝ _ α ζ (le_of_lt z0) },
  -- 3: weird, Liouville-like inequality.
  { show 1 ≤ (a + 1 : ℝ) ^ f.nat_degree * abs (eval α fR - eval (z / (a + 1)) fR),
    rw [fa, zero_sub, abs_neg],
    -- key observation: the right-hand side of the inequality is an *integer*.  Therefore,
    -- if its absolute value is not at least one, then it vanishes.  Proceed by contradiction
    refine one_le_pow_mul_abs_eval_div (int.coe_nat_succ_pos a) (λ hy, _),
    -- If the evaluation of the polynomial vanishes, then we found a root of fR that is rational.
    -- We know that α is the only root of fR in our interval, and α is irrational: follow your nose.
    refine (irrational_iff_ne_rational α).mp ha z (a + 1) ((mem_singleton_iff.mp _).symm),
    rw ← U,
    refine ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩,
    exact (mem_roots fR0).mpr (is_root.def.mpr hy) }
end

namespace liouville

theorem transcendental {x : ℝ} (liouville_x : liouville x) :
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

end liouville

#exit

/-
have gen : ∀ e : ℝ, 0 < e → max eb el ≤ e → j z a ∈ closed_ball α e,
    { intros e e0 eM,
      refine mem_closed_ball'.mp _,
      refine ((lt_div_iff me0).mpr (not_le.mp dm1)).le.trans _,
--      refine (one_div_le_one_div me0 mel).mpr (rfl.le.trans (le_max_right _ _)).trans _,
      by_cases lb : el ≤ eb,

      transitivity (1 / (max (1 / el) M)),
      { exact (one_div_le_one_div me0 mel).mpr (rfl.le.trans (le_max_right _ _)) },
      { refine (one_div_le mel e0).mpr _,
        refine le_trans (one_div_le_one_div_of_le el0 (lb.trans _)) (le_max_left _ _),
        exact le_of_max_le_left eM },
      { obtain bl := (not_le.mp lb).le,
      transitivity (1 / (max (1 / eb) M)),
      { refine (one_div_le_one_div me0 meb).mpr _,
        exact max_le (le_max_left _ _) ((le_max_right _ M).trans (le_max_right _ _)) },
      { refine (one_div_le meb e0).mpr _,
        refine le_trans (one_div_le_one_div_of_le eb0 (bl.trans _)) (le_max_left _ _),
        apply le_trans (le_max_right _ _) eM } } },
-/

/-
lemma max_one_div_one_div_iff {R : Type*} [linear_ordered_field R] {a b : R}
  (a0 : 0 < a) (b0 : 0 < b) :
  max (1 / a) (1 / b) = 1 / a ↔ min a b = a :=
begin
  rw [min_eq_left_iff, max_eq_left_iff, one_div_le_one_div b0 a0]
end


lemma one_div_max_eq_min_one_div_one_div {R : Type*} [linear_ordered_field R] {a b : R}
  (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
  1 / max a b = min (1 / a) (1 / b) :=
begin

end
-/

/-- This lemma collects the properties needed to prove `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = a ^ f.nat_degree`, `j z a  = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
lemma exists_one_le_pow_mul_dist_no_repeat {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {M : ℝ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
--  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∃ ε : ℝ, 0 < ε ∧ ∀ {y : R}, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∃ ε : ℝ, 0 < ε ∧ ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε →
    1 ≤ (d a) * dist (f α) (f (j z a))) :
  ∃ ε : ℝ, 0 < ε ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) * (dist α (j z a) * ε) :=
begin
  rcases B with ⟨eb, eb0, B⟩,
  rcases L with ⟨el, el0, L⟩,
  have mebl : 0 < max (1 / eb) (1 / el) := lt_max_iff.mpr (or.inl (one_div_pos.mpr eb0)),
  have me0 : 0 < max M (max (1 / eb) (1 / el)) := mebl.trans_le (le_max_right _ _),
  refine ⟨max M (max (1 / eb) (1 / el)), me0, λ z a, _⟩,
  by_cases dm1 : 1 ≤ dist α (j z a) * max M (max (1 / eb) (1 / el)),
  { exact one_le_mul_of_one_le_of_one_le (d0 a) dm1 },
  { have jb : ∀ e : ℝ, 0 < e → min eb el ≤ e → j z a ∈ closed_ball α e,
    { refine λ e e0 eel, mem_closed_ball'.mp _,
      refine ((lt_div_iff me0).mpr (not_le.mp dm1)).le.trans _,
      refine ((one_div_le_one_div me0 mebl).mpr (le_max_right M _)).trans _,
      refine (one_div_le mebl e0).mpr (le_max_iff.mpr _),
      rwa [one_div_le_one_div e0 eb0, one_div_le_one_div e0 el0, ← min_le_iff] },
    refine (L (jb el el0 (min_le_right eb el))).trans _,
    refine mul_le_mul_of_nonneg_left _ (zero_le_one.trans (d0 a)),
    refine (B (jb eb eb0 (min_le_left eb el))).trans _,
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg }
end


lemma exists_one_le_pow_mul_dist_v_join {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε → 1 ≤ (d a) * dist (f α) (f (j z a))) :
  ∃ e : ℝ, 0 < e ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) * (dist α (j z a) * e) :=
exists_one_le_pow_mul_dist_no_repeat d0 ⟨ε, e0, B⟩ ⟨ε, e0, L⟩







lemma bounded_deriv {α : ℝ} {f : ℝ → ℝ} {M : ℝ} {ε : ℝ} (e0 : 0 ≤ ε)
  (fc : ∀ (x : ℝ), x ∈ closed_ball α ε → ∥deriv f x∥ ≤ M)
  (fd : ∀ (x : ℝ), x ∈ closed_ball α ε → differentiable_at ℝ f x) :
  ∀ {y : ℝ}, y ∈ closed_ball α ε → dist (f α) (f y) ≤ M * (dist α y) :=
begin
  refine λ y yc, le_trans (le_of_eq (dist_eq_norm _ _)) _,
  refine convex.norm_image_sub_le_of_norm_deriv_le fd fc (convex_closed_ball α ε) yc _,
  exact mem_closed_ball_self e0,
end

lemma bounded_deriv_exists {α : ℝ} {f : ℝ → ℝ} {ε : ℝ} (e0 : 0 ≤ ε)
  (fc : ∃ M : ℝ, ∀ (x : ℝ), x ∈ closed_ball α ε → ∥deriv f x∥ ≤ M)
  (fd : ∀ (x : ℝ), x ∈ closed_ball α ε → differentiable_at ℝ f x) :
  ∃ M : ℝ, ∀ {y : ℝ}, y ∈ closed_ball α ε → dist (f α) (f y) ≤ M * (dist α y) :=
begin
  cases fc with M fc,
  refine ⟨M, λ y yc, le_trans (le_of_eq (dist_eq_norm _ _)) _⟩,
  refine convex.norm_image_sub_le_of_norm_deriv_le fd fc (convex_closed_ball α ε) yc _,
  exact mem_closed_ball_self e0,
end

lemma exists_pos_real_of_irrational_root_v {α : ℝ} (ha : irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b.succ) ^ f.nat_degree * (abs (α - (a / (b.succ))) * ε) :=
begin
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
  apply @exists_one_le_pow_mul_dist_no_repeat ℤ ℕ ℝ _ _ _ (λ x, fR.eval x),
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left (1 : ℝ)).mpr a.cast_nonneg) _ },
  { refine ⟨1, zero_lt_one, _⟩, --λ y yc,
--  change dist ((λ (x : ℝ), eval x fR) α) ((λ (x : ℝ), eval x fR) y) ≤ dist α y * _,
  rotate,
  intros y yc,
  rw [mul_comm (dist α _) _, dist_eq_norm],
  apply bounded_deriv zero_le_one _ (λ x hx, polynomial.differentiable_at fR) yc,
  sorry,sorry,
/-
  apply convex.norm_image_sub_le_of_norm_deriv_le,

  refine λ x hx, polynomial.differentiable_at fR,
  rw [mem_closed_ball, dist_eq, abs_le] at yc,
  cases yc,
  apply convex.norm_image_sub_le_of_norm_deriv_le _ _ (convex_Icc (α - 1) (α + 1)),

    refine ⟨_, _⟩;
    linarith,
    refine ⟨_, _⟩;
    linarith,
    apply_instance,
    intros y hy,exact polynomial.differentiable_at fR,

    intros z,
  apply is_compact.exists_forall_ge
-/
  },
  {
    refine ⟨1, zero_lt_one, λ z a zac, _⟩,
  { show 1 ≤ (a + 1 : ℝ) ^ f.nat_degree * abs (eval α fR - eval (z / (a + 1)) fR),
    rw [fa, zero_sub, abs_neg],
    refine one_le_pow_mul_abs_eval_div (int.coe_nat_succ_pos a) (λ hy, _),
    refine (irrational_iff_ne_rational α).mp ha z (a + 1) ((mem_singleton_iff.mp _).symm),
    rw ← U,
    refine ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩,
    exact (mem_roots fR0).mpr (is_root.def.mpr hy) }

  },
end





/--  Works, but repeats an inequality. -/
lemma exists_one_le_pow_mul_dist {Z N R : Type*} [metric_space R]
  {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R} {M : ℝ}
--denominators are positive
  (d0 : ∀ (a : N), 1 ≤ d a)
--  (e0 : 0 < ε)
--function is Lipschitz at α
  (B : ∃ ε : ℝ, 0 < ε ∧ ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ (dist α y) * M)
--clear denominators
  (L : ∃ ε : ℝ, 0 < ε ∧ ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε →
    1 ≤ (d a) * dist (f α) (f (j z a))) :
  ∃ ε : ℝ, 0 < ε ∧ ∀ (z : Z), ∀ (a : N), 1 ≤ (d a) * (dist α (j z a) * ε) :=
begin
  rcases B with ⟨eb, eb0, B⟩,
  rcases L with ⟨el, el0, L⟩,
  have mel : 0 < max (1 / el) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr el0)),
  have meb : 0 < max (1 / eb) M := lt_max_iff.mpr (or.inl (one_div_pos.mpr eb0)),
  have me0 : 0 < max (1 / eb) (max (1 / el) M) := lt_max_iff.mpr (or.inr mel),
  refine ⟨max (1 / eb) (max (1 / el) M), me0, λ z a, _⟩,
  by_cases dm1 : 1 ≤ (dist α (j z a) * max (1 / eb) (max (1 / el) M)),
  { exact one_le_mul_of_one_le_of_one_le (d0 a) dm1 },
  { refine (@L z a _).trans _,
    { refine mem_closed_ball'.mp _,
      refine ((lt_div_iff me0).mpr (not_le.mp dm1)).le.trans _,
      transitivity (1 / (max (1 / el) M)),
      { exact (one_div_le_one_div me0 mel).mpr (rfl.le.trans (le_max_right _ _)) },
      { exact ((one_div_le mel el0).mpr (le_max_left _ _)) } },
    { refine mul_le_mul_of_nonneg_left ((B _).trans _) (zero_le_one.trans (d0 a)),
      { refine mem_closed_ball'.mp _,
        refine ((lt_div_iff me0).mpr (not_le.mp dm1)).le.trans _,
        transitivity (1 / (max (1 / eb) M)),
        { refine (one_div_le_one_div me0 meb).mpr _,
          exact max_le (le_max_left _ _) ((le_max_right _ M).trans (le_max_right _ _)) },
        { refine (one_div_le meb eb0).mpr _,
          refine le_trans rfl.le (le_max_left _ _) } },
      { refine mul_le_mul_of_nonneg_left _ dist_nonneg,
        exact (le_max_right _ _).trans (le_max_right _ _) } } }
end


lemma exists_pos_real_of_irrational_root {α : ℝ} (ha : irrational α)
  {f : polynomial ℤ} (f0 : f ≠ 0) (fa : eval α (map (algebra_map ℤ ℝ) f) = 0):
  ∃ ε : ℝ, 0 < ε ∧
    ∀ (a : ℤ), ∀ (b : ℕ), (1 : ℝ) ≤ (b.succ) ^ f.nat_degree * (abs (α - (a / (b.succ))) * ε) :=
begin
  set fR : polynomial ℝ := map (algebra_map ℤ ℝ) f,
--  obtain F := @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ (λ n, (n + 1) ^ f.nat_degree) (λ a b, a / (b + 1))
--    (λ y, fR.eval y) α _ (_) _ _ (λ y hy, _) (λ z a hq, _),
  refine @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ (λ n, (n + 1) ^ f.nat_degree) (λ a b, a / (b + 1))
    (λ y, fR.eval y) α _ (_) _ _ (λ y hy, _) (λ z a hq, _),
  work_on_goal 2
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left (1 : ℝ)).mpr a.cast_nonneg) _ },

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

lemma exists_one_le_pow_mul_dist_v {Z N R : Type*} [metric_space R]
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

lemma exists_pos_real_of_irrational_root_v_v {α : ℝ} (ha : irrational α)
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
  refine @exists_one_le_pow_mul_dist_v ℤ ℕ ℝ _ _ _ (λ y, fR.eval y) α ζ
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

namespace liouville

theorem transcendental {x : ℝ} (liouville_x : liouville x) :
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

end liouville

#exit

  obtain F := @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ (λ n, (n + 1) ^ f.nat_degree) (λ a b, a / (b + 1))
    (λ y, fR.eval y) α _ (_) _ _ (λ y hy, _) (λ z a hq, _),
  refine @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ (λ n, (n + 1) ^ f.nat_degree) (λ a b, a / (b + 1))
    (λ y, fR.eval y) α _ (_) _ _ (λ y hy, _) (λ z a hq, _),
  work_on_goal 2
  { exact λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left (1 : ℝ)).mpr a.cast_nonneg) _ },

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
