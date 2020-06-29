/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.basic
import analysis.specific_limits
import tactic.noncomm_ring

/-!
# The group of units of a normed ring

In this file we prove that the group of units of a complete normed ring is an open subset of the
ring.
-/

noncomputable theory

variables {α : Type*} [normed_ring α] [complete_space α]

/-- In a normed ring, an element `x` of distance less than `1` from `1` is a unit.  Here we
construct its `units` structure.  -/
def perturbation_unit (x : α) (h : ∥x∥ < 1) : units α :=
{ val := 1 - x,
  inv := tsum (λ (n : ℕ), x ^ n),
  val_inv := mul_neg_geom_series x h,
  inv_val := geom_series_mul_neg x h }

lemma unit_of_near_unit [nonzero α] (x : units α) (y : α)
  (h : ∥y - x∥ < ∥((x⁻¹:units α):α)∥⁻¹) : is_unit y :=
begin
  have hpos : 0 < ∥((x⁻¹:units α):α)∥ := norm_pos x⁻¹,
  have hrad : ∥((x⁻¹:units α):α) * (x - y)∥ < 1,
  { calc ∥((x⁻¹:units α):α) * ((x:α) - y)∥
        ≤ ∥((x⁻¹:units α):α)∥ * ∥(x:α) - y∥           : norm_mul_le x.inv _
    ... = ∥((x⁻¹:units α):α)∥ * ∥y - x∥               : by rw [←neg_sub, norm_neg]
    ... < ∥((x⁻¹:units α):α)∥ * ∥((x⁻¹:units α):α)∥⁻¹ : by nlinarith [h, hpos]
    ... = 1                                          : mul_inv_cancel (by linarith [hpos]) },
  use x * (perturbation_unit _ hrad),
  unfold perturbation_unit,
  noncomm_ring, simp,
end

/-- The group of units of a complete normed ring is an open subset of the ring. -/
lemma units_open : is_open (is_unit : set α) :=
begin
  rcases subsingleton_or_nonzero α with _i|_i, resetI,
  { exact is_open_discrete is_unit },
  { apply metric.is_open_iff.mpr,
    rintros x' ⟨x, h⟩,
    refine ⟨∥((x⁻¹:units α):α)∥⁻¹, inv_pos.mpr (@norm_pos α _ _i x⁻¹), _⟩,
    intros y hy,
    rw [metric.mem_ball, dist_eq_norm, ←h] at hy,
    exact @unit_of_near_unit α _ _ _i x y hy },
end
