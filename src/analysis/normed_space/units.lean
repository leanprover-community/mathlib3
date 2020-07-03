/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.basic
import analysis.specific_limits
import tactic.noncomm_ring

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The main result is `is_open`:  the group of units of a complete normed ring is an open subset of the
ring.

-/

noncomputable theory

namespace units
variables {α : Type*} [normed_ring α] [complete_space α]

/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
def one_sub (t : α) (h : ∥t∥ < 1) : units α :=
{ val := 1 - t,
  inv := ∑' (n : ℕ), t ^ n,
  val_inv := mul_neg_geom_series t h,
  inv_val := geom_series_mul_neg t h }

@[simp] lemma one_sub_coe (t : α) (h : ∥t∥ < 1) : ((one_sub t h) : α) = 1 - t := rfl

/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
def add (x : units α) (t : α) (h : ∥t∥ < ∥((x⁻¹:units α):α)∥⁻¹) : units α :=
x * (units.one_sub (- (((x⁻¹:units α):α) * t))
begin
  rcases subsingleton_or_nonzero α with _i|_i, resetI,
  { rw subsingleton.elim ((x⁻¹:units α):α) 0,
    have : (0:ℝ) < 1 := by norm_num,
    simpa, },
  { have hpos : 0 < ∥((x⁻¹:units α):α)∥ := @units.norm_pos _ _ _i x⁻¹,
    calc ∥-(((x⁻¹:units α):α) * t)∥
        = ∥((x⁻¹:units α):α) * t∥                    : by { rw norm_neg }
    ... ≤ ∥((x⁻¹:units α):α)∥ * ∥t∥                   : norm_mul_le x.inv _
    ... < ∥((x⁻¹:units α):α)∥ * ∥((x⁻¹:units α):α)∥⁻¹ : by nlinarith only [h, hpos]
    ... = 1                                         : mul_inv_cancel (ne_of_gt hpos) },
end )

@[simp] lemma add_coe (x : units α) (t : α) (h : ∥t∥ < ∥((x⁻¹:units α):α)∥⁻¹) :
  ((x.add t h) : α) = x + t := by { unfold units.add, simp [mul_add] }

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
def unit_of_nearby (x : units α) (y : α) (h : ∥y - x∥ < ∥((x⁻¹:units α):α)∥⁻¹) : units α :=
x.add ((y:α) - x) h

@[simp] lemma unit_of_nearby_coe (x : units α) (y : α) (h : ∥y - x∥ < ∥((x⁻¹:units α):α)∥⁻¹) :
  ((x.unit_of_nearby y h) : α) = y := by { unfold units.unit_of_nearby, simp }

/-- The group of units of a complete normed ring is an open subset of the ring. -/
lemma is_open : is_open {x : α | is_unit x} :=
begin
  rcases subsingleton_or_nonzero α with _i|_i, resetI,
  { exact is_open_discrete is_unit },
  { apply metric.is_open_iff.mpr,
    rintros x' ⟨x, h⟩,
    refine ⟨∥((x⁻¹:units α):α)∥⁻¹, inv_pos.mpr (@units.norm_pos α _ _i x⁻¹), _⟩,
    intros y hy,
    rw [metric.mem_ball, dist_eq_norm, ←h] at hy,
    use x.unit_of_nearby y hy,
    simp }
end

end units
