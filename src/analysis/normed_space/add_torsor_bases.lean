/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.add_torsor
import linear_algebra.affine_space.independent

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:
 * `exists_subset_affine_independent_affine_span_eq_top_of_open`

-/

variables {V P : Type*} [normed_group V] [normed_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

open affine_map

/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
lemma exists_subset_affine_independent_span_eq_top_of_open {s u : set P} (hu : is_open u)
  (hsu : s ⊆ u) (hne : s.nonempty) (h : affine_independent ℝ (coe : s → P)) :
  ∃ t : set P, s ⊆ t ∧ t ⊆ u ∧ affine_independent ℝ (coe : t → P) ∧ affine_span ℝ t = ⊤ :=
begin
  obtain ⟨q, hq⟩ := hne,
  obtain ⟨ε, hε, hεu⟩ := metric.is_open_iff.mp hu q (hsu hq),
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h,
  let f : P → P := λ y, line_map q y (ε / 2 / (dist y q)),
  have hf : ∀ y, f y ∈ u,
  { intros y,
    apply hεu,
    simp only [metric.mem_ball, f, line_map_apply, dist_vadd_left, norm_smul, real.norm_eq_abs,
      dist_eq_norm_vsub V y q],
    cases eq_or_ne (∥y -ᵥ q∥) 0 with hyq hyq, { rwa [hyq, mul_zero], },
    rw [← norm_pos_iff, norm_norm] at hyq,
    calc abs (ε / 2 / ∥y -ᵥ q∥) * ∥y -ᵥ q∥
          = ε / 2 / ∥y -ᵥ q∥ * ∥y -ᵥ q∥ : by rw [abs_div, abs_of_pos (half_pos hε), abs_of_pos hyq]
      ... = ε / 2 : div_mul_cancel _ (ne_of_gt hyq)
      ... < ε : half_lt_self hε, },
  have hεyq : ∀ (y ∉ s), ε / 2 / dist y q ≠ 0,
  { simp only [ne.def, div_eq_zero_iff, or_false, dist_eq_zero, bit0_eq_zero, one_ne_zero,
      not_or_distrib, ne_of_gt hε, true_and, not_false_iff],
    finish, },
  classical,
  let w : t → units ℝ := λ p, if hp : (p : P) ∈ s then 1 else units.mk0 _ (hεyq ↑p hp),
  refine ⟨set.range (λ (p : t), line_map q p (w p : ℝ)), _, _, _, _⟩,
  { intros p hp, use ⟨p, ht₁ hp⟩, simp [w, hp], },
  { intros y hy,
    simp only [set.mem_range, set_coe.exists, subtype.coe_mk] at hy,
    obtain ⟨p, hp, hyq⟩ := hy,
    by_cases hps : p ∈ s;
    simp only [w, hps, line_map_apply_one, units.coe_mk0, dif_neg, dif_pos, not_false_iff,
      units.coe_one, subtype.coe_mk] at hyq;
    rw ← hyq;
    [exact hsu hps, exact hf p], },
  { exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range, },
  { rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃], },
end
