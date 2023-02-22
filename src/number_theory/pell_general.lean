/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/

import tactic.qify
import data.zmod.basic
import number_theory.diophantine_approximation

/-!
# Pell's Equation

We prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `pell.ex_nontriv_sol`.

This is the beginning of a development that aims at providing all of the essential theory
of Pell's Equation for general $d$ (as opposed to the contents of `number_theory.pell`,
which is specific to the case $d = a^2 - 1$ for some $a > 1$).

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation
-/

namespace pell

section existence

open set real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem ex_nontriv_sol {d : ℤ} (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
begin
  let ξ : ℝ := sqrt d,
  have hξ : irrational ξ,
  { refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt $ int.cast_nonneg.mpr h₀.le) _ two_pos,
    rintro ⟨x, hx⟩,
    refine hd ⟨x, @int.cast_injective ℝ _ _ d (x * x) _⟩,
    rw [← sq_sqrt $ int.cast_nonneg.mpr h₀.le, int.cast_mul, ← hx, sq], },
  obtain ⟨M, hM₁⟩ := exists_nat_gt (2 * ξ + 1),
  have hM : {q : ℚ | |q.1 ^ 2 - d * q.2 ^ 2| < M}.infinite,
  { refine infinite.mono (λ q (h : |ξ - q| < 1 / q.2 ^ 2), _)
      (infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational hξ),
    replace h : |ξ - q.1 / q.2| < 1 / q.2 ^ 2 := by {convert h, exact_mod_cast q.num_div_denom},
    have hq : 0 < (q.2 : ℝ) := nat.cast_pos.mpr q.pos,
    have H : (d : ℝ) * q.2 ^ 2 - q.1 ^ 2 =
               (ξ - q.1 / q.2) * q.2 ^ 2 * (2 * ξ - (ξ - q.1 / q.2)),
    { field_simp [hq.ne'], rw ← sq_sqrt (int.cast_pos.mpr h₀).le, ring, },
    have claim : |(q.1 : ℝ) ^ 2 - d * q.2 ^ 2| < M,
    { rw [abs_sub_comm, H, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q.2 : ℝ))],
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h.le $ sq_nonneg _) $
        abs_nonneg _).trans_lt _,
      rw [one_div_mul_cancel (sq_pos_of_pos hq).ne', one_mul],
      refine (((abs_sub _ _).trans_lt $ add_lt_add_left h _).trans_le $
        add_le_add_left (_ : _ ≤ 1) _).trans _,
      { refine (one_div_le zero_lt_one $ sq_pos_of_pos hq).mp _,
        rw [div_one, one_le_sq_iff hq.le],
        exact_mod_cast q.pos, },
      { rwa abs_of_nonneg (mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) (sqrt_nonneg _)), } },
    exact_mod_cast claim, },
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * q.2 ^ 2 = m}.infinite,
  { by_contra' hf,
    refine not_infinite.mpr (finite.bUnion (finite_Ioo (- (M : ℤ)) M) $
      λ m _, not_infinite.mp $ hf m) (@eq.subst _ set.infinite _ _ (set.ext $ λ q, _) hM),
    simp only [abs_lt, mem_set_of_eq, mem_Ioo, mem_Union, exists_prop, exists_eq_right'], },
  have hm₀ : m ≠ 0,
  { rintro rfl,
    obtain ⟨q, hq⟩ := hm.nonempty,
    rw [mem_set_of, sub_eq_zero, mul_comm] at hq,
    obtain ⟨a, ha⟩ := (int.pow_dvd_pow_iff two_pos).mp ⟨d, hq⟩,
    rw [ha, mul_pow] at hq,
    refine hd ⟨a, sq a ▸ (mul_left_cancel₀ (pow_ne_zero 2 _) hq).symm⟩,
    exact nat.cast_ne_zero.mpr q.pos.ne', },
  haveI := ne_zero_iff.mpr (int.nat_abs_ne_zero.mpr hm₀),
  let f : ℚ → (zmod m.nat_abs) × (zmod m.nat_abs) := λ q, (q.1, q.2),
  haveI hft := (zmod.fintype m.nat_abs).finite,
  obtain ⟨q₁, h₁ : q₁.1 ^ 2 - d * q₁.2 ^ 2 = m, q₂, h₂ : q₂.1 ^ 2 - d * q₂.2 ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_maps_to (maps_to_univ f _)
      (finite_univ_iff.mpr $ @finite.prod.finite _ _ hft hft),
  obtain ⟨hq1 : (q₁.1 : zmod m.nat_abs) = q₂.1, hq2 : (q₁.2 : zmod m.nat_abs) = q₂.2⟩ :=
    prod.ext_iff.mp hqf,
  have h₂' : (d * q₂.2 ^ 2 : zmod m.nat_abs) = q₂.1 ^ 2,
  { exact_mod_cast (zmod.int_coe_eq_int_coe_iff_dvd_sub (d * q₂.2 ^ 2) (q₂.1 ^ 2) m.nat_abs).mpr
      (int.nat_abs_dvd.mpr $ trans_rel_left (∣) dvd_rfl h₂.symm), },
  have hd₁ : m ∣ q₁.1 * q₂.1 - d * q₁.2 * q₂.2,
  { refine int.nat_abs_dvd.mp ((zmod.int_coe_eq_int_coe_iff_dvd_sub _ _ _).mp _),
    push_cast,
    rw [hq1, hq2, ← sq, ← h₂', sq, mul_assoc], },
  have hd₂ : m ∣ q₁.1 * q₂.2 - q₂.1 * q₁.2,
  { refine int.nat_abs_dvd.mp ((zmod.int_coe_eq_int_coe_iff_dvd_sub _ _ _).mp _),
    push_cast,
    rw [hq1, hq2], },
  replace hm₀ : (m : ℚ) ≠ 0 := int.cast_ne_zero.mpr hm₀,
  refine ⟨(q₁.1 * q₂.1 - d * q₁.2 * q₂.2) / m, (q₁.1 * q₂.2 - q₂.1 * q₁.2) / m, _, _⟩,
  { qify [hd₁, hd₂],
    field_simp [hm₀],
    norm_cast,
    conv_rhs {congr, rw sq, congr, rw ← h₁, skip, rw ← h₂},
    push_cast,
    ring, },
  { qify [hd₂],
    refine div_ne_zero_iff.mpr ⟨_, hm₀⟩,
    exact_mod_cast mt sub_eq_zero.mp (mt rat.eq_iff_mul_eq_mul.mpr hne), },
end

end existence

end pell
