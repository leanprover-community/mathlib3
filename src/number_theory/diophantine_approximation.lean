/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import tactic.basic
import data.real.irrational
import combinatorics.pigeonhole

/-!
# Diophantine Approximation

This file gives proofs of various versions of **Dirichlet's approximation theorem**
and its important consequence that when `ξ` is an irrational real number, then there are
infinitely many rationals `x/y` (in lowest terms) such that `|ξ - x/y| < 1/y^2`.

The proof is based on the pigeonhole principle.

## Main statements

The main results are
* `real.exists_int_int_abs_mul_sub_le`, which is a version of Dirichlet's approximation
  theorem and states that for all real `ξ` and natural `0 < n`, there are integers
  `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `real.exists_nat_abs_mul_sub_round_le`, which is a variant of this replacing `j`
  by `round(k*ξ)` and using a natural number `k`,
* A further variant `real.exists_rat_abs_sub_le_and_denom_le` in terms of rationals `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.denom)` and `q.denom ≤ n`,
* `dioph_approx.rat_approx_infinite`, which states that for irrational `ξ`,
  `{q : ℚ | |ξ - q| < 1/q.denom^2}` is infinite,

## Implementation notes

We use the namespace `real` for the results.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>

## Tags

Diophantine approximation, Dirichlet's approximation theorem
-/

namespace real

section dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`.
-/

open finset int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`. -/
lemma exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) :=
begin
  let f : ℤ → ℤ := λ m, ⌊fract (ξ * m) * (n + 1)⌋,
  have hn : 0 < (n : ℝ) + 1 := by exact_mod_cast nat.succ_pos _,
  have hfu := λ m : ℤ, mul_lt_of_lt_one_left hn $ fract_lt_one (ξ * ↑m),
  conv in (|_| ≤ _) { rw [mul_comm, le_div_iff hn, ← abs_of_pos hn, ← abs_mul], },
  let D := Icc (0 : ℤ) n,
  by_cases H : ∃ m ∈ D, f m = n,
  { obtain ⟨m, hm, hf⟩ := H,
    have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1)),
    have hm₀ : 0 < m,
    { have hf₀ : f 0 = 0,
      { simp only [floor_eq_zero_iff, algebra_map.coe_zero, mul_zero, fract_zero, zero_mul,
                   set.left_mem_Ico, zero_lt_one], },
      refine ne.lt_of_le (λ h, n_pos.ne _) (mem_Icc.mp hm).1,
      exact_mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n), },
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, _⟩,
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le],
    refine ⟨le_sub_iff_add_le.mpr _, sub_le_iff_le_add.mpr $ le_of_lt $
             (hfu m).trans $ lt_one_add _⟩,
    simpa only [neg_add_cancel_comm_assoc] using hf', },
  { simp_rw [not_exists] at H,
    have hD : (Ico (0 : ℤ) n).card < D.card,
    { rw [card_Icc, card_Ico], exact lt_add_one n, },
    have hfu' : ∀ m, f m ≤ n := λ m, lt_add_one_iff.mp (floor_lt.mpr (by exact_mod_cast hfu m)),
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n :=
      λ x hx, mem_Ico.mpr ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le),
                           ne.lt_of_le (H x hx) (hfu' x)⟩,
    have : ∃ (x : ℤ) (hx : x ∈ D) (y : ℤ) (hy : y ∈ D), x < y ∧ f x = f y,
    { obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd,
      rcases lt_trichotomy x y with h | h | h,
      exacts [⟨x, hx, y, hy, h, hxy⟩, false.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩], },
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ := this,
    refine ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
            sub_le_iff_le_add.mpr $ le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, _⟩,
    convert_to |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1,
    { congr, push_cast, simp only [fract], ring, },
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le, }
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
lemma exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) :=
begin
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
  have hk := to_nat_of_nonneg hk₀.le,
  rw [← hk] at hk₀ hk₁ h,
  exact ⟨k.to_nat, coe_nat_pos.mp hk₀, nat.cast_le.mp hk₁, (round_le (↑k.to_nat * ξ) j).trans h⟩,
end

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.denom ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.denom)`. -/
lemma exists_rat_abs_sub_le_and_denom_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
  ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.denom) ∧ q.denom ≤ n :=
begin
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos,
  have hk₀' : (0 : ℝ) < k := int.cast_pos.mpr hk₀,
  have hden : ((j / k : ℚ).denom : ℤ) ≤ k,
  { convert le_of_dvd hk₀ (rat.denom_dvd j k), exact rat.coe_int_div_eq_mk, },
  refine ⟨j / k, _, nat.cast_le.mp (hden.trans hk₁)⟩,
  rw [← div_div, le_div_iff (nat.cast_pos.mpr $ rat.pos _ : (0 : ℝ) < _)],
  refine (mul_le_mul_of_nonneg_left (int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans _,
  rwa [← abs_of_pos hk₀', rat.cast_div, rat.cast_coe_int, rat.cast_coe_int,
       ← abs_mul, sub_mul, div_mul_cancel _ hk₀'.ne', mul_comm],
end

end dirichlet

section rat_approx

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/

open set

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
lemma ex_better_approx {ξ : ℝ} (hξ : irrational ξ) (q : ℚ) :
  ∃ q' : ℚ, |ξ - q'| < 1 / q'.denom ^ 2 ∧ |ξ - q'| < |ξ - q| :=
begin
  have h : 0 < |ξ - q|,
  { refine abs_pos.mpr (sub_ne_zero.mpr _),
    simp only [irrational, mem_range, not_exists, ← ne.def] at hξ,
    exact (hξ q).symm, },
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|),
  have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm,
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_denom_le ξ (nat.cast_pos.mp m_pos),
  have den_pos : (0 : ℝ) < q'.denom := nat.cast_pos.mpr q'.pos,
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos,
  refine ⟨q', lt_of_le_of_lt hbd _, lt_of_le_of_lt hbd _⟩,
  { rw [sq, one_div_lt_one_div md_pos (mul_pos den_pos den_pos), mul_lt_mul_right den_pos],
    exact lt_add_of_le_of_pos (nat.cast_le.mpr hden) zero_lt_one, },
  { rw [one_div_lt md_pos h],
    refine hm.trans (lt_of_lt_of_le (lt_add_one _) $
                      (le_mul_iff_one_le_right $ add_pos m_pos zero_lt_one).mpr _),
    exact_mod_cast (q'.pos : 1 ≤ q'.denom), }
end

/-- There is always at least one good rational approximation. -/
lemma rat_approx_nonempty (ξ : ℝ) : {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.nonempty :=
⟨⌊ξ⌋, by simp [abs_of_nonneg, int.fract_lt_one]⟩

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
lemma rat_approx_infinite {ξ : ℝ} (hξ : irrational ξ) :
  {q : ℚ | |ξ - q| < 1 / q.denom ^ 2}.infinite :=
begin
  refine or.resolve_left (set.finite_or_infinite _) (λ h, _),
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / q.denom ^ 2} (λ q, |ξ - q|) h (rat_approx_nonempty ξ),
  obtain ⟨q', hmem, hbetter⟩ := ex_better_approx hξ q,
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter),
end

end rat_approx

end real
