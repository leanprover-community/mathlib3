/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/

import tactic.qify
import data.zmod.basic
import number_theory.diophantine_approximation
import number_theory.zsqrtd.basic
import algebra.star.unitary

/-!
# Pell's Equation

We prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `pell.exists_of_not_is_square`.

This is the beginning of a development that aims at providing all of the essential theory
of Pell's Equation for general $d$ (as opposed to the contents of `number_theory.pell_matiyasevic`,
which is specific to the case $d = a^2 - 1$ for some $a > 1$).

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Provide the structure theory of the solution set to Pell's equation
  and furthermore also for `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

namespace pell

section existence

variables {d : ℤ}

open set real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
begin
  let ξ : ℝ := sqrt d,
  have hξ : irrational ξ,
  { refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt $ int.cast_nonneg.mpr h₀.le) _ two_pos,
    rintro ⟨x, hx⟩,
    refine hd ⟨x, @int.cast_injective ℝ _ _ d (x * x) _⟩,
    rw [← sq_sqrt $ int.cast_nonneg.mpr h₀.le, int.cast_mul, ← hx, sq], },
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1),
  have hM : {q : ℚ | |q.1 ^ 2 - d * q.2 ^ 2| < M}.infinite,
  { refine infinite.mono (λ q h, _) (infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational hξ),
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (nat.cast_pos.mpr q.pos) 2,
    have h1 : (q.num : ℝ) / (q.denom : ℝ) = q := by exact_mod_cast q.num_div_denom,
    rw [mem_set_of, abs_sub_comm, ← @int.cast_lt ℝ, ← div_lt_div_right (abs_pos_of_pos h0)],
    push_cast,
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel _ h0.ne',
        ← div_pow, h1, ← sq_sqrt (int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div],
    refine mul_lt_mul'' (((abs_add ξ q).trans _).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _),
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add'],
    rw [mem_set_of, abs_sub_comm] at h,
    refine (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans _),
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, nat.abs_cast, nat.one_le_cast],
    exact q.pos, },
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * q.2 ^ 2 = m}.infinite,
  { contrapose! hM,
    simp only [not_infinite] at hM ⊢,
    refine (congr_arg _ (ext (λ x, _))).mp (finite.bUnion (finite_Ioo (-M) M) (λ m _, hM m)),
    simp only [abs_lt, mem_set_of_eq, mem_Ioo, mem_Union, exists_prop, exists_eq_right'], },
  have hm₀ : m ≠ 0,
  { rintro rfl,
    obtain ⟨q, hq⟩ := hm.nonempty,
    rw [mem_set_of, sub_eq_zero, mul_comm] at hq,
    obtain ⟨a, ha⟩ := (int.pow_dvd_pow_iff two_pos).mp ⟨d, hq⟩,
    rw [ha, mul_pow, mul_right_inj' (pow_pos (int.coe_nat_pos.mpr q.pos) 2).ne'] at hq,
    exact hd ⟨a, sq a ▸ hq.symm⟩, },
  haveI := ne_zero_iff.mpr (int.nat_abs_ne_zero.mpr hm₀),
  let f : ℚ → (zmod m.nat_abs) × (zmod m.nat_abs) := λ q, (q.1, q.2),
  obtain ⟨q₁, h₁ : q₁.1 ^ 2 - d * q₁.2 ^ 2 = m, q₂, h₂ : q₂.1 ^ 2 - d * q₂.2 ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_maps_to (maps_to_univ f _) finite_univ,
  obtain ⟨hq1 : (q₁.1 : zmod m.nat_abs) = q₂.1, hq2 : (q₁.2 : zmod m.nat_abs) = q₂.2⟩ :=
    prod.ext_iff.mp hqf,
  have hd₁ : m ∣ q₁.1 * q₂.1 - d * (q₁.2 * q₂.2),
  { rw [← int.nat_abs_dvd, ← zmod.int_coe_zmod_eq_zero_iff_dvd],
    push_cast,
    rw [hq1, hq2, ← sq, ← sq],
    norm_cast,
    rw [zmod.int_coe_zmod_eq_zero_iff_dvd, int.nat_abs_dvd, nat.cast_pow, ← h₂], },
  have hd₂ : m ∣ q₁.1 * q₂.2 - q₂.1 * q₁.2,
  { rw [← int.nat_abs_dvd, ← zmod.int_coe_eq_int_coe_iff_dvd_sub],
    push_cast,
    rw [hq1, hq2], },
  replace hm₀ : (m : ℚ) ≠ 0 := int.cast_ne_zero.mpr hm₀,
  refine ⟨(q₁.1 * q₂.1 - d * (q₁.2 * q₂.2)) / m, (q₁.1 * q₂.2 - q₂.1 * q₁.2) / m, _, _⟩,
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

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
theorem exists_iff_not_is_square (h₀ : 0 < d) :
  (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬ is_square d :=
begin
  refine ⟨_, exists_of_not_is_square h₀⟩,
  rintros ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩,
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy,
  simpa [mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using int.eq_of_mul_eq_one hxy,
end

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
lemma exists_pos_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ 1 < x ∧ 0 < y :=
begin
  obtain ⟨x, y, h, hy⟩ := exists_of_not_is_square h₀ hd,
  refine ⟨|x|, |y|, by rwa [sq_abs, sq_abs], _, abs_pos.mpr hy⟩,
  rw [← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right],
  exact mul_pos h₀ (sq_pos_of_ne_zero y hy),
end

end existence

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `pell.solution₁ d`. It contains integers `x` and `y` and
a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*y' + d*y*y', x*y' + y*x')`
(this is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results).
-/

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.

/-- `pell.solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
This is a structure containing two integers `x` and `y` and a proof `rel` that the equation holds.
-/
@[derive [comm_group, has_distrib_neg, inhabited]]
def solution₁ (d : ℤ) : Type := ↥(unitary (zsqrtd d))

namespace solution₁

variables {d : ℤ}

/-- An alternative form of the relation, suitable for rewriting `x^2`. -/
lemma rel_x (a : solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by {rw ← a.rel, ring}

/-- An alternative form of the relation, suitable for rewriting `d * y^2`. -/
lemma rel_y (a : solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by {rw ← a.rel, ring}

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
lemma ext {a b : solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
begin
  cases a,
  cases b,
  congr; assumption,
end

-- Define an attribute for a `simp` set to be used in `pell_tac`.
run_cmd mk_simp_attr `pell_simp
run_cmd tactic.add_doc_string `simp_attr.pell_simp "Simp set to be used in `pell_tac`"

/-- We use `1` to denote the trivial solution `(1, 0)`. -/
instance : has_one (solution₁ d) :=
{ one := { x := 1, y := 0, rel := by simp } }

instance : inhabited (solution₁ d) := ⟨1⟩

@[simp, pell_simp]
lemma x_one : (1 : solution₁ d).x = 1 := rfl

@[simp, pell_simp]
lemma y_one : (1 : solution₁ d).y = 0 := rfl

/-- We can multiply two solutions. -/
instance : has_mul (solution₁ d) :=
{ mul := λ a b,
  { x := a.x * b.x + d * (a.y * b.y),
    y := a.x * b.y + a.y * b.x,
    rel := by {conv_rhs {rw ← mul_one (1 : ℤ), congr, rw ← a.rel, skip, rw ← b.rel}, ring} } }

@[simp, pell_simp]
lemma x_mul (a b : solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) := rfl

@[simp, pell_simp]
lemma y_mul (a b : solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x := rfl

/-- We obtain the inverse of a solution by changing the sign of `y`. -/
instance : has_inv (solution₁ d) :=
{ inv := λ a, { x := a.x, y := -a.y, rel := by simp [a.rel] } }

@[simp, pell_simp]
lemma x_inv (a : solution₁ d) : a⁻¹.x = a.x := rfl

@[simp, pell_simp]
lemma y_inv (a : solution₁ d) : a⁻¹.y = -a.y := rfl

/-- We define the negative of a solution by negating both `x` and `y`. -/
instance : has_neg (solution₁ d) :=
{ neg := λ a, { x := -a.x, y := -a.y, rel := by simp [a.rel] } }

@[simp, pell_simp]
lemma x_neg (a : solution₁ d) : (-a).x = -a.x := rfl

@[simp, pell_simp]
lemma y_neg (a : solution₁ d) : (-a).y = -a.y := rfl

/-- Set up a tactic that discharges the computational goals below. -/
meta def pell_tac : tactic unit :=
`[ intros, ext; simp only with pell_simp; ring_nf ]

/-- The solutions to the Pell equation `x^2 - d*y^2 = 1` form a commutative group. -/
instance : comm_group (solution₁ d) :=
{ mul := has_mul.mul,
  mul_assoc := by pell_tac,
  one := has_one.one,
  one_mul := by pell_tac,
  mul_one := by pell_tac,
  mul_comm := by pell_tac,
  inv := has_inv.inv,
  mul_left_inv := λ a, by {pell_tac, rw a.rel_x, ring},
  .. }

/-- The negation of solutions is compatible with the multiplicative structure. -/
instance : has_distrib_neg (solution₁ d) :=
{ neg := has_neg.neg,
  neg_neg := by pell_tac,
  neg_mul := by pell_tac,
  mul_neg := by pell_tac }

end solution₁

end pell
#lint
