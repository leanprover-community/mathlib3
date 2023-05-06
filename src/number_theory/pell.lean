/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/

import tactic.qify
import data.zmod.basic
import number_theory.diophantine_approximation
import number_theory.zsqrtd.basic

/-!
# Pell's Equation

*Pell's Equation* is the equation $x^2 - d y^2 = 1$, where $d$ is a positive integer
that is not a square, and one is interested in solutions in integers $x$ and $y$.

In this file, we aim at providing all of the essential theory of Pell's Equation for general $d$
(as opposed to the contents of `number_theory.pell_matiyasevic`, which is specific to the case
$d = a^2 - 1$ for some $a > 1$).

We begin by defining a type `pell.solution₁ d` for solutions of the equation,
show that it has a natural structure as an abelian group, and prove some basic
properties.

We then prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `pell.exists_of_not_is_square` and `pell.exists_nontrivial_of_not_is_square`.

We then define the *fundamental solution* to be the solution
with smallest $x$ among all solutions satisfying $x > 1$ and $y > 0$.
We show that every solution is a power of the fundamental solution up to a (common) sign,
see `pell.fundamental.eq_zpow_or_neg_zpow`, and that a (positive) solution has this property
if and only if it is fundamental, see `pell.pos_generator_iff_fundamental`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Extend to `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

namespace pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `pell.solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*y' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `pell.solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `pell.solution₁ d`.
-/

open zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `pell.is_pell_iff_mem_unitary`. -/
lemma is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
  a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary ℤ√d :=
by rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.

/-- `pell.solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
@[derive [comm_group, has_distrib_neg, inhabited]]
def solution₁ (d : ℤ) : Type := ↥(unitary ℤ√d)

namespace solution₁

variables {d : ℤ}

instance : has_coe (solution₁ d) ℤ√d := { coe := subtype.val }

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def x (a : solution₁ d) : ℤ := (a : ℤ√d).re

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def y (a : solution₁ d) : ℤ := (a : ℤ√d).im

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
lemma prop (a : solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
is_pell_solution_iff_mem_unitary.mpr a.property

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
lemma prop_x (a : solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by {rw ← a.prop, ring}

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
lemma prop_y (a : solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by {rw ← a.prop, ring}

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
lemma ext {a b : solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
subtype.ext $ ext.mpr ⟨hx, hy⟩

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : solution₁ d :=
{ val := ⟨x, y⟩,
  property := is_pell_solution_iff_mem_unitary.mp prop }

@[simp]
lemma x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x := rfl

@[simp]
lemma y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y := rfl

@[simp]
lemma coe_mk  (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x,y⟩ :=
zsqrtd.ext.mpr ⟨x_mk x y prop, y_mk x y prop⟩

@[simp]
lemma x_one : (1 : solution₁ d).x = 1 := rfl

@[simp]
lemma y_one : (1 : solution₁ d).y = 0 := rfl

@[simp]
lemma x_mul (a b : solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) :=
by {rw ← mul_assoc, refl}

@[simp]
lemma y_mul (a b : solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x := rfl

@[simp]
lemma x_inv (a : solution₁ d) : a⁻¹.x = a.x := rfl

@[simp]
lemma y_inv (a : solution₁ d) : a⁻¹.y = -a.y := rfl

@[simp]
lemma x_neg (a : solution₁ d) : (-a).x = -a.x := rfl

@[simp]
lemma y_neg (a : solution₁ d) : (-a).y = -a.y := rfl

/-- When `d` is negative, then `x` or `y` must be zero in a solution. -/
lemma eq_zero_of_d_neg (h₀ : d < 0) (a : solution₁ d) : a.x = 0 ∨ a.y = 0 :=
begin
  have h := a.prop,
  contrapose! h,
  have h1 := sq_pos_of_ne_zero a.x h.1,
  have h2 := sq_pos_of_ne_zero a.y h.2,
  nlinarith,
end

/-- A solution has `x ≠ 0`. -/
lemma x_ne_zero (h₀ : 0 ≤ d) (a : solution₁ d) : a.x ≠ 0 :=
begin
  intro hx,
  have h : 0 ≤ d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _),
  rw [a.prop_y, hx, sq, zero_mul, zero_sub] at h,
  exact not_le.mpr (neg_one_lt_zero : (-1 : ℤ) < 0) h,
end

/-- A solution with `x > 1` must have `y ≠ 0`. -/
lemma y_ne_zero_of_one_lt_x {a : solution₁ d} (ha : 1 < a.x) : a.y ≠ 0 :=
begin
  intro hy,
  have prop := a.prop,
  rw [hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero] at prop,
  exact lt_irrefl _ (((one_lt_sq_iff $ zero_le_one.trans ha.le).mpr ha).trans_eq prop),
end

/-- If a solution has `x > 1`, then `d` is positive. -/
lemma d_pos_of_one_lt_x {a : solution₁ d} (ha : 1 < a.x) : 0 < d :=
begin
  refine pos_of_mul_pos_left _ (sq_nonneg a.y),
  rw [a.prop_y, sub_pos],
  exact one_lt_pow ha two_ne_zero,
end

/-- If a solution has `x > 1`, then `d` is not a square. -/
lemma d_nonsquare_of_one_lt_x {a : solution₁ d} (ha : 1 < a.x) : ¬ is_square d :=
begin
  have hp := a.prop,
  rintros ⟨b, rfl⟩,
  simp_rw [← sq, ← mul_pow, sq_sub_sq, int.mul_eq_one_iff_eq_one_or_neg_one] at hp,
  rcases hp with ⟨hp₁, hp₂⟩ | ⟨hp₁, hp₂⟩; linarith [ha, hp₁, hp₂],
end

/-- A solution with `x = 1` is trivial. -/
lemma eq_one_of_x_eq_one (h₀ : d ≠ 0) {a : solution₁ d} (ha : a.x = 1) : a = 1 :=
begin
  have prop := a.prop_y,
  rw [ha, one_pow, sub_self, mul_eq_zero, or_iff_right h₀, sq_eq_zero_iff] at prop,
  exact ext ha prop,
end

/-- A solution is `1` or `-1` if and only if `y = 0`. -/
lemma eq_one_or_neg_one_iff_y_eq_zero {a : solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 :=
begin
  refine ⟨λ H, H.elim (λ h, by simp [h]) (λ h, by simp [h]), λ H, _⟩,
  have prop := a.prop,
  rw [H, sq (0 : ℤ), mul_zero, mul_zero, sub_zero, sq_eq_one_iff] at prop,
  exact prop.imp (λ h, ext h H) (λ h, ext h H),
end

/-- The set of solutions with `x > 0` is closed under multiplication. -/
lemma x_mul_pos {a b : solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).x :=
begin
  simp only [x_mul],
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp _).1,
  rw [← abs_of_pos ha, ← abs_of_pos hb, ← abs_mul, ← sq_lt_sq, mul_pow a.x, a.prop_x, b.prop_x,
      ← sub_pos],
  ring_nf,
  cases le_or_lt 0 d with h h,
  { positivity, },
  { rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne',
        zero_pow two_pos, zero_add, zero_mul, zero_add],
    exact one_pos, },
end

/-- The set of solutions with `x` and `y` positive is closed under multiplication. -/
lemma y_mul_pos {a b : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
  (hby : 0 < b.y) :
  0 < (a * b).y :=
begin
  simp only [y_mul],
  positivity,
end

/-- If `(x, y)` is a solution with `x` positive, then all its powers with natural exponents
have positive `x`. -/
lemma x_pow_pos {a : solution₁ d} (hax : 0 < a.x) (n : ℕ) : 0 < (a ^ n).x :=
begin
  induction n with n ih,
  { simp only [pow_zero, x_one, zero_lt_one], },
  { rw [pow_succ],
    exact x_mul_pos hax ih, }
end

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
natural exponents have positive `y`. -/
lemma y_pow_succ_pos {a : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : ℕ) :
  0 < (a ^ n.succ).y :=
begin
  induction n with n ih,
  { simp only [hay, pow_one], },
  { rw [pow_succ],
    exact y_mul_pos hax hay (x_pow_pos hax _) ih, }
end

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
exponents have positive `y`. -/
lemma y_zpow_pos {a : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : ℤ} (hn : 0 < n) :
  0 < (a ^ n).y :=
begin
  lift n to ℕ using hn.le,
  norm_cast at hn ⊢,
  rw ← nat.succ_pred_eq_of_pos hn,
  exact y_pow_succ_pos hax hay _,
end

/-- If `(x, y)` is a solution with `x` positive, then all its powers have positive `x`. -/
lemma x_zpow_pos {a : solution₁ d} (hax : 0 < a.x) (n : ℤ) : 0 < (a ^ n).x :=
begin
  cases n,
  { rw zpow_of_nat,
    exact x_pow_pos hax n },
  { rw zpow_neg_succ_of_nat,
    exact x_pow_pos hax (n + 1) },
end

/-- If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of any power
has the same sign as the exponent. -/
lemma sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
   (n : ℤ) :
  (a ^ n).y.sign = n.sign :=
begin
  rcases n with (_ | _) | _,
  { refl },
  { rw zpow_of_nat,
    exact int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n) },
  { rw zpow_neg_succ_of_nat,
    exact int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n)) },
end

/-- If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`. -/
lemma exists_pos_variant (h₀ : 0 < d) (a : solution₁ d) :
  ∃ b : solution₁ d, 0 < b.x ∧ 0 ≤ b.y ∧ a ∈ ({b, b⁻¹, -b, -b⁻¹} : set (solution₁ d)) :=
begin
  refine (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
           ((le_total 0 a.y).elim (λ hy hx, ⟨-a⁻¹, _, _, _⟩) (λ hy hx, ⟨-a, _, _, _⟩))
           ((le_total 0 a.y).elim (λ hy hx, ⟨a, hx, hy, _⟩) (λ hy hx, ⟨a⁻¹, hx, _, _⟩));
      simp only [neg_neg, inv_inv, neg_inv, set.mem_insert_iff, set.mem_singleton_iff, true_or,
                 eq_self_iff_true, x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true];
      assumption,
end

end solution₁

section existence

/-!
### Existence of nontrivial solutions
-/

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

namespace solution₁

/-- If `d` is a positive integer that is not a square, then there exists a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_nontrivial_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ a : solution₁ d, a ≠ 1 ∧ a ≠ -1 :=
begin
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_is_square h₀ hd,
  refine ⟨mk x y prop, λ H, _, λ H, _⟩; apply_fun solution₁.y at H; simpa only [hy] using H,
end

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
lemma exists_pos_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ a : solution₁ d, 1 < a.x ∧ 0 < a.y :=
begin
  obtain ⟨x, y, h, hy⟩ := exists_of_not_is_square h₀ hd,
  refine ⟨mk (|x|) (|y|) (by rwa [sq_abs, sq_abs]), _, abs_pos.mpr hy⟩,
  rw [x_mk, ← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right],
  exact mul_pos h₀ (sq_pos_of_ne_zero y hy),
end

end solution₁

end existence

/-! ### Fundamental solutions

We define the notion of a *fundamental solution* of Pell's equation and
show that it exists and is unique (when `d` is positive and non-square)
and generates the group of solutions up to sign.
-/

variables {d : ℤ}

/-- We define a solution to be *fundamental* if it has `x > 1` and `y > 0`
and its `x` is the smallest possible among solutions with `x > 1`. -/
def is_fundamental (a : solution₁ d) : Prop :=
1 < a.x ∧ 0 < a.y ∧ ∀ {b : solution₁ d}, 1 < b.x → a.x ≤ b.x

namespace is_fundamental

open solution₁

/-- A fundamental solution has positive `x`. -/
lemma x_pos {a : solution₁ d} (h : is_fundamental a) : 0 < a.x := zero_lt_one.trans h.1

/-- If a fundamental solution exists, then `d` must be positive. -/
lemma d_pos {a : solution₁ d} (h : is_fundamental a) : 0 < d := d_pos_of_one_lt_x h.1

/-- If a fundamental solution exists, then `d` must be a non-square. -/
lemma d_nonsquare {a : solution₁ d} (h : is_fundamental a) : ¬ is_square d :=
d_nonsquare_of_one_lt_x h.1

/-- If there is a fundamental solution, it is unique. -/
lemma unique {a b : solution₁ d} (ha : is_fundamental a) (hb : is_fundamental b) : a = b :=
begin
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1),
  refine solution₁.ext hx _,
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx],
  exact (sq_eq_sq ha.2.1.le hb.2.1.le).mp (int.eq_of_mul_eq_mul_left ha.d_pos.ne' this),
end

/-- If `d` is positive and not a square, then a fundamental solution exists. -/
lemma exists_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ a : solution₁ d, is_fundamental a :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_is_square h₀ hd,
  -- convert to `x : ℕ` to be able to use `nat.find`
  have P : ∃ x' : ℕ, 1 < x' ∧ ∃ y' : ℤ, 0 < y' ∧ (x' : ℤ) ^ 2 - d * y' ^ 2 = 1,
  { have hax := a.prop,
    lift a.x to ℕ using (by positivity) with ax,
    norm_cast at ha₁,
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩, },
  classical, -- to avoid having to show that the predicate is decidable
  let x₁ := nat.find P,
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := nat.find_spec P,
  refine ⟨mk x₁ y₁ hy₁, (by {rw x_mk, exact_mod_cast hx}), hy₀, λ b hb, _⟩,
  rw x_mk,
  have hb' := (int.to_nat_of_nonneg $ zero_le_one.trans hb.le).symm,
  have hb'' := hb,
  rw hb' at hb ⊢,
  norm_cast at hb ⊢,
  refine nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr $ y_ne_zero_of_one_lt_x hb'', _⟩,
  convert b.prop using 1,
  rw [← hb', sq_abs],
end

/-- The `n`th power of a fundamental solution is trivial if and only if `n = 0`. -/
lemma pow_eq_one_iff {a : solution₁ d} (h : is_fundamental a) (n : ℤ) : a ^ n = 1 ↔ n = 0 :=
begin
  refine ⟨λ H, _, λ H, by rw [H, zpow_zero]⟩,
  have H' : (a ^ n).y = 0 := by rw [H, y_one],
  rcases lt_trichotomy 0 n with hn | rfl | hn,
  { exact absurd H' (y_zpow_pos h.x_pos h.2.1 hn).ne', },
  { refl, },
  { have := y_zpow_pos h.x_pos h.2.1 (by rwa [lt_neg, neg_zero] : 0 < -n),
    rw [zpow_neg, y_inv, H', neg_zero] at this,
    exact false.elim (lt_irrefl _ this), }
end

/-- The `n`th power of a fundamental solution has positive `y` if and only if `n` is positive. -/
lemma pow_y_pos_iff {a : solution₁ d} (h : is_fundamental a) (n : ℤ) : 0 < (a ^ n).y ↔ 0 < n :=
begin
  refine ⟨λ H, _, y_zpow_pos h.x_pos h.2.1⟩,
  rcases lt_trichotomy 0 n with hn | rfl | hn,
  { exact hn, },
  { rwa [zpow_zero, y_one] at H, },
  { have := y_zpow_pos h.x_pos h.2.1 (by rwa [lt_neg, neg_zero] : 0 < -n),
    rw [zpow_neg, y_inv, lt_neg, neg_zero] at this,
    exact false.elim (lt_irrefl _ $ H.trans this), }
end

/-- The `n`th power of a fundamental solution has negative `y` if and only if `n` is negative. -/
lemma pow_y_neg_iff {a : solution₁ d} (h : is_fundamental a) (n : ℤ) : (a ^ n).y < 0 ↔ n < 0 :=
begin
  rw [← neg_neg n, zpow_neg, y_inv, neg_lt, neg_zero, neg_lt, neg_zero],
  exact h.pow_y_pos_iff (-n),
end

/-- A power of a fundamental solution is never equal to the negative of a power of this
fundamental solution. -/
lemma pow_ne_neg_fundamental_pow {a : solution₁ d} (h : is_fundamental a) {n n' : ℤ} :
   a ^ n ≠ -a ^ n' :=
begin
  intro hf,
  apply_fun solution₁.x at hf,
  have H := x_zpow_pos h.x_pos n,
  rw [hf, x_neg, lt_neg, neg_zero] at H,
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H),
end

/-- The `x`-coordinate of a fundamental solution is a lower bound for the `x`-coordinate
of any positive solution. -/
lemma x_le_x {a₁ : solution₁ d} (h : is_fundamental a₁) {a : solution₁ d} (hax : 1 < a.x) :
  a₁.x ≤ a.x :=
h.2.2 hax

/-- The `y`-coordinate of a fundamental solution is a lower bound for the `y`-coordinate
of any positive solution. -/
lemma le_y {a₁ : solution₁ d} (h : is_fundamental a₁) {a : solution₁ d} (hax : 1 < a.x)
  (hay : 0 < a.y) :
  a₁.y ≤ a.y :=
begin
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by { rw [a.prop_x, a₁.prop_x], ring },
  rw [← abs_of_pos hay, ← abs_of_pos h.2.1, ← sq_le_sq, ← mul_le_mul_left h.d_pos, ← sub_nonpos,
      ← mul_sub, H, sub_nonpos, sq_le_sq, abs_of_pos (zero_lt_one.trans h.1),
      abs_of_pos (zero_lt_one.trans hax)],
  exact h.x_le_x hax,
end

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate decreases and the `y`-coordinate remains nonnegative. -/
lemma mul_inv_lt_x {a₁ : solution₁ d} (h : is_fundamental a₁) {a : solution₁ d} (hax : 1 < a.x)
  (hay : 0 < a.y) :
  0 < (a * a₁⁻¹).x ∧ (a * a₁⁻¹).x < a.x ∧ 0 ≤ (a * a₁⁻¹).y :=
begin
  have hax' := zero_lt_one.trans hax,
  have H₁ : a.x * a₁.y ≤ a.y * a₁.x,
  { rw [← abs_of_pos hax', ← abs_of_pos hay,
        ← abs_of_pos h.x_pos, ← abs_of_pos h.2.1, ← abs_mul, ← abs_mul, ← sq_le_sq,
        mul_pow, mul_pow, a.prop_x, a₁.prop_x, ← sub_nonneg],
    ring_nf,
    rw [sub_nonneg, sq_le_sq, abs_of_pos hay, abs_of_pos h.2.1],
    exact h.le_y hax hay, },
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add',
             lt_add_neg_iff_add_lt, zero_add, y_mul, le_neg_add_iff_add_le, add_zero],
  refine ⟨_, _, H₁⟩,
  { refine (mul_lt_mul_left hax').mp _,
    rw [(by ring : a.x * (d * (a.y * a₁.y)) = (d * a.y) * (a.x * a₁.y))],
    refine ((mul_le_mul_left $ mul_pos h.d_pos hay).mpr H₁).trans_lt _,
    rw [← mul_assoc, mul_assoc d, ← sq, a.prop_y, ← sub_pos],
    ring_nf,
    exact zero_lt_one.trans h.1, },
  { refine (mul_lt_mul_left h.2.1).mp _,
    rw [(by ring : a₁.y * (a.x * a₁.x) = a.x * a₁.y * a₁.x)],
    refine ((mul_le_mul_right $ zero_lt_one.trans h.1).mpr H₁).trans_lt _,
    rw [mul_assoc, ← sq, a₁.prop_x, ← sub_neg],
    ring_nf,
    rw [sub_neg, ← abs_of_pos hay, ← abs_of_pos h.2.1, ← abs_of_pos hax', ← abs_mul, ← sq_lt_sq,
        mul_pow, a.prop_x],
    calc
      a.y ^ 2 = 1 * a.y ^ 2                  : (one_mul _).symm
          ... ≤ d * a.y ^ 2                  : (mul_le_mul_right $ sq_pos_of_pos hay).mpr h.d_pos
          ... < d * a.y ^ 2 + 1              : lt_add_one _
          ... = (1 + d * a.y ^ 2) * 1        : by rw [add_comm, mul_one]
          ... ≤ (1 + d * a.y ^ 2) * a₁.y ^ 2
                : (mul_le_mul_left (by {have := h.d_pos, positivity})).mpr (sq_pos_of_pos h.2.1), }
end

/-- Any nonnegative solution is a power with nonnegative exponent of a fundamental solution. -/
lemma eq_pow_of_nonneg {a₁ : solution₁ d} (h : is_fundamental a₁) {a : solution₁ d} (hax : 0 < a.x)
  (hay : 0 ≤ a.y) :
  ∃ n : ℕ, a = a₁ ^ n :=
begin
  lift a.x to ℕ using hax.le with ax hax',
  induction ax using nat.strong_induction_on with x ih generalizing a,
  cases hay.eq_or_lt with hy hy,
  { -- case 1: `a = 1`
    refine ⟨0, _⟩,
    simp only [pow_zero],
    ext; simp only [x_one, y_one],
    { have prop := a.prop,
      rw [← hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero, sq_eq_one_iff] at prop,
      refine prop.resolve_right (λ hf, _),
      have := (hax.trans_eq hax').le.trans_eq hf,
      norm_num at this, },
    { exact hy.symm, } },
  { -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos],
    obtain ⟨hxx₁, hxx₂, hyy⟩ := h.mul_inv_lt_x hx₁ hy,
    lift (a * a₁⁻¹).x to ℕ using hxx₁.le with x' hx',
    obtain ⟨n, hn⟩ := ih x' (by exact_mod_cast hxx₂.trans_eq hax'.symm) hxx₁ hyy hx',
    exact ⟨n + 1, by rw [pow_succ, ← hn, mul_comm a, ← mul_assoc, mul_inv_self, one_mul]⟩, },
end

/-- Every solution is, up to a sign, a power of a given fundamental solution. -/
lemma eq_zpow_or_neg_zpow {a₁ : solution₁ d} (h : is_fundamental a₁) (a : solution₁ d) :
  ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n :=
begin
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a,
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby,
  rcases hb with rfl | rfl | rfl | hb,
  { exact ⟨n, or.inl (by exact_mod_cast hn)⟩, },
  { exact ⟨-n, or.inl (by simp [hn])⟩, },
  { exact ⟨n, or.inr (by simp [hn])⟩, },
  { rw set.mem_singleton_iff at hb,
    rw hb,
    exact ⟨-n, or.inr (by simp [hn])⟩, }
end

end is_fundamental

open solution₁ is_fundamental

/-- When `d` is positive and not a square, then the group of solutions to the Pell equation
`x^2 - d*y^2 = 1` has a unique positive generator (up to sign). -/
theorem exists_unique_pos_generator (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃! a₁ : solution₁ d, 1 < a₁.x ∧ 0 < a₁.y ∧ ∀ a : solution₁ d, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n :=
begin
  obtain ⟨a₁, ha₁⟩ := is_fundamental.exists_of_not_is_square h₀ hd,
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, λ a (H : 1 < _ ∧ _), _⟩,
  obtain ⟨Hx, Hy, H⟩ := H,
  obtain ⟨n₁, hn₁⟩ := H a₁,
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a,
  rcases hn₂ with rfl | rfl,
  { rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁,
        ← zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁,
    cases hn₁,
    { rcases int.is_unit_iff.mp (is_unit_of_mul_eq_one _ _ $ sub_eq_zero.mp $
                (ha₁.pow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with rfl | rfl,
      { rw zpow_one, },
      { rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy,
        exact false.elim (lt_irrefl _ $ ha₁.2.1.trans Hy), } },
    { rw [← zpow_zero a₁, eq_comm] at hn₁,
      exact false.elim (ha₁.pow_ne_neg_fundamental_pow hn₁), } },
  { rw [x_neg, lt_neg] at Hx,
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx,
    norm_num at this, }
end

/-- A positive solution is a generator (up to sign) of the group of all solutions to the
Pell equation `x^2 + d*y^2 = 1` if and only if it is a fundamental solution. -/
theorem pos_generator_iff_fundamental (a : solution₁ d) :
  (1 < a.x ∧ 0 < a.y ∧ ∀ b : solution₁ d, ∃ n : ℤ, b = a ^ n ∨ b = -a ^ n) ↔ is_fundamental a :=
begin
  refine ⟨λ h, _, λ H, ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩,
  have h₀ := d_pos_of_one_lt_x h.1,
  have hd := d_nonsquare_of_one_lt_x h.1,
  obtain ⟨a₁, ha₁⟩ := is_fundamental.exists_of_not_is_square h₀ hd,
  obtain ⟨b, hb₁, hb₂⟩ := exists_unique_pos_generator h₀ hd,
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩],
end

end pell
