/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Heather Macbeth
-/

import analysis.special_functions.trigonometric.complex

/-!
# IMO 1962 Q4

Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.

Since Lean does not have a concept of "simplest form", we just express what is
in fact the simplest form of the set of solutions, and then prove it equals the set of solutions.
-/

open real
open_locale real
noncomputable theory

def problem_equation (x : ℝ) : Prop := cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

def solution_set : set ℝ :=
{ x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 ∨ x = (2 * ↑k + 1) * π / 6 }

/-
The key to solving this problem simply is that we can rewrite the equation as
a product of terms, shown in `alt_formula`, being equal to zero.
-/

def alt_formula (x : ℝ) : ℝ := cos x * (cos x ^ 2 - 1/2) * cos (3 * x)

lemma cos_sum_equiv {x : ℝ} :
(cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = alt_formula x :=
begin
  simp only [real.cos_two_mul, cos_three_mul, alt_formula],
  ring
end

lemma alt_equiv {x : ℝ} : problem_equation x ↔ alt_formula x = 0 :=
begin
  rw [ problem_equation, ← cos_sum_equiv, div_eq_zero_iff, sub_eq_zero],
  norm_num,
end

lemma finding_zeros {x : ℝ} :
alt_formula x = 0 ↔ cos x ^ 2 = 1/2 ∨ cos (3 * x) = 0 :=
begin
  simp only [alt_formula, mul_assoc, mul_eq_zero, sub_eq_zero],
  split,
  { rintro (h1|h2),
    { right,
      rw [cos_three_mul, h1],
      ring },
    { exact h2 } },
  { exact or.inr }
end

/-
Now we can solve for `x` using basic-ish trigonometry.
-/

lemma solve_cos2_half {x : ℝ} : cos x ^ 2 = 1/2 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 :=
begin
  rw cos_sq,
  simp only [add_right_eq_self, div_eq_zero_iff],
  norm_num,
  rw cos_eq_zero_iff,
  split;
  { rintro ⟨k, h⟩,
    use k,
    linarith },
end

lemma solve_cos3x_0 {x : ℝ} : cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 6 :=
begin
  rw cos_eq_zero_iff,
  refine exists_congr (λ k, _),
  split; intro; linarith
end

/-
The final theorem is now just gluing together our lemmas.
-/

theorem imo1962_q4 {x : ℝ} : problem_equation x ↔ x ∈ solution_set :=
begin
  rw [alt_equiv, finding_zeros, solve_cos3x_0, solve_cos2_half],
  exact exists_or_distrib.symm
end


/-
We now present a second solution.  The key to this solution is that, when the identity is
converted to an identity which is polynomial in `a` := `cos x`, it can be rewritten as a product of
terms, `a ^ 2 * (2 * a ^ 2 - 1) * (4 * a ^ 2 - 3)`, being equal to zero.
-/

/-- Someday, when there is a Grobner basis tactic, try to automate this proof. (A little tricky --
the ideals are not the same but their Jacobson radicals are.) -/
lemma formula {R : Type*} [comm_ring R] [is_domain R] [char_zero R] (a : R) :
  a ^ 2 + (2 * a ^ 2 - 1) ^ 2 + (4 * a ^ 3 - 3 * a) ^ 2 = 1
  ↔ (2 * a ^ 2 - 1) * (4 * a ^ 3 - 3 * a) = 0 :=
calc a ^ 2 + (2 * a ^ 2 - 1) ^ 2 + (4 * a ^ 3 - 3 * a) ^ 2 = 1
    ↔ a ^ 2 + (2 * a ^ 2 - 1) ^ 2 + (4 * a ^ 3 - 3 * a) ^ 2 - 1 = 0 : by rw ← sub_eq_zero
... ↔ 2 * a ^ 2 * (2 * a ^ 2 - 1) * (4 * a ^ 2 - 3) = 0 : by { split; intros h; convert h; ring }
... ↔ a * (2 * a ^ 2 - 1) * (4 * a ^ 2 - 3) = 0 : by simp [(by norm_num : (2:R) ≠ 0)]
... ↔ (2 * a ^ 2 - 1) * (4 * a ^ 3 - 3 * a) = 0 : by { split; intros h; convert h using 1; ring }

/-
Again, we now can solve for `x` using basic-ish trigonometry.
-/

lemma solve_cos2x_0 {x : ℝ} :
  cos (2 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 :=
begin
  rw cos_eq_zero_iff,
  refine exists_congr (λ k, _),
  split; intro; linarith
end

/-
Again, the final theorem is now just gluing together our lemmas.
-/

theorem imo1962_q4' {x : ℝ} : problem_equation x ↔ x ∈ solution_set :=
calc problem_equation x
    ↔ cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1 : by refl
... ↔ cos (2 * x) = 0 ∨ cos (3 * x) = 0 : by simp [cos_two_mul, cos_three_mul, formula]
... ↔ x ∈ solution_set : by { rw [solve_cos2x_0, solve_cos3x_0, ← exists_or_distrib], refl }
