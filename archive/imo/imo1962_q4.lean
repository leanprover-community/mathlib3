/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import data.real.pi

open real
noncomputable theory

notation `π` := real.pi

/-!
Solve the equation `(cos x)^2 + (cos 2*x)^2 + (cos 3*x)^2 = 1`.

Since Lean does not have a concept of "simplest form", we just express what is
in fact the simplest form of the set of solutions, and then prove it equals the set of solutions.
-/

def problem_equation (x : ℝ) : Prop := cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

def solution_set : set ℝ :=
{ x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 ∨ x = (2 * ↑k + 1) * π / 6 }

/-
The key to solving this problem simply is that we can rewrite the equation as
a product of terms, shown in `alt_formula`, being equal to zero.
-/

def alt_formula (x : ℝ) : ℝ := cos x * (cos x ^ 2 - 1/2) * cos (3 * x)

lemma cosx2 {x : ℝ} : cos x ^ 2 = 1 - sin x ^ 2 :=
begin
  have h1 : sin x ^ 2 = 1 - cos x ^ 2, from real.sin_square x,
  rw h1,
  ring
end

lemma cos3x {x : ℝ} : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x :=
begin
  have h1 : cos (x + 2 * x) = cos x * cos (2 * x) - sin x * sin (2 * x),
    from real.cos_add x (2 * x),
  have h2 : x + 2 * x = 3 * x, by ring,
  rw ← h2,
  rw h1,
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, pow_two],
  have h3 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2, by ring,
  rw [h3, cosx2],
  ring
end

lemma cos3x_factorization {x : ℝ} : cos (3 * x) = 4 * (cos x) * (cos x ^ 2 - 3/4) :=
by { rw cos3x, linarith }

lemma cos_sum_equiv {x : ℝ} :
(cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = alt_formula x :=
begin
  simp [real.cos_two_mul, cos3x],
  unfold alt_formula,
  rw cos3x_factorization,
  ring
end

lemma alt_equiv {x : ℝ} : problem_equation x ↔ alt_formula x = 0 :=
begin
  unfold problem_equation,
  rw ← cos_sum_equiv,
  split,
  { intro h1,
    rw h1,
    ring },
  { intro h2,
    simp at h2,
    norm_num at h2,
    exact sub_eq_zero.mp h2 }
end

/-
Since alt_formula is a product, its zeros are the zeros of the multiplicands.
The `cos x = 0` implies `cos (3 * x) = 0` so we can drop that case.
-/

lemma cosx_0_imp_cos3x_0 {x : ℝ} (h : cos x = 0) : cos (3 * x) = 0 :=
begin
  rw [cos3x, h],
  ring
end

lemma finding_zeros {x : ℝ} :
alt_formula x = 0 ↔ cos x ^ 2 = 1/2 ∨ cos (3 * x) = 0 :=
begin
  unfold alt_formula,
  simp only [mul_assoc, mul_eq_zero, sub_eq_zero],
  split,
  { intro h1,
    cases h1 with h2 h3,
    { right,
      exact cosx_0_imp_cos3x_0 h2 },
    { exact h3 } },
  { exact or.inr }
end

/-
Now we can solve for `x` using basic-ish trigonometry.
-/

lemma solve_cos2_half {x : ℝ} : cos x ^ 2 = 1/2 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 :=
begin
  rw cos_square,
  simp,
  norm_num,
  rw cos_eq_zero_iff,
  split, all_goals
  { intro h,
    cases h with k h,
    use k,
    linarith },
end

lemma solve_cos3x_0 {x : ℝ} : cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑ k + 1) * π / 6 :=
begin
  rw cos_eq_zero_iff,
  split, all_goals
  { intro h,
    cases h with k h,
    use k,
    linarith },
end

/-
The final theorem is now just gluing together our lemmas.
-/

theorem imo1962_q4 {x : ℝ} : problem_equation x ↔ x ∈ solution_set :=
begin
  rw [alt_equiv, finding_zeros, solve_cos3x_0, solve_cos2_half],
  unfold solution_set,
  split,
  { intro h,
    cases h, all_goals
    { cases h with k h,
      use k,
      finish } },
  { intro h,
    cases h with k h,
    cases h,
    { left, use k, finish },
    { right, use k, finish } }
end
