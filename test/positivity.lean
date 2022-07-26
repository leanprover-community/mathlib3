import analysis.normed.group.basic
import data.real.sqrt
import tactic.positivity

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/

/- ## Numeric goals -/

example : 0 ≤ 0 := by positivity

example : 0 ≤ 3 := by positivity

example : 0 < 3 := by positivity

/- ## Goals working directly from a hypothesis -/

example {a : ℤ} (ha : 0 ≤ a) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 ≤ a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a := by positivity

example {a b : ℤ} (h : 0 ≤ a + b) : 0 ≤ a + b := by positivity

/- ## Tests of the @[positivity] plugin tactics (addition, multiplication, division) -/

example {a : ℤ} (ha : 3 < a) : 0 ≤ a + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 ≤ 3 + a + b + b + 14 := by positivity

example {H : Type*} [linear_ordered_add_comm_group H] {a b : H} (ha : 0 < a) (hb : 0 ≤ b) :
  0 ≤ a + a + b :=
by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a + a := by positivity

example {a b : ℚ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

-- TODO: this fails because `div_nonneg` doesn't apply directly to `ℤ` -- it requires a linearly
-- ordered field
-- example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

example {a : ℕ} : 0 < a ^ 0 := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 2 + a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a ^ 2 + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 ≤ 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 < 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {x : ℚ} (hx : 0 ≤ x) : 0 ≤ x⁻¹ := by positivity

example {a : ℤ} : 0 ≤ |a| := by positivity

example {a : ℤ} : 0 < |a| + 3 := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ real.sqrt a := by positivity

example {a : ℝ} (ha : 0 ≤ a) : 0 < real.sqrt (a + 3) := by positivity

example {a b : ℤ} (ha : 3 < a) : 0 ≤ min a (b ^ 2) := by positivity

-- test that the tactic can ignore arithmetic operations whose associated extension tactic requires
-- more typeclass assumptions than are available
example {R : Type*} [has_zero R] [has_div R] [linear_order R] {a b c : R} (h1 : 0 < a) (h2 : 0 < b)
  (h3 : 0 < c) :
  0 < max (a / b) c :=
by positivity

example : 0 ≤ max 3 4 := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity

example {b : ℤ} : 0 ≤ max (b ^ 2) 0 := by positivity

example : 0 ≤ max (0:ℤ) (-3) := by positivity

example : 0 ≤ max (-3 : ℤ) 5 := by positivity

example {V : Type*} [normed_add_comm_group V] (x : V) : 0 ≤ ∥x∥ := by positivity

example {X : Type*} [metric_space X] (x y : X) : 0 ≤ dist x y := by positivity

/- ## Tests that the tactic is agnostic on reversed inequalities -/

example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity

example {a : ℤ} (ha : a > 0) : a ≥ 0 := by positivity
