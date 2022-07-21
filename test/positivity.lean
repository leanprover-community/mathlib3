import tactic.positivity

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/

/- ## Numeric goals -/

example : 0 ≤ 0 := by positivity

example : 0 ≤ 3 := by positivity

example : 0 < 3 := by positivity

/- ## Goals working directly from a hypothesis -/

example {a : ℤ} (ha : 0 ≤ a) : 0 ≤ a := by positivity -- fails

example {a : ℤ} (ha : 0 < a) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 ≤ a) : 0 < a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a := by positivity

example {a b : ℤ} (h : 0 ≤ a + b) : 0 ≤ a + b := by positivity -- fails

/- ## Tests of the @[positivity] plugin tactics (addition, multiplication) -/

example {a : ℤ} (ha : 3 < a) : 0 ≤ a + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 ≤ 3 + a + b + b + 14 := by positivity

example {a : ℤ} (ha : 3 < a) : 0 < a + a := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a + b + b + 7 + 14 := by positivity

/- ## Tests of other @[positivity] plugin tactics not yet implemented

Eg. powers, division, absolute value.  All these tests currently fail. -/

example {a : ℤ} (ha : 3 < a) : a ^ 2 + a ≥ 0 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 ≤ 3 * a ^ 2 * b + b * 7 + 14 := by positivity

example {a : ℤ} (ha : 3 < a) : a ^ 2 + a > 0 := by positivity

example {a b : ℤ} (ha : 3 < a) (hb : b ≥ 4) : 0 < 3 * a ^ 2 * b + b * 7 + 14 := by positivity

/- ## Tests that the tactic is agnostic on reversed inequalities -/

example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity

example {a : ℤ} (ha : a > 0) : a ≥ 0 := by positivity
