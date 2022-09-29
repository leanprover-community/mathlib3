import algebra.order.smul
import analysis.normed.group.basic
import analysis.special_functions.pow
import combinatorics.simple_graph.density
import data.complex.exponential
import data.rat.nnrat
import data.real.ereal
import data.real.hyperreal
import data.real.sqrt
import tactic.positivity

/-! # Tests for the `positivity` tactic

This tactic proves goals of the form `0 ≤ a` and `0 < a`.
-/

/-  Test for instantiating meta-variables.  Reported on
https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/New.20tactic.3A.20.60positivity.60/near/300639970
-/
example : 0 ≤ 0 :=
begin
  apply le_trans _ le_rfl,
  positivity,
end

open_locale ennreal nnrat nnreal

universe u
variables {α β : Type*}

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

example {a b : ℤ} (ha : 3 < a) (hb : 4 ≤ b) : 0 < 3 + a * b / 7 + b + 7 + 14 := by positivity

example {a : ℤ} (ha : 0 < a) : 0 < a / a := by positivity

/-! ### Exponentiation -/

example [ordered_semiring α] [nontrivial α] (a : α) : 0 < a ^ 0 := by positivity
example [linear_ordered_ring α] (a : α) (n : ℕ) : 0 ≤ a ^ (bit0 n) := by positivity
example [ordered_semiring α] {a : α} {n : ℕ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example [ordered_semiring α] {a : α} {n : ℕ} (ha : 0 < a) : 0 < a ^ n := by positivity

example [linear_ordered_semifield α] (a : α) : 0 < a ^ (0 : ℤ) := by positivity
example [linear_ordered_field α] (a : α) (n : ℤ) : 0 ≤ a ^ (bit0 n) := by positivity
example [linear_ordered_semifield α] {a : α} {n : ℤ} (ha : 0 ≤ a) : 0 ≤ a ^ n := by positivity
example [linear_ordered_semifield α] {a : α} {n : ℤ} (ha : 0 < a) : 0 < a ^ n := by positivity

example {a b : cardinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity
example {a b : ordinal.{u}} (ha : 0 < a) : 0 < a ^ b := by positivity

example {a b : ℝ} (ha : 0 ≤ a) : 0 ≤ a ^ b := by positivity
example {a b : ℝ} (ha : 0 < a) : 0 < a ^ b := by positivity
example {a : ℝ≥0} {b : ℝ} (ha : 0 < a) : 0 < a ^ b := by positivity
example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a ^ b := by positivity
example {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b := by positivity

example {a : ℝ} (ha : 0 < a) : 0 ≤ ⌊a⌋ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌊a⌋ := by positivity

example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉₊ := by positivity
example {a : ℝ} (ha : 0 < a) : 0 < ⌈a⌉ := by positivity
example {a : ℝ} (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := by positivity

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

example [ordered_semiring α] [ordered_add_comm_monoid β] [smul_with_zero α β]
  [ordered_smul α β] {a : α} (ha : 0 < a) {b : β} (hb : 0 < b) : 0 ≤ a • b := by positivity

example {r : ℝ} : 0 < real.exp r := by positivity

example {V : Type*} [normed_add_comm_group V] (x : V) : 0 ≤ ∥x∥ := by positivity

example {X : Type*} [metric_space X] (x y : X) : 0 ≤ dist x y := by positivity

example {E : Type*} [add_group E] {p : add_group_seminorm E} {x : E} : 0 ≤ p x := by positivity
example {E : Type*} [group E] {p : group_seminorm E} {x : E} : 0 ≤ p x := by positivity

example {r : α → β → Prop} [Π a, decidable_pred (r a)] {s : finset α} {t : finset β} :
  0 ≤ rel.edge_density r s t := by positivity
example {G : simple_graph α} [decidable_rel G.adj] {s t : finset α} :
  0 ≤ G.edge_density s t := by positivity

/- ### Canonical orders -/

example {a : ℕ} : 0 ≤ a := by positivity
example {a : ℚ≥0} : 0 ≤ a := by positivity
example {a : ℝ≥0} : 0 ≤ a := by positivity
example {a : ℝ≥0∞} : 0 ≤ a := by positivity

/- ### Coercions -/

example {a : ℕ} : (0 : ℤ) ≤ a := by positivity
example {a : ℕ} (ha : 0 < a) : (0 : ℤ) < a := by positivity
example {a : ℤ} (ha : 0 ≤ a) : (0 : ℚ) ≤ a := by positivity
example {a : ℤ} (ha : 0 < a) : (0 : ℚ) < a := by positivity
example {a : ℚ} (ha : 0 ≤ a) : (0 : ℝ) ≤ a := by positivity
example {a : ℚ} (ha : 0 < a) : (0 : ℝ) < a := by positivity
example {r : ℝ≥0} : (0 : ℝ) ≤ r := by positivity
example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ) < r := by positivity
example {r : ℝ≥0} (hr : 0 < r) : (0 : ℝ≥0∞) < r := by positivity
-- example {r : ℝ≥0} : (0 : ereal) ≤ r := by positivity -- TODO: Handle `coe_trans`
-- example {r : ℝ≥0} (hr : 0 < r) : (0 : ereal) < r := by positivity
example {r : ℝ} (hr : 0 ≤ r) : (0 : ereal) ≤ r := by positivity
example {r : ℝ} (hr : 0 < r) : (0 : ereal) < r := by positivity
example {r : ℝ} (hr : 0 ≤ r) : (0 : hyperreal) ≤ r := by positivity
example {r : ℝ} (hr : 0 < r) : (0 : hyperreal) < r := by positivity
example {r : ℝ≥0∞} : (0 : ereal) ≤ r := by positivity
example {r : ℝ≥0∞} (hr : 0 < r) : (0 : ereal) < r := by positivity

example {α : Type*} [ordered_ring α] {n : ℤ} : 0 ≤ ((n ^ 2 : ℤ) : α) := by positivity
example {r : ℝ≥0} : 0 ≤ ((r : ℝ) : ereal) := by positivity
example {r : ℝ≥0} : 0 < ((r + 1 : ℝ) : ereal) := by positivity

/- ## Tests that the tactic is agnostic on reversed inequalities -/

example {a : ℤ} (ha : a > 0) : 0 ≤ a := by positivity

example {a : ℤ} (ha : 0 < a) : a ≥ 0 := by positivity

example {a : ℤ} (ha : a > 0) : a ≥ 0 := by positivity
