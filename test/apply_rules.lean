import data.int.order.basic
import data.nat.pow

open nat

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]

@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules with mono_rules

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules with mono_rules

-- test that metavariables created for implicit arguments don't get stuck
example (P : ℕ → Type) (f : Π {n : ℕ}, P n → P (n + 1)) (g : P 0) : P 2 :=
begin
  apply_rules [f, g],
end

/-
Test that there are no conflicts between attribute and declaration names.
After #13227 there is little chance of ambiguity here, but this is still a valid test.
-/

@[user_attribute]
meta def p_rules_attr : user_attribute :=
{ name := `p_rules,
  descr := "testing" }

constant P : ℕ → Prop

axiom p_rules : P 0

@[p_rules] axiom foo : P 10

example : P 0 := by success_if_fail {apply_rules with p_rules}; apply_rules [p_rules]
example : P 10 := by apply_rules with p_rules 60

attribute [p_rules] pow_lt_pow_of_lt_left

open nat

-- This tests for the following bug:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/namespace.20affects.20behaviour.20of.20.60apply_list_expr.60
example {x y : ℤ} (n : ℕ) (h1 : x < y) (h2 : 0 ≤ x) (h3 : 0 < n) : x ^ n < y ^ n :=
by apply_rules with p_rules
