import tactic.ring_exp

universes u

set_option trace.app_builder true

-- Tests for addition.
example (a b : ℚ) : a = a := by ring_exp
example (a b : ℚ) : a + b = a + b := by ring_exp
example (a b : ℚ) : b + a = a + b := by ring_exp
example (a b : ℤ) : a + b + b = b + (a + b) := by ring_exp
example (a b c : ℕ) : a + b + b + (c + c) = c + (b + c) + (a + b) := by ring_exp
-- Tests for constants.
example (a : ℕ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
example (a : ℤ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
-- Tests for multiplication.
example (a : ℕ) : 0 = a * 0 := by ring_exp_eq
example (a : ℕ) : a = a * 1 := by ring_exp
example (a : ℕ) : a + a = a * 2 := by ring_exp
example (a b : ℤ) : a * b = b * a := by ring_exp
example (a b : ℕ) : a * 4 * b + a = a * (4 * b + 1) := by ring_exp
-- Tests for exponentiation.
example : 0 ^ 1 = 0 := by ring_exp
example (a : ℕ) : a ^ 0 = 1 := by ring_exp
example (a : ℕ) : a ^ 1 = a := by ring_exp
example (a : ℕ) : a ^ 2 = a * a := by ring_exp
example (a b : ℕ) : a ^ b = a ^ b := by ring_exp
example (a b : ℕ) : a ^ (b + 1) = a * a ^ b := by ring_exp
example (n : ℕ) (a m : ℕ) : a * a^n * m = a^(n+1) * m := by ring_exp
example (n : ℕ) (a m : ℕ) : m * a^n * a = a^(n+1) * m := by ring_exp
example (n : ℕ) (a m : ℤ) : a * a^n * m = a^(n+1) * m := by ring_exp
example (n : ℕ) (m : ℤ) : 2 * 2^n * m = 2^(n+1) * m := by ring_exp
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring_exp
example (n m : ℕ) (a : ℤ) : (a ^ n)^m = a^(n * m) := by ring_exp
example (n m : ℕ) (a : ℤ) : a^(n^0) = a^1 := by ring_exp
example (n : ℕ) : 0^(n + 1) = 0 := by ring_exp
example {α} [comm_ring α] (x : α) (k : ℕ) : x ^ (k + 2) = x * x * x^k := by ring_exp
example {α} [comm_ring α] (k : ℕ) (x y z : α) :
  x * (z * (x - y)) + (x * (y * y ^ k) - y * (y * y ^ k)) = (z * x + y * y ^ k) * (x - y)
:= by ring_exp

-- Powers of sums
example (a b : ℤ) : (a + b)^2 = a^2 + b^2 + a * b + b * a := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
-- Coefficients and negation
example (a : ℚ) : (1/2) * a + (1/2) * a = a := by ring_exp
example {α} [comm_ring α] (a : α) : a - a = 0 := by ring_exp_eq
example (a : ℤ) : a - a = 0 := by ring_exp
example (a : ℤ) : a + - a = 0 := by ring_exp
example (a : ℤ) : - a = (-1) * a := by ring_exp
example (a b : ℕ) : a - b + a + a = a - b + 2 * a := by ring_exp -- Here, (a - b) is treated as an atom.

example {α} [comm_ring α] (a b c : α) : b ^ 0 = 1 := by ring_exp_eq
example {α} [comm_ring α] (a b c : α) : b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring_exp_eq
constant f {α} : α → α
example {α : Type} [linear_ordered_field α] (x : α) :
  2 * x + 1 * 1 - (2 * f (x + 1 / 2) + 2 * 1) + (1 * 1 - (2 * x - 2 * f (x + 1 / 2))) = 0
:= by ring_exp_eq
example {α : Type u} [linear_ordered_field α] (x : α) :
  f (x + 1 / 2) ^ 1 * -2 + (f (x + 1 / 2) ^ 1 * 2 + 0) = 0
:= by ring_exp_eq

-- This is a somewhat subtle case: `-c/b` is parsed as `(-c)/b`,
-- so we can't simply treat both sides of the division as atoms.
-- Instead, we follow the `ring` tactic in interpreting `-c / b` as `-c * b⁻¹`,
-- with only `b⁻¹` an atom.
example {α} [linear_ordered_field α] (a b c : α) : a*(-c/b)*(-c/b) = a*((c/b)*(c/b)) := by ring_exp

/--
  This last example is copied from `data/polynomial.lean`,
  and is used as a benchmark because it was one of the slowest results.
  -/
variables {α : Type} [comm_ring α]
def pow_sub_pow_factor (x y : α) : Π {i : ℕ},{z // x^i - y^i = z*(x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
begin
  cases @pow_sub_pow_factor (k+1) with z hz,
  existsi z*x + y^(k+1),
  rw [_root_.pow_succ x, _root_.pow_succ y, ←sub_add_sub_cancel (x*x^(k+1)) (x*y^(k+1)),
  ←mul_sub x, hz],
  ring_exp_eq
end

-- Here, we check that `n - s` is not treated as `n + additive_inverse s`,
-- if `s` doesn't have an additive inverse.
constant fact : ℕ → ℕ
example (B s n : ℕ) :
  B * (fact s * ((n - s) * fact (n - s - 1))) = B * (n - s) * (fact s * fact (n - s - 1))
:= by ring_exp
