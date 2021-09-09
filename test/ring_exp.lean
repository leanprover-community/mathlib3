import tactic.ring_exp
import tactic.zify
import algebra.group_with_zero.power
import tactic.field_simp

universes u

section addition
/-!
  ### `addition` section

  Test associativity and commutativity of `(+)`.
-/
example (a b : ℚ) : a = a := by ring_exp
example (a b : ℚ) : a + b = a + b := by ring_exp
example (a b : ℚ) : b + a = a + b := by ring_exp
example (a b : ℤ) : a + b + b = b + (a + b) := by ring_exp
example (a b c : ℕ) : a + b + b + (c + c) = c + (b + c) + (a + b) := by ring_exp
end addition

section numerals
/-!
  ### `numerals` section

  Test that numerals behave like rational numbers.
-/
example (a : ℕ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
example (a : ℤ) : a + 5 + 5 = 0 + a + 10 := by ring_exp
example (a : ℚ) : (1/2) * a + (1/2) * a = a := by ring_exp
end numerals

section multiplication
/-!
  ### `multiplication section`

  Test that multiplication is associative and commutative.
  Also test distributivity of `(+)` and `(*)`.
-/
example (a : ℕ) : 0 = a * 0 := by ring_exp_eq
example (a : ℕ) : a = a * 1 := by ring_exp
example (a : ℕ) : a + a = a * 2 := by ring_exp
example (a b : ℤ) : a * b = b * a := by ring_exp
example (a b : ℕ) : a * 4 * b + a = a * (4 * b + 1) := by ring_exp
end multiplication

section exponentiation
/-!
  ### `exponentiation` section

  Test that exponentiation has the correct distributivity properties.
-/
example : 0 ^ 1 = 0 := by ring_exp
example : 0 ^ 2 = 0 := by ring_exp
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

-- We can represent a large exponent `n` more efficiently than just `n` multiplications:
example (a b : ℚ) : (a * b) ^ 1000000 = (b * a) ^ 1000000 := by ring_exp

example (n : ℕ) : 2 ^ (n + 1 + 1)  = 2 * 2 ^ (n + 1) :=
by ring_exp_eq

end exponentiation

section power_of_sum
/-!
  ### `power_of_sum` section

  Test that raising a sum to a power behaves like repeated multiplication,
  if needed.
-/
example (a b : ℤ) : (a + b)^2 = a^2 + b^2 + a * b + b * a := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
end power_of_sum

section negation
/-!
  ### `negation` section

  Test that negation and subtraction satisfy the expected properties,
  also in semirings such as `ℕ`.
-/
example {α} [comm_ring α] (a : α) : a - a = 0 := by ring_exp_eq
example (a : ℤ) : a - a = 0 := by ring_exp
example (a : ℤ) : a + - a = 0 := by ring_exp
example (a : ℤ) : - a = (-1) * a := by ring_exp
-- Here, (a - b) is treated as an atom.
example (a b : ℕ) : a - b + a + a = a - b + 2 * a := by ring_exp
example (n : ℕ) : n + 1 - 1 = n := by ring_exp! -- But we can force a bit of evaluation anyway.
end negation

constant f {α} : α → α
section complicated
/-!
  ### `complicated` section

  Test that complicated, real-life expressions also get normalized.
-/
example {α : Type} [linear_ordered_field α] (x : α) :
  2 * x + 1 * 1 - (2 * f (x + 1 / 2) + 2 * 1) + (1 * 1 - (2 * x - 2 * f (x + 1 / 2))) = 0
:= by ring_exp_eq
example {α : Type u} [linear_ordered_field α] (x : α) :
  f (x + 1 / 2) ^ 1 * -2 + (f (x + 1 / 2) ^ 1 * 2 + 0) = 0
:= by ring_exp_eq

example (x y : ℕ) : x + id y = y + id x := by ring_exp!

-- Here, we check that `n - s` is not treated as `n + additive_inverse s`,
-- if `s` doesn't have an additive inverse.
example (B s n : ℕ) : B * (f s * ((n - s) * f (n - s - 1))) = B * (n - s) * (f s * f (n - s - 1)) :=
by ring_exp

-- This is a somewhat subtle case: `-c/b` is parsed as `(-c)/b`,
-- so we can't simply treat both sides of the division as atoms.
-- Instead, we follow the `ring` tactic in interpreting `-c / b` as `-c * b⁻¹`,
-- with only `b⁻¹` an atom.
example {α} [linear_ordered_field α] (a b c : α) : a*(-c/b)*(-c/b) = a*((c/b)*(c/b)) := by ring_exp

-- test that `field_simp` works fine with powers and `ring_exp`.
example (x y : ℚ) (n : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
  1/ (2/(x / y))^(2 * n) + y / y^(n+1) - (x/y)^n * (x/(2 * y))^n / 2 ^n = 1/y^n :=
begin
  field_simp,
  ring_exp
end
end complicated

-- Test that `nat.succ d` gets handled as `d + 1`.
example (d : ℕ) : 2 * (2 ^ d - 1) + 1 = 2 ^ d.succ - 1 :=
begin
  zify [nat.one_le_pow'],
  ring_exp,
end

section conv
/-!
  ### `conv` section

  Test that `ring_exp` works inside of `conv`, both with and without `!`.
-/

example (n : ℕ) : (2^n * 2 + 1)^10 = (2^(n+1) + 1)^10 :=
begin
conv_rhs
{ congr,
  ring_exp, },
conv_lhs
{ congr,
  ring_exp, },
end

example (x y : ℤ) : x + id y - y + id x = x * 2 := begin
  conv_lhs { ring_exp!, },
end
end conv

section benchmark
/-!
  ### `benchmark` section

  The `ring_exp` tactic shouldn't be too slow.
-/
-- This last example was copied from `data/polynomial.lean`, because it timed out.
-- After some optimization, it doesn't.
variables {α : Type} [comm_ring α]
def pow_sub_pow_factor (x y : α) : Π {i : ℕ},{z // x^i - y^i = z*(x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
begin
  cases @pow_sub_pow_factor (k+1) with z hz,
  existsi z*x + y^(k+1),
  rw [pow_succ x, pow_succ y, ←sub_add_sub_cancel (x*x^(k+1)) (x*y^(k+1)),
  ←mul_sub x, hz],
  ring_exp_eq
end

-- Another benchmark: bound the growth of the complexity somewhat.
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 4 = (1 + x) ^ 4   := by try_for  5000 {ring_exp}
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6   := by try_for 10000 {ring_exp}
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 8 = (1 + x) ^ 8   := by try_for 15000 {ring_exp}
end benchmark
