import tactic.ring
import data.real.basic
import algebra.parity

example (x y : ℕ) : x + y = y + x := by ring
example (x y : ℕ) : x + y + y = 2 * y + x := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
example {α} [comm_ring α] (x y : α) : x + y + y - x = 2 * y := by ring
example (x y : ℚ) : x / 2 + x / 2 = x := by ring
example (x y : ℚ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := by ring
example {α} [comm_semiring α] (x : α) : (x + 1) ^ 6 = (1 + x) ^ 6 := by try_for 15000 {ring}
example (n : ℕ) : (n / 2) + (n / 2) = 2 * (n / 2) := by ring
example {α} [field α] [char_zero α] (a : α) : a / 2 = a / 2 := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  a * (-c / b) * (-c / b) + -c + c = a * (c / b * (c / b)) := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example (x : ℚ) : x ^ (2 + 2) = x^4 := by ring_nf -- TODO: ring should work?
example {α} [comm_ring α] (x : α) : x ^ 2 = x * x := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * c * a = -(4 * c * a) + b ^ 2 := by ring
example {α} [linear_ordered_field α] (a b c : α) :
  b ^ 2 - 4 * a * c = 4 * a * 0 + b * b - 4 * a * c := by ring
example {α} [comm_semiring α] (x y z : α) (n : ℕ) :
  (x + y) * (z * (y * y) + (x * x ^ n + (1 + ↑n) * x ^ n * y)) =
    x * (x * x ^ n) + ((2 + ↑n) * (x * x ^ n) * y + (x * z + (z * y + (1 + ↑n) * x ^ n)) * (y * y)) := by ring
example {α} [comm_ring α] (a b c d e : α) :
  (-(a * b) + c + d) * e = (c + (d + -a * b)) * e := by ring
example (a n s: ℕ) : a * (n - s) = (n - s) * a := by ring

example (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
  x / (y / z) + y ⁻¹ + 1 / (y * -x) = -1/ (x * y) + (x * z + 1) / y :=
begin
  field_simp,
  ring
end

example {A : ℤ} (f : ℤ → ℤ) : f 0 = f (A - A) := by ring_nf
example {A : ℤ} (f : ℤ → ℤ) : f 0 = f (A + -A) := by ring_nf

example {a b c : ℝ} (h : 0 < a ^ 4 + b ^ 4 + c ^ 4) :
  a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) +
  b ^ 4 / (b ^ 4 + c ^ 4 + a ^ 4) +
  c ^ 4 / (c ^ 4 + a ^ 4 + b ^ 4)
  = 1 :=
begin
  ring_nf at ⊢ h,
  field_simp [h.ne'],
end

example (a b c d x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
  a + b / x - c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x - c) / x) :=
begin
  field_simp,
  ring
end

example : (876544 : ℤ) * -1 + (1000000 - 123456) = 0 := by ring

example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
  2 * x ^ 3 * 2 / (24 * x) = x ^ 2 / 6 :=
begin
  field_simp,
  ring
end

-- this proof style is not recommended practice
example (A B : ℕ) (H : B * A = 2) : A * B = 2 := by {ring_nf, exact H}

example (a : ℤ) : odd ((2 * a + 1) ^ 2) :=
begin
  use 2 * a ^ 2 + 2 * a,
  ring_nf,
end

example {x y : ℝ}
  (hxy : -y ^ 2 + x ^ 2 = -(5 * y) + 5 * x) :
  x ^ 2 - y ^ 2 = 5 * x - 5 * y :=
begin
  ring_nf at hxy ⊢,
  exact hxy
end

example {α} [field α] {x y : α}
  (h : 0 = (1 - x) ^ 2 * (x * (2 ^ 2 * y ^ 2 + 4 * (1 - x) ^ 2))) :
  0 = x * ((2 ^ 2 * y ^ 2 + 4 * (1 - x) ^ 2) * (1 - x) ^ 2) :=
by transitivity; [exact h, ring]

-- `ring_nf` should descend into the subexpressions `x * -a` and `-a * x`:
example {a x : ℚ} : x * -a = - a * x := by ring_nf

example (f : ℤ → ℤ) (a b : ℤ) : f (2 * a + b) + b = b + f (b + a + a) :=
begin
  success_if_fail {{ ring_nf {recursive := ff} }},
  ring_nf
end

-- instances do not have to syntactically be `monoid.has_pow`
example {R} [comm_semiring R] (x : ℕ → R) : x ^ 2 = x * x := by ring

-- even if there's an instance we don't recognize, we treat it as an atom
example {R} [field R] (x : ℕ → R) :
  (x ^ (2 : ℤ)) ^ 2 = (x ^ (2 : ℤ)) * (x ^ (2 : ℤ)) := by ring
