import tactic.linear_combination
import data.real.basic


/-! ### Simple Cases with ℤ and two or less equations -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by linear_combination 1*h1

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by linear_combination (h1)

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  2*x + 4 = -6 :=
by linear_combination 2*h1

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by linear_combination -2*h2 + h1

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  2*x + 4 - y = -16 :=
by linear_combination 2*h1 + -1*h2

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by linear_combination -h2 + 2*h1

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  11*y = -11 :=
by linear_combination -2*h1 + 3*h2

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y = 11 :=
by linear_combination 2*h1 - 3*h2

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y = 11 + 1 - 1 :=
by linear_combination 2*h1 + -3*h2

example (x y : ℤ) (h1 : 10 = 3*x + 2*y) (h2 : 3 = 2*x + 5*y) :
  11 + 1 - 1 = -11*y :=
by linear_combination 2*h1 - 3*h2


/-! ### More complicated cases with two equations -/

example (x y : ℤ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by linear_combination 2*h1 - h2

example (x y : ℚ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y + 1 = 11 + 1 :=
by linear_combination 2*h1 - 3*h2

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) :
  b = 2 / 3 :=
by linear_combination ha/6 + hab/3


/-! ### Cases with more than 2 equations -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 :=
by linear_combination 1/6 * ha + 1/3 * hab + 0 * hignore

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by linear_combination ha - hb - 2*hc

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  6*x = -10 :=
by linear_combination 1*ha + 4*hb - 3*hc

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  10 = 6*-x :=
by linear_combination ha + 4*hb - 3*hc

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by linear_combination 2*h1 + 1*h2 - 2*h3

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by linear_combination 2*h1 + h2 - 2*h3

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
by linear_combination 2*h1 -1*h2 +3*h3 -3*h4

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  6 - 3*c + 3*a + 3*d = 2*b - d + 12 - 3*a :=
by linear_combination 2*h2 -h3 +3*h1 -3*h4


/-! ### Cases with non-hypothesis inputs -/

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by linear_combination 3 * h a b + hqc

constant bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 :=
by linear_combination bad a + b * bad (b*b)

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) :
  a * a = a * b :=
by linear_combination a*h

example (a b c : ℤ) (h : a = b) :
  a * c = b * c :=
by linear_combination c*h

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
by linear_combination c*h1 + h2

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
by linear_combination x*y*h1 + 2*h2

example {α} [h : comm_ring α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
  c * (a*f - b*e) = 0 :=
by linear_combination e*h1 + a*h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by linear_combination (x + 2*y)*hzw

/-! ### Cases that explicitly use a linear_combination_config -/

example (x y : ℚ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y + 1 = 11 + 1 :=
by linear_combination 2*h1 -3*h2 with {normalization_tactic := `[ring]}

example (x y : ℚ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
  -11*y + 1 = 11 + 1 :=
by linear_combination 2*h1 + -3*h2 with {normalization_tactic := `[ring1]}

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) :
  b = 2 / 3 :=
by linear_combination 1/6*ha + 1/3*hab with {normalization_tactic := `[ring_nf]}

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by linear_combination h1 with {normalization_tactic := `[simp]}


/-! ### Cases that have linear_combination skip normalization -/


example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) :
  b = 2 / 3 :=
begin
  linear_combination 1/6*ha + 1/3*hab with {normalize := ff},
  linarith
end

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) :
  2*x = -6 :=
begin
  linear_combination 2*h1 with {normalize := ff},
  simp,
  norm_cast
end


/-! ### Cases without any arguments provided -/

-- the corner case is "just apply the normalization procedure".
-- an empty `linear_combination` at the end of a declaration is a bad edge case for the parser.
example {x y z w : ℤ} (h₁ : 3 * x = 4 + y) (h₂ : x + 2 * y = 1) : z + w = w + z :=
by linear_combination

.

-- this interacts as expected with options
example {x y z w : ℤ} (h₁ : 3 * x = 4 + y) (h₂ : x + 2 * y = 1) : z + w = w + z :=
begin
  linear_combination with {normalize := ff},
  guard_target' z + w - (w + z) - (0 - 0) = 0,
  simp [add_comm]
end

example {x y z w : ℤ} (h₁ : 3 * x = 4 + y) (h₂ : x + 2 * y = 1) : z + w = w + z :=
by linear_combination with {normalization_tactic := `[simp [add_comm]]}

/-! ### Cases where the goal is not closed -/

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
begin
  linear_combination x*y*h1 + h2,
  guard_target' (x * 3 - 7 = 0),
  linear_combination h2
end

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  6 - 3*c + 3*a + 3*d = 2*b - d + 12 - 3*a :=
begin
  linear_combination 2*h2,
  linear_combination -h3,
  linear_combination 3*h1,
  linear_combination -3*h4,
end

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
begin
  linear_combination,
  linear_combination h1 - 2 * h2,
end

/-! ### Cases that should fail -/


-- This should fail because the second coefficient has a different type than
--   the equations it is being combined with.  This was a design choice for the
--   sake of simplicity, but the tactic could potentially be modified to allow
--   this behavior.
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y + 2*x = 1 :=
begin
  success_if_fail_with_msg {linear_combination h1 + (0 : ℝ) * h2}
    "invalid type ascription, term has type
  ℝ
but is expected to have type
  ℤ",
  linear_combination h1
end


-- This fails because the linear_combination tactic requires the equations
--   and coefficients to use a type that fulfills the add_group condition,
--   and ℕ does not.
example (a b : ℕ) (h1 : a = 3) :
  a = 3 :=
begin
  success_if_fail {linear_combination h1},
  exact h1
end

example (a b : ℤ) (x y : ℝ) (hab : a = b) (hxy : x = y) : 2*x = 2*y :=
begin
  success_if_fail_with_msg {linear_combination 2*hab}
    "hab is an equality between terms of type ℤ, but is expected to be between terms of type ℝ",
  linear_combination 2*hxy
end
