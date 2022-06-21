/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Dhruv Bhatia
-/

import tactic.polyrith
import data.real.basic

/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10):
  3*x + 2*y = 10 :=
by polyrith

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by polyrith

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by polyrith

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
  -3*x - 3*y - 4*z = 2 :=
by polyrith

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
  x + 2.2*y + 2*z - 5*w = -8.5 :=
by polyrith

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
  2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
by polyrith


/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) :
  a * a = a * b :=
by polyrith

example (a b c : ℤ) (h : a = b) :
  a * c = b * c :=
by polyrith

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
by polyrith

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
by polyrith

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by polyrith


/-! ### Cases with non-hypothesis inputs/input restrictions -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
  b = 2 / 3 :=
by polyrith only [ha, hab]

constant term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0): a + b + c + d = 0 :=
by polyrith only [term c d, h]

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by polyrith [h a b, hqc]

constant bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 :=
by polyrith [bad a, bad (b^2)]

/-! ### Case over arbitrary field/ring -/

example {α} [h : comm_ring α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
  c * (a*f - b*e) = 0 :=
by polyrith

example {K : Type*} [field K] [invertible 2] [invertible 3]
  {ω p q r s t x: K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) :=
begin
  have hs_nonzero : s ≠ 0,
  { contrapose! hp_nonzero with hs_nonzero,
    polyrith,
     },
  have H' : 2 * q = s ^ 3 - t ^ 3,
  { rw ← mul_left_inj' (pow_ne_zero 3 hs_nonzero),
    polyrith,},
  polyrith,
end

/-!
### With trace enabled
Here, the tactic will trace the command that gets sent to sage,
and so the tactic will not succeed
-/

set_option trace.polyrith true

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
  -y + 2*x + 4 = -16 :=
by polyrith

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
  c * a + b = c * b + 1 :=
by polyrith

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0): a + b + c + d = 0 :=
by polyrith only [term c d, h]

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc :=
by polyrith [h a b, hqc]
