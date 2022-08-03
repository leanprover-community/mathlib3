import algebra.ring.basic
import tactic.field_simp
import tactic.ring

/-!
## `field_simp` tests.

Check that `field_simp` works for units of a ring.
-/

variables {R : Type*} [comm_ring R]

/--
Check that `divp_add_divp_same` takes priority over `divp_add_divp`.
-/
example (a b : R) (u : Rˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u :=
by field_simp

/--
Check that `divp_sub_divp_same` takes priority over `divp_sub_divp`.
-/
example (a b : R) (u : Rˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u :=
by field_simp

/--
Combining `eq_divp_iff_mul_eq` and `divp_eq_iff_mul_eq`.
-/
example (a c : R) (b d : Rˣ)  : a /ₚ b = c /ₚ d ↔ a * d = c * b :=
by field_simp

/--
Making sure inverses of units are rewritten propperly.
-/
example (x : Rˣ) : ↑x⁻¹ = 1 /ₚ x :=
by field_simp

/--
Checking arithmetic expressions.
-/
example (a b c d e f g : R) (u : Rˣ) :
(f - (e + c * -(a /ₚ u) * b + d) - g) = (f * u - (e * u + c * (-a) * b + d * u) - g * u) /ₚ u :=
by field_simp

/--
Division of units.
-/
example (a : R) (u₁ u₂ : Rˣ) : a /ₚ (u₁ / u₂) = a * u₂ /ₚ u₁ :=
by field_simp

example (a : R) (b c : Rˣ) : a /ₚ b /ₚ c = a /ₚ (c * b) :=
by field_simp
