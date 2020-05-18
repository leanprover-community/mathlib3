import ring_theory.fractional_ideal
import ring_theory.principal_ideal_domain

universes u

open localization

namespace ring

/-- A dedekind domain is an integral domain that satisfies one of some equivalent conditions.

  In this case we use that all nonzero fractional ideals are invertible. -/
class dedekind_domain (R : Type u) extends integral_domain R :=
(ideal_mul_inv_cancel : ∀ {I : fractional_ideal R (non_zero_divisors R)}, I ≠ 0 → I * I⁻¹ = 1)

variables {R : Type u} [integral_domain R] {I : fractional_ideal R (non_zero_divisors R)}

end ring
