import algebraic_geometry.elliptic_curve.EllipticCurve
import algebraic_geometry.elliptic_curve.group_law
import group_theory.finiteness
import number_theory.number_field

namespace EllipticCurve

-- let `K` be a number field, and `E` be an elliptic curve over `K`
variables {K : Type*} [field K] [decidable_eq K] [number_field K]
variables (E : EllipticCurve K)

/-- The multiplication by `n` isogeny. -/
def mul_by_n (n : ℕ) : E/K →+ E/K :=
  { to_fun := λ P, n • P
  , map_zero' := by simp
  , map_add' := by simp
  }

/-- The weak Mordell-Weil theorem. -/
theorem weak_mordell_weil : fintype ((E/K) ⧸ (mul_by_n E 2).range) :=
  sorry

/-- The Mordell-Weil theorem. -/
theorem mordell_weil : add_group.fg (E/K) :=
  sorry

end EllipticCurve
