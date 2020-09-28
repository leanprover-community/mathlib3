-- this should all be moved

import algebra.invertible
import data.mv_polynomial.monad

-- ### FOR_MATHLIB

section
-- move this
lemma prod_mk_injective {α β : Type*} (a : α) :
  function.injective (prod.mk a : β → α × β) :=
by { intros b₁ b₂ h, simpa only [true_and, prod.mk.inj_iff, eq_self_iff_true] using h }
end

-- TODO: making this a global instance causes timeouts in the comm_ring instance for Witt vectors
-- :scream: :scream: :scream:
/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any `ℚ`-algebra. -/
def invertible_rat_algebra_coe_nat (R : Type*) (p : ℕ)
  [semiring R] [algebra ℚ R] [invertible (p : ℚ)] :
  invertible (p : R) :=
invertible.copy (invertible.map (algebra_map ℚ R : ℚ →* R) p) p
  (by simp only [ring_hom.map_nat_cast, coe_monoid_hom])

namespace mv_polynomial
noncomputable instance invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

/-- A natural number that is invertible when coerced to `ℚ` is also invertible
when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance invertible_rat_coe_nat (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
invertible_rat_algebra_coe_nat _ _

end mv_polynomial
-- ### end FOR_MATHLIB
