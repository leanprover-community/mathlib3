import data.mv_polynomial
import algebra.invertible


namespace mv_polynomial
open_locale classical
section invertible

noncomputable instance invertible_C
  (σ : Type*) {R : Type*} [comm_semiring R] (r : R) [invertible r] :
  invertible (C r : mv_polynomial σ R) :=
invertible.map ⟨C, C_1, λ x y, C_mul⟩ _

-- name??
noncomputable def invertible_rat_coe_nat (σ : Type*) (p : ℕ) [invertible (p : ℚ)] :
  invertible (p : mv_polynomial σ ℚ) :=
(mv_polynomial.invertible_C σ (p:ℚ)).copy p $ (C_eq_coe_nat p).symm

end invertible

section counit

variables (α : Type*) (β : Type*)
variables [comm_semiring α] [comm_semiring β] [algebra α β]

noncomputable def counit : mv_polynomial β α →ₐ β :=
aeval id

lemma counit_surjective : function.surjective (mv_polynomial.counit α β) :=
λ r, ⟨X r, eval₂_hom_X' _ _ _⟩

end counit

end mv_polynomial
