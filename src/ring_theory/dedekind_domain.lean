import ring_theory.fractional_ideal
import ring_theory.principal_ideal_domain

universes u v

open localization

namespace ring

open fractional_ideal

variables {R : Type u} {K : Type v} [field K]

/-- Condition (DD3) of being a Dedekind domain: all nonzero fractional ideals are invertible. -/
def DD3 [integral_domain R] (g : fraction_map R K) : Prop :=
∀ {I : fractional_ideal g}, I ≠ 0 → I * I⁻¹ = 1

lemma DD3_of_principal_ideal_domain [principal_ideal_domain R] (g : fraction_map R K) : DD3 g :=
λ I hI, fractional_ideal.invertible_of_principal I hI

end ring
