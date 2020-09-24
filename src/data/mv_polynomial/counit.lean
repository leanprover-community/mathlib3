/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial.basic

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `mv_polynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `A`,
then there is a natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
     obtained by `X a ↦ a`
* `mv_polynomial.counit` is an “absolute” variant with `R = ℤ`
* `mv_polynomial.counit_nat` is an “absolute” variant with `R = ℕ`

-/

namespace mv_polynomial
open function

variables (A B R : Type*) [comm_semiring A] [comm_semiring B] [comm_ring R] [algebra A B]

/-- `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism
`mv_polynomial A R →ₐ[R] A` obtained by `X a ↦ a`.

See `mv_polynomial.counit` for the “absolute” variant with `R = ℤ`,
and `mv_polynomial.counit_nat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def acounit : mv_polynomial B A →ₐ[A] B :=
aeval id

lemma acounit_surjective : surjective (acounit A B) :=
λ a, ⟨X a, eval₂_hom_X' _ _ _⟩

/-- `mv_polynomial.counit R` is the natural surjective ring homomorphism
`mv_polynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring,
and `mv_polynomial.counit_nat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def counit : mv_polynomial R ℤ →+* R :=
acounit ℤ R

lemma counit_surjective : surjective (counit R) :=
acounit_surjective ℤ R

/-- `mv_polynomial.counit_nat R` is the natural surjective ring homomorphism
`mv_polynomial R ℕ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring
and `mv_polynomial.counit` for the “absolute” variant with `R = ℤ`. -/
noncomputable def counit_nat : mv_polynomial A ℕ →+* A :=
acounit ℕ A

lemma counit_nat_surjective : surjective (counit_nat A) :=
acounit_surjective ℕ A

end mv_polynomial
