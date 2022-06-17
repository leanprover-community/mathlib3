/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial.basic

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `mv_polynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism
  `mv_polynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `mv_polynomial.counit` is an “absolute” variant with `R = ℤ`
* `mv_polynomial.counit_nat` is an “absolute” variant with `R = ℕ`

-/

namespace mv_polynomial
open function

variables (A B R : Type*) [comm_semiring A] [comm_semiring B] [comm_ring R] [algebra A B]

/-- `mv_polynomial.acounit A B` is the natural surjective algebra homomorphism
`mv_polynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`,
and `mv_polynomial.counit_nat` for the “absolute” variant with `A = ℕ`. -/
noncomputable def acounit : mv_polynomial B A →ₐ[A] B :=
aeval id

variables {B}

@[simp] lemma acounit_X (b : B) : acounit A B (X b) = b := aeval_X _ b

variables {A} (B)

@[simp] lemma acounit_C (a : A) : acounit A B (C a) = algebra_map A B a := aeval_C _ a

variables (A)

lemma acounit_surjective : surjective (acounit A B) := λ b, ⟨X b, acounit_X A b⟩

/-- `mv_polynomial.counit R` is the natural surjective ring homomorphism
`mv_polynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring,
and `mv_polynomial.counit_nat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def counit : mv_polynomial R ℤ →+* R :=
acounit ℤ R

/-- `mv_polynomial.counit_nat A` is the natural surjective ring homomorphism
`mv_polynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring
and `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`. -/
noncomputable def counit_nat : mv_polynomial A ℕ →+* A :=
acounit ℕ A


lemma counit_surjective : surjective (counit R) := acounit_surjective ℤ R
lemma counit_nat_surjective : surjective (counit_nat A) := acounit_surjective ℕ A

lemma counit_C (n : ℤ) : counit R (C n) = n := acounit_C _ _
lemma counit_nat_C (n : ℕ) : counit_nat A (C n) = n := acounit_C _ _

variables {R A}

@[simp] lemma counit_X (r : R) : counit R (X r) = r := acounit_X _ _
@[simp] lemma counit_nat_X (a : A) : counit_nat A (X a) = a := acounit_X _ _

end mv_polynomial
