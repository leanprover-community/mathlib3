/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.triv_sq_zero_ext

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0`. They are a special case of
`triv_sq_zero_ext R M` with `M = R`.

## Notation

In the `dual_number` locale:

* `R[ε]` is a shorthand for `dual_number R`
* `ε` is a shorthand for `dual_number.eps`

## Main definitions

* `dual_number`
* `dual_number.eps`
* `dual_number.lift`

## Implementation notes

Rather than duplicating the API of `triv_sq_zero_ext`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/

variables {R : Type*}

/-- The type of dual numbers, numbers of the form $a + bε$ where $ε^2 = 0$.-/
abbreviation dual_number (R : Type*) : Type* := triv_sq_zero_ext R R

/-- The unit element $ε$ that squares to zero. -/
def dual_number.eps [has_zero R] [has_one R] : dual_number R := triv_sq_zero_ext.inr 1

localized "notation (name := dual_number.eps) `ε` := dual_number.eps" in dual_number
localized "postfix (name := dual_number) `[ε]`:1025 := dual_number" in dual_number

open_locale dual_number

namespace dual_number

open triv_sq_zero_ext

@[simp] lemma fst_eps [has_zero R] [has_one R] : fst ε = (0 : R) := fst_inr _ _
@[simp] lemma snd_eps [has_zero R] [has_one R] : snd ε = (1 : R) := snd_inr _ _

/-- A version of `triv_sq_zero_ext.snd_mul` with `*` instead of `•`. -/
@[simp] lemma snd_mul [semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
snd_mul _ _

@[simp] lemma eps_mul_eps [semiring R] : (ε * ε : R[ε]) = 0 := inr_mul_inr _ _ _

@[simp] lemma inr_eq_smul_eps [mul_zero_one_class R] (r : R) : inr r = (r • ε : R[ε]) :=
ext (mul_zero r).symm (mul_one r).symm

/-- For two algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext] lemma alg_hom_ext {A} [comm_semiring R] [semiring A] [algebra R A]
  ⦃f g : R[ε] →ₐ[R] A⦄ (h : f ε = g ε) : f = g :=
alg_hom_ext' $ linear_map.ext_ring $ h

variables {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

/-- A universal property of the dual numbers, providing a unique `R[ε] →ₐ[R] A` for every element
of `A` which squares to `0`.

This isomorphism is named to match the very similar `complex.lift`. -/
@[simps {attrs := []}]
def lift : {e : A // e * e = 0} ≃ (R[ε] →ₐ[R] A) :=
equiv.trans
  (show {e : A // e * e = 0} ≃ {f : R →ₗ[R] A // ∀ x y, f x * f y = 0}, from
    (linear_map.ring_lmap_equiv_self R ℕ A).symm.to_equiv.subtype_equiv $ λ a, begin
      dsimp,
      simp_rw smul_mul_smul,
      refine ⟨λ h x y, h.symm ▸ smul_zero _, λ h, by simpa using h 1 1⟩,
    end)
  triv_sq_zero_ext.lift

/- When applied to `ε`, `dual_number.lift` produces the element of `A` that squares to 0. -/
@[simp]
lemma lift_apply_eps (e : {e : A // e * e = 0}) : lift e (ε : R[ε]) = e :=
(triv_sq_zero_ext.lift_aux_apply_inr _ _ _).trans $ one_smul _ _

/- Lifting `dual_number.eps` itself gives the identity. -/
@[simp]
lemma lift_eps : lift ⟨ε, by exact eps_mul_eps⟩ = alg_hom.id R R[ε] :=
alg_hom_ext $ lift_apply_eps _

end dual_number
