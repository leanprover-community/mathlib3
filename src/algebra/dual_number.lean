/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.triv_sq_zero_ext

/-!
# Dual numbers

The dual numbers are a special case of `triv_sq_zero_ext R M` with `R = M`, with notation `𝔻[R]` in
the `dual_number` locale.

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

localized "notation `𝔻[` R `]` := dual_number R" in dual_number

open_locale dual_number

namespace dual_number

open triv_sq_zero_ext

/-- The unit element $ε$ that squares to zero. -/
def eps [has_zero R] [has_one R] : 𝔻[R] := inr 1

@[simp] lemma fst_eps [has_zero R] [has_one R] : fst eps = (0 : R) := fst_inr _ _
@[simp] lemma snd_eps [has_zero R] [has_one R] : snd eps = (1 : R) := snd_inr _ _

@[simp] lemma eps_mul_eps [semiring R] : (eps * eps : 𝔻[R]) = 0 := inr_mul_inr _ _ _

@[simp] lemma inr_eq_smul_eps [mul_zero_one_class R] (r : R) : inr r = (r • eps : 𝔻[R]) :=
ext (mul_zero r).symm (mul_one r).symm

/-- For two algebra morphisms out of `𝔻[R]` agree, it suffices for them to agree on `eps`. -/
@[ext] lemma alg_hom_ext {A} [comm_semiring R] [semiring A] [algebra R A]
  ⦃f g : 𝔻[R] →ₐ[R] A⦄ (h : f eps = g eps) : f = g :=
alg_hom_ext' $ linear_map.ext_ring $ h

variables {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

/-- A universal property of the dual numbers, providing a unique `𝔻[R] →ₐ[R] A` for every element
of `A` which squares to `-1`.

This isomorphism is named to match the very similar `complex.lift`. -/
@[simps]
def lift : {e : A // e * e = 0} ≃ (𝔻[R] →ₐ[R] A) :=
equiv.trans
  (show {e : A // e * e = 0} ≃ {f : R →ₗ[R] A // ∀ x y, f x * f y = 0}, from
    (linear_map.ring_lmap_equiv_self R ℕ A).symm.to_equiv.subtype_equiv $ λ a, begin
      dsimp,
      simp_rw smul_mul_smul,
      refine ⟨λ h x y, h.symm ▸ smul_zero _, λ h, by simpa using h 1 1⟩,
    end)
  triv_sq_zero_ext.lift

/- When applied to `eps` itself, `lift` is the identity. -/
@[simp]
lemma lift_apply_eps (e : {e : A // e * e = 0}) : lift e (eps : 𝔻[R]) = e :=
(triv_sq_zero_ext.lift_aux_apply_inr _ _ _).trans $ one_smul _ _

/- When applied to `eps` itself, `lift` is the identity. -/
@[simp]
lemma lift_eps : lift ⟨eps, by exact eps_mul_eps⟩ = alg_hom.id R 𝔻[R] :=
alg_hom_ext $ lift_apply_eps _

end dual_number
