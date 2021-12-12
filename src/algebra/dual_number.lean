/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.triv_sq_zero_ext

/-!
# Dual numbers

The dual numbers are a special case of `triv_sq_zero_ext R M` with `R = M`, with notation `𝔻[R]` in
the `dual_number` locale.

## Main definitions

* `dual_number.eps`
* `dual_number.lift`

## Implementation notes

Rather than duplicating the API of `triv_sq_zero_ext`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/

variables {R : Type*}

abbreviation dual_number (R : Type*) : Type* := triv_sq_zero_ext R R

localized "notation `𝔻[` R `]` := dual_number R" in dual_number

open_locale dual_number

namespace dual_number

open triv_sq_zero_ext

/-- The unit element that squares to zero -/
def eps [has_zero R] [has_one R] : 𝔻[R] := inr 1

@[simp] lemma fst_eps [has_zero R] [has_one R] : fst eps = (0 : R) := fst_inr _
@[simp] lemma snd_eps [has_zero R] [has_one R] : snd eps = (1 : R) := snd_inr _

@[simp] lemma eps_mul_eps [semiring R] : (eps * eps : 𝔻[R]) = 0 := inr_mul_inr _ _ _

@[simp] lemma inr_eq_smul_eps [mul_zero_one_class R] (r : R) : inr r = (r • eps : 𝔻[R]) :=
ext (mul_zero r).symm (mul_one r).symm

@[ext]
lemma alg_hom_ext {A} [comm_semiring R] [semiring A] [algebra R A]
  ⦃f g : 𝔻[R] →ₐ[R] A⦄ (h : f eps = g eps) : f = g :=
alg_hom_ext' $ linear_map.ext_ring $ h

variables {A : Type*} [comm_semiring R] [semiring A] [algebra R A]

/-- There is an alg_hom from the dual numbers over `R` to any `R`-algebra with an element that
squares to `0`.

See `dual_number.lift` for this as an equiv. -/
def lift_aux (e : A) (he : e * e = 0) : 𝔻[R] →ₐ[R] A :=
alg_hom.of_linear_map
  ((algebra.linear_map _ _).comp (triv_sq_zero_ext.fst_hom R R).to_linear_map
    + (linear_map.to_span_singleton _ _ e).comp (triv_sq_zero_ext.snd_hom R R))
  (show algebra_map R _ 1 + (0 : R) • e = 1, by rw [zero_smul, map_one, add_zero])
  (triv_sq_zero_ext.ind $ λ r₁ m₁, triv_sq_zero_ext.ind $ λ r₂ m₂, begin
    dsimp [triv_sq_zero_ext.fst_hom],
    simp only [add_zero, zero_add, add_mul, mul_add, smul_mul_smul, he, smul_zero],
    rw [←ring_hom.map_mul, add_smul, ←algebra.commutes _ (m₁ • e), ←algebra.smul_def,
        ←algebra.smul_def, add_right_comm, add_assoc, mul_smul, mul_smul],
  end)

@[simp] lemma lift_aux_apply_eps (e : A) (he : e * e = 0) : lift_aux e he (eps : 𝔻[R]) = e :=
show algebra_map R A 0 + (1 : R) • e = e, by rw [ring_hom.map_zero, one_smul, zero_add]

/-- A universal property of the dual numbers, providing a unique `𝔻[R] →ₐ[R] A` for every element
of `A` which squares to `-1`.

This isomorphism is named to match the very similar `complex.lift`. -/
@[simps]
def lift : {e : A // e * e = 0} ≃ (𝔻[R] →ₐ[R] A) :=
{ to_fun := λ e, lift_aux e e.prop,
  inv_fun := λ F, ⟨F eps, (F.map_mul _ _).symm.trans $ (F.congr_arg eps_mul_eps).trans F.map_zero⟩,
  left_inv := λ e, by { ext, exact lift_aux_apply_eps _ e.prop },
  right_inv := λ F, by { ext, exact lift_aux_apply_eps _ _, } }

/- When applied to `eps` itself, `lift` is the identity. -/
@[simp]
lemma lift_aux_eps : lift_aux eps (by exact eps_mul_eps) = alg_hom.id R 𝔻[R] :=
alg_hom_ext $ lift_aux_apply_eps _ _

end dual_number
