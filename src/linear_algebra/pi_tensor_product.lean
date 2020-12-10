/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import group_theory.congruence
import linear_algebra.basic

/-!
# Tensor products of several semimodules over commutative semirings

## Notations

## Tags

multilinear, tensor, tensor product
-/

noncomputable theory
open_locale classical
open function

section semiring

variables {ι : Type*} {R : Type*} [comm_semiring R] [fintype ι]
variables {s : ι → Type*} [∀ i, add_comm_monoid (s i)] [∀ i, semimodule R (s i)]

namespace pi_tensor_product
include R
variables (R) (s)

/-- The relation on `free_add_monoid (Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (Π i, s i) → free_add_monoid (Π i, s i) → Prop
| of_zero : ∀ (f : Π i, s i), (∃ i, (f i = 0)) → eqv (free_add_monoid.of f) 0
| of_add : ∀ (f : Π i, s i) (i : ι) (m₁ m₂ : s i), eqv
    (free_add_monoid.of (update f i m₁) + free_add_monoid.of (update f i m₂))
    (free_add_monoid.of (update f i (m₁ + m₂)))
| of_smul : ∀ (f : Π i, s i) (i j : ι) (r : R), eqv
    (free_add_monoid.of (update f i (r • (f i))))
    (free_add_monoid.of (update f j (r • (f j))))
| add_comm : ∀ x y, eqv (x + y) (y + x)

end pi_tensor_product

variables (R) (s)

def pi_tensor_product : Type* :=
(add_con_gen (pi_tensor_product.eqv R s)).quotient

variables {R}

/- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`. -/
localized "notation `⨂[`:100 R `] ` binders `, ` r:(scoped:67 f, pi_tensor_product R f) := r"
  in tensor_product

open_locale tensor_product

namespace pi_tensor_product

section module

instance : add_comm_monoid (⨂[R] i, s i) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (pi_tensor_product.eqv R s)).add_monoid }

instance : inhabited (⨂[R] i, s i) := ⟨0⟩

variables (R) {s}

def tprod (f : Π i, s i) : ⨂[R] i, s i := add_con.mk' _ $ free_add_monoid.of f
variables {R}

notation `⨂ₜ[`:100 R`] ` binders `, ` r:(scoped:67 f, tprod R f) := r

@[elab_as_eliminator]
protected theorem induction_on
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C0 : C 0)
  (C1 : ∀ {f : Π i, s i}, C (⨂ₜ[R] i : ι, f i))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
add_con.induction_on z $ λ x, free_add_monoid.rec_on x C0 $ λ f y ih,
by { rw add_con.coe_add, exact Cp C1 ih }

lemma zero_tprod (f : Π i, s i) (hf : ∃ i, f i = 0) : ⨂ₜ[R] i, f i = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero _ hf

lemma add_tprod (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  (⨂ₜ[R] j, (update f i m₁) j) + (⨂ₜ[R] j, (update f i m₂) j) = ⨂ₜ[R] j, (update f i (m₁ + m₂)) j :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add f i m₁ m₂)

lemma smul_tprod (f : Π i, s i) (i j : ι) (r : R) :
  ⨂ₜ[R] k, (update f i (r • f i) k) = ⨂ₜ[R] k, (update f j (r • f j)) k :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _ _

end module

end pi_tensor_product

end semiring
