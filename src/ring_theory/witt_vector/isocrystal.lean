/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import ring_theory.witt_vector.frobenius_fraction_field

/-!

## F-isocrystals over a perfect field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

When `k` is an integral domain, so is `𝕎 k`, and we can consider its field of fractions `K(p, k)`.
The endomorphism `witt_vector.frobenius` lifts to `φ : K(p, k) → K(p, k)`; if `k` is perfect, `φ` is
an automorphism.

Let `k` be a perfect integral domain. Let `V` be a vector space over `K(p,k)`.
An *isocrystal* is a bijective map `V → V` that is `φ`-semilinear.
A theorem of Dieudonné and Manin classifies the finite-dimensional isocrystals over algebraically
closed fields. In the one-dimensional case, this classification states that the isocrystal
structures are parametrized by their "slope" `m : ℤ`.
Any one-dimensional isocrystal is isomorphic to `φ(p^m • x) : K(p,k) → K(p,k)` for some `m`.

This file proves this one-dimensional case of the classification theorem.
The construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].

## Main declarations

* `witt_vector.isocrystal`: a vector space over the field `K(p, k)` additionally equipped with a
  Frobenius-linear automorphism.
* `witt_vector.isocrystal_classification`: a one-dimensional isocrystal admits an isomorphism to one
  of the standard one-dimensional isocrystals.

## Notation

This file introduces notation in the locale `isocrystal`.
* `K(p, k)`: `fraction_ring (witt_vector p k)`
* `φ(p, k)`: `witt_vector.fraction_ring.frobenius_ring_hom p k`
* `M →ᶠˡ[p, k] M₂`: `linear_map (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂`
* `M ≃ᶠˡ[p, k] M₂`: `linear_equiv (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂`
* `Φ(p, k)`: `witt_vector.isocrystal.frobenius p k`
* `M →ᶠⁱ[p, k] M₂`: `witt_vector.isocrystal_hom p k M M₂`
* `M ≃ᶠⁱ[p, k] M₂`: `witt_vector.isocrystal_equiv p k M M₂`

## References

* [Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022]
* [Theory of commutative formal groups over fields of finite characteristic][manin1963]
* <https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf>

-/

noncomputable theory
open finite_dimensional

namespace witt_vector

variables (p : ℕ) [fact p.prime]
variables (k : Type*) [comm_ring k]
localized "notation (name := witt_vector.fraction_ring)
  `K(`p`, `k`)` := fraction_ring (witt_vector p k)" in isocrystal

section perfect_ring
variables [is_domain k] [char_p k p] [perfect_ring k p]

/-! ### Frobenius-linear maps -/

/-- The Frobenius automorphism of `k` induces an automorphism of `K`. -/
def fraction_ring.frobenius : K(p, k) ≃+* K(p, k) :=
is_fraction_ring.field_equiv_of_ring_equiv (frobenius_equiv p k)

/-- The Frobenius automorphism of `k` induces an endomorphism of `K`. For notation purposes. -/
def fraction_ring.frobenius_ring_hom : K(p, k) →+* K(p, k) := fraction_ring.frobenius p k

localized "notation (name := witt_vector.frobenius_ring_hom)
  `φ(`p`, `k`)` := witt_vector.fraction_ring.frobenius_ring_hom p k" in isocrystal

instance inv_pair₁ : ring_hom_inv_pair (φ(p, k)) _ :=
ring_hom_inv_pair.of_ring_equiv (fraction_ring.frobenius p k)

instance inv_pair₂ :
  ring_hom_inv_pair ((fraction_ring.frobenius p k).symm : K(p, k) →+* K(p, k)) _ :=
ring_hom_inv_pair.of_ring_equiv (fraction_ring.frobenius p k).symm

localized "notation (name := frobenius_ring_hom.linear_map) M ` →ᶠˡ[`:50 p `, ` k `] ` M₂ :=
  linear_map (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂" in isocrystal
localized "notation (name := frobenius_ring_hom.linear_equiv) M ` ≃ᶠˡ[`:50 p `, ` k `] ` M₂ :=
  linear_equiv (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂" in isocrystal

/-! ### Isocrystals -/

/--
An isocrystal is a vector space over the field `K(p, k)` additionally equipped with a
Frobenius-linear automorphism.
-/
class isocrystal (V : Type*) [add_comm_group V] extends module K(p, k) V :=
( frob : V ≃ᶠˡ[p, k] V )

variables (V : Type*) [add_comm_group V] [isocrystal p k V]
variables (V₂ : Type*) [add_comm_group V₂] [isocrystal p k V₂]

variables {V}

/--
Project the Frobenius automorphism from an isocrystal. Denoted by `Φ(p, k)` when V can be inferred.
-/
def isocrystal.frobenius : V ≃ᶠˡ[p, k] V := @isocrystal.frob p _ k _ _ _ _ _ _ _
variables (V)

localized "notation `Φ(`p`, `k`)` := witt_vector.isocrystal.frobenius p k" in isocrystal

/-- A homomorphism between isocrystals respects the Frobenius map. -/
@[nolint has_nonempty_instance]
structure isocrystal_hom extends V →ₗ[K(p, k)] V₂ :=
( frob_equivariant : ∀ x : V, Φ(p, k) (to_linear_map x) = to_linear_map (Φ(p, k) x) )

/-- An isomorphism between isocrystals respects the Frobenius map. -/
@[nolint has_nonempty_instance]
structure isocrystal_equiv extends V ≃ₗ[K(p, k)] V₂ :=
( frob_equivariant : ∀ x : V, Φ(p, k) (to_linear_equiv x) = to_linear_equiv (Φ(p, k) x) )

localized "notation (name := isocrystal_hom)
  M ` →ᶠⁱ[`:50 p `, ` k `] ` M₂ := witt_vector.isocrystal_hom p k M M₂" in isocrystal
localized "notation (name := isocrystal_equiv)
  M ` ≃ᶠⁱ[`:50 p `, ` k `] ` M₂ := witt_vector.isocrystal_equiv p k M M₂" in isocrystal


end perfect_ring

open_locale isocrystal

/-! ### Classification of isocrystals in dimension 1 -/

/-- A helper instance for type class inference. -/
local attribute [instance]
def fraction_ring.module : module K(p, k) K(p, k) := semiring.to_module

/--
Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal structure
of slope `m : ℤ`.
-/
@[nolint unused_arguments has_nonempty_instance, derive [add_comm_group, module K(p, k)]]
def standard_one_dim_isocrystal (m : ℤ) : Type* :=
K(p, k)

section perfect_ring
variables [is_domain k] [char_p k p] [perfect_ring k p]

/-- The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal. -/
instance (m : ℤ) : isocrystal p k (standard_one_dim_isocrystal p k m) :=
{ frob := (fraction_ring.frobenius p k).to_semilinear_equiv.trans
   (linear_equiv.smul_of_ne_zero _ _ _ (zpow_ne_zero m (witt_vector.fraction_ring.p_nonzero p k))) }

@[simp] lemma standard_one_dim_isocrystal.frobenius_apply (m : ℤ)
  (x : standard_one_dim_isocrystal p k m) :
  Φ(p, k) x = (p:K(p, k)) ^ m • φ(p, k) x :=
rfl

end perfect_ring

/-- A one-dimensional isocrystal over an algebraically closed field
admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensional isocrystals. -/
theorem isocrystal_classification
  (k : Type*) [field k] [is_alg_closed k] [char_p k p]
  (V : Type*) [add_comm_group V] [isocrystal p k V]
  (h_dim : finrank K(p, k) V = 1) :
  ∃ (m : ℤ), nonempty (standard_one_dim_isocrystal p k m ≃ᶠⁱ[p, k] V) :=
begin
  haveI : nontrivial V := finite_dimensional.nontrivial_of_finrank_eq_succ h_dim,
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0,
  have : Φ(p, k) x ≠ 0 := by simpa only [map_zero] using Φ(p,k).injective.ne hx,
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p, k), a ≠ 0 ∧ Φ(p, k) x = a • x,
  { rw finrank_eq_one_iff_of_nonzero' x hx at h_dim,
    obtain ⟨a, ha⟩ := h_dim (Φ(p, k) x),
    refine ⟨a, _, ha.symm⟩,
    intros ha',
    apply this,
    simp only [←ha, ha', zero_smul] },
  obtain ⟨b, hb, m, hmb⟩ := witt_vector.exists_frobenius_solution_fraction_ring p ha,
  replace hmb : φ(p, k) b * a = p ^ m * b := by convert hmb,
  use m,
  let F₀ : standard_one_dim_isocrystal p k m →ₗ[K(p,k)] V :=
    linear_map.to_span_singleton K(p, k) V x,
  let F : standard_one_dim_isocrystal p k m ≃ₗ[K(p,k)] V,
  { refine linear_equiv.of_bijective F₀ ⟨_, _⟩,
    { rw ← linear_map.ker_eq_bot,
      exact linear_map.ker_to_span_singleton K(p, k) V hx },
    { rw ← linear_map.range_eq_top,
      rw ← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim,
      rw linear_map.span_singleton_eq_range } },
  refine ⟨⟨(linear_equiv.smul_of_ne_zero K(p, k) _ _ hb).trans F, _⟩⟩,
  intros c,
  rw [linear_equiv.trans_apply, linear_equiv.trans_apply,
      linear_equiv.smul_of_ne_zero_apply, linear_equiv.smul_of_ne_zero_apply,
      linear_equiv.map_smul, linear_equiv.map_smul],
  simp only [hax, linear_equiv.of_bijective_apply, linear_map.to_span_singleton_apply,
    linear_equiv.map_smulₛₗ, standard_one_dim_isocrystal.frobenius_apply, algebra.id.smul_eq_mul],
  simp only [←mul_smul],
  congr' 1,
  linear_combination φ(p,k) c * hmb,
end

end witt_vector
