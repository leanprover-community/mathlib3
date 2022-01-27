/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import ring_theory.witt_vector.is_alg_closed

/-!
## F-isocrystals over a perfect field

https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf

-/

noncomputable theory
open finite_dimensional

-- move this
def baz {R : Type*} [semiring R] (σ : R →+* R) {τ : out_param (R →+* R)}
  [ring_hom_inv_pair σ τ] [ring_hom_inv_pair τ σ] :
  R ≃ₛₗ[σ] R :=
{ map_smul' := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _,
  .. ring_hom.to_add_monoid_hom σ }

-- do we have the linear equivalence "scalar-multiply by an invertible scalar" ?
def bop {R : Type*} [field R] {M : Type*} [add_comm_monoid M] [module R M] {c : R} (hc : c ≠ 0) :
  M ≃ₗ[R] M :=
{ to_fun := λ x, c • x,
  map_add' := _,
  map_smul' := _,
  inv_fun := λ x, c⁻¹ • x,
  left_inv := _,
  right_inv := _ }

variables (p : ℕ) [fact p.prime]
variables (k : Type*) [comm_ring k] [is_domain k] [char_p k p] [perfect_ring k p]

notation `K(` p`,` k`)` := fraction_ring (witt_vector p k)

/-! ### Frobenius-linear maps -/

/- The Frobenius automorphism of `k` induces an automorphism of `K`. -/
def foo₀ : K(p, k) ≃+* K(p, k) := is_fraction_ring.field_equiv_of_ring_equiv
  (ring_equiv.of_bijective _ (witt_vector.frobenius_bijective p k))

-- for notational purposes
def foo : K(p, k) →+* K(p, k) := foo₀ p k

notation `φ(` p`,` k`)` := foo₀ p k

instance inv_pair₁ : ring_hom_inv_pair (foo p k) _ :=
ring_hom_inv_pair.of_ring_equiv (foo₀ p k)

instance inv_pair₂ : ring_hom_inv_pair ((foo₀ p k).symm : K(p, k) →+* K(p, k)) _ :=
ring_hom_inv_pair.of_ring_equiv (foo₀ p k).symm

notation M ` →ᶠˡ[`:50 p `,` k `] ` M₂ := linear_map (foo p k) M M₂
notation M ` ≃ᶠˡ[`:50 p `,` k `] ` M₂ := linear_equiv (foo p k) M M₂

/-! ### Isocrystals -/

class isocrystal (V : Type*) [add_comm_group V] extends module K(p, k) V :=
( frob : V ≃ᶠˡ[p, k] V )

variables (V : Type*) [add_comm_group V] [isocrystal p k V]
variables (V₂ : Type*) [add_comm_group V₂] [isocrystal p k V₂]

variables {V}
-- for notational purposes
def isocrystal_frob' : V ≃ᶠˡ[p, k] V := @isocrystal.frob p _ k _ _ _ _ _ _ _
variables (V)

notation `Φ(` p`,` k`)` := isocrystal_frob' p k

structure isocrystal_hom extends V →ₗ[K(p, k)] V₂ :=
( frob_equivariant : ∀ x : V, Φ(p, k) (to_linear_map x) = to_linear_map (Φ(p, k) x) )

structure isocrystal_equiv extends V ≃ₗ[K(p, k)] V₂ :=
( frob_equivariant : ∀ x : V, Φ(p, k) (to_linear_equiv x) = to_linear_equiv (Φ(p, k) x) )

notation M ` →ᶠⁱ[`:50 p `,` k `] ` M₂ := isocrystal_hom p k M M₂
notation M ` ≃ᶠⁱ[`:50 p `,` k `] ` M₂ := isocrystal_equiv p k M M₂

/-! ### Classification of isocrystals in dimension 1 -/

-- this is too complicated for typeclass search to find unassisted
instance : module K(p, k) K(p, k) := semiring.to_module

/-- Type synonym for `K(p, k)` to carry the standard `m`-indexed 1-dimensional isocrystal structure.
-/
@[derive [add_comm_group, module K(p, k)]] def standard_one_dim_isocrystal (m : ℤ) : Type* :=
K(p, k)

instance (m : ℤ) : isocrystal p k (standard_one_dim_isocrystal p k m) :=
{ frob := (baz (foo p k)).trans (bop (sorry : (p : K(p, k)) ^ m ≠ 0)) }

@[simp] lemma frobenius_standard_one_dim_isocrystal_apply (m : ℤ)
  (x : standard_one_dim_isocrystal p k m) :
  Φ(p, k) x = (p:K(p, k)) ^ m • φ(p, k) x :=
rfl

/-- A one-dimensional isocrystal admits an isomorphism to one of the standard (indexed by `m : ℤ`)
one-dimensional isocrystals. -/
lemma classification
  (k : Type*) [field k] [is_alg_closed k] [char_p k p]
  (V : Type*) [add_comm_group V] [isocrystal p k V]
  (h_dim : finrank K(p, k) V = 1) :
  ∃ (m : ℤ), nonempty (standard_one_dim_isocrystal p k m ≃ᶠⁱ[p, k] V) :=
begin
  haveI : nontrivial V := sorry, -- one-dimensional is nontrivial
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0,
  have : Φ(p, k) x ≠ 0 := by simpa using Φ(p, k).injective.ne hx,
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p, k), a ≠ 0 ∧ Φ(p, k) x = a • x := sorry, -- single vector spans
  obtain ⟨b, hb, m, (hmb : φ(p, k) b * a = p ^ m * b)⟩ := important p k ha,
  use m,
  let F₀ : standard_one_dim_isocrystal p k m →ₗ[K(p,k)] V :=
    b • linear_map.to_span_singleton K(p, k) V x,
  let F : standard_one_dim_isocrystal p k m ≃ₗ[K(p,k)] V :=
    linear_equiv.of_bijective F₀ sorry sorry, -- by upgrading `F₀`
  refine ⟨⟨F, _⟩⟩,
  intros c,
  simp [F, F₀, foo, hax, ← mul_smul],
  congr' 1,
  transitivity (φ(p,k) b * a) * φ(p,k) c,
  { ring },
  { rw hmb,
    ring },
end
