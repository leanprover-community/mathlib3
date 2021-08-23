/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import data.setoid.partition
import analysis.normed_space.inner_product

/-!
# The square lattice in a Euclidean affine plane modelled on `ℂ`

In this file the "square" action of `ℤ × ℤ` on an affine plane `P` modelled on `ℂ` is defined; that
is, `(m, n)` acts on `x : P` by the affine-addition of the complex number `m + n * I`.

A `square_lattice P` is then defined to be an orbit of this action; that is, a standard grid of
points in the plane, with the four closest points to a point `x` all equidistant from `x` and at
right angles to each other.

## TODO

Add the hexagonal lattice, defined along the same lines.

-/

open add_action

/-- The "square" additive group homomorphism from `ℤ × ℤ` to `ℂ`, given by,
`(m, n) ↦ (m + n * I)`. -/
noncomputable def square_add_hom : ℤ × ℤ →+ ℂ :=
add_monoid_hom.coprod (gmultiples_hom ℂ (1:ℂ)) (gmultiples_hom ℂ complex.I)

lemma square_add_hom_apply (v : ℤ × ℤ) :
  square_add_hom v = (v.1:ℂ) + v.2 * complex.I :=
show gsmul v.1 (1:ℂ) + gsmul v.2 complex.I = _, by simp

@[simp] lemma square_add_hom_eq_zero_iff (v : ℤ × ℤ) : square_add_hom v = 0 ↔ v = 0 :=
begin
  refine ⟨λ h, _, λ h, by simp [h]⟩,
  simpa [prod.ext_iff, complex.ext_iff, square_add_hom_apply] using h,
end

variables {P : Type*} [metric_space P] [normed_add_torsor ℂ P]

/-- The "square" action of `ℤ × ℤ` on a Euclidean affine plane `P`; that is, `(m, n)` acts on
`x : P` by the affine-addition of the complex number `m + n * I`. -/
noncomputable instance square_action : add_action (ℤ × ℤ) P :=
add_action.comp_hom P square_add_hom

@[simp] lemma square_action_apply (v : ℤ × ℤ) (x : P) :
  v +ᵥ x = ((v.1:ℂ) + v.2 * complex.I) +ᵥ x :=
show (square_add_hom v) +ᵥ x = _, by simp [square_add_hom_apply]

/-- The "square" action of `ℤ × ℤ` on `P` is a free action. -/
lemma square_action_stabilizer (x : P) : stabilizer (ℤ × ℤ) x = ⊥ :=
begin
  rw eq_bot_iff,
  intros v,
  rw mem_stabilizer_iff,
  intros h,
  suffices : square_add_hom v +ᵥ x = (0:ℂ) +ᵥ x,
  { rw vadd_right_cancel_iff at this,
    simpa using this, },
  rwa zero_vadd
end

variables (P)
/-- In a Euclidean affine plane `P` modelled on `ℂ`, a `square_lattice P` is an orbit of the
"square" action of `ℤ × ℤ` on `P`, given by `(m, n) +ᵥ x := (m + n * I) +ᵥ x`. -/
def square_lattice := subtype (orbit_rel (ℤ × ℤ) P).classes

namespace square_lattice
variables {P}

/-- The set of points in a `square_lattice` of a Euclidean affine plane `P` modelled on `ℂ`. -/
def points (Λ : square_lattice P) : set P := (@coe_b _ _ coe_subtype) Λ

/-- Construct a `square_lattice` of a Euclidean affine plane `P` modelled on `ℂ`, as the orbit of
a particular point `x : P` under the natural "square" `ℤ × ℤ`-action. -/
def mk (x : P) : square_lattice P := ⟨orbit (ℤ × ℤ) x, x, rfl⟩

@[simp] lemma points_mk (x : P) : (square_lattice.mk x).points = orbit (ℤ × ℤ) x := rfl

/-- A `square_lattice` in a Euclidean affine plane modelled on `ℂ` is nonempty. -/
lemma points_nonempty (Λ : square_lattice P) : Λ.points.nonempty :=
(orbit_rel (ℤ × ℤ) P).mem_nonempty (subtype.property Λ)

/-- A `square_lattice` in a Euclidean affine plane modelled on `ℂ` is equal to the orbit, under the
"square" `ℤ × ℤ`- action, of any one of its points. -/
lemma points_eq_orbit (Λ : square_lattice P) {x : P} (hx : x ∈ Λ.points) :
  Λ.points = orbit (ℤ × ℤ) x :=
(orbit_rel (ℤ × ℤ) P).eq_set_rel_of_mem (subtype.property Λ) hx

/-- A `square_lattice` in a Euclidean affine plane modelled on `ℂ` is closed under the "square"
`ℤ × ℤ`- action. -/
lemma add_mem (Λ : square_lattice P) {x : P} (hx : x ∈ Λ.points) (v : ℤ × ℤ) :
  v +ᵥ x ∈ Λ.points :=
by { rw Λ.points_eq_orbit hx, exact mem_orbit x v }

/-- Any two points in a `square_lattice` in a Euclidean affine plane modelled on `ℂ` are related by
the "square" `ℤ × ℤ`- action. -/
lemma exists_eq_add (Λ : square_lattice P) {x y : P} (hx : x ∈ Λ.points) (hy : y ∈ Λ.points) :
  ∃ v : ℤ × ℤ, y = v +ᵥ x :=
by simpa [Λ.points_eq_orbit hx, mem_orbit_iff, eq_comm] using hy

end square_lattice
