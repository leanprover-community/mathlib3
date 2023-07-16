/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import representation_theory.basic
import representation_theory.fdRep

/-!
# Subspace of invariants a group representation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces the subspace of invariants of a group representation
and proves basic results about it.
The main tool used is the average of all elements of the group, seen as an element of
`monoid_algebra k G`. The action of this special element gives a projection onto the
subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

open_locale big_operators
open monoid_algebra
open representation

namespace group_algebra

variables (k G : Type*) [comm_semiring k] [group G]
variables [fintype G] [invertible (fintype.card G : k)]

/--
The average of all elements of the group `G`, considered as an element of `monoid_algebra k G`.
-/
noncomputable def average : monoid_algebra k G :=
  ⅟(fintype.card G : k) • ∑ g : G, of k G g

/--
`average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) :
  (finsupp.single g 1 * average k G : monoid_algebra k G) = average k G :=
begin
  simp only [mul_one, finset.mul_sum, algebra.mul_smul_comm, average, monoid_algebra.of_apply,
    finset.sum_congr, monoid_algebra.single_mul_single],
  set f : G → monoid_algebra k G := λ x, finsupp.single x 1,
  show ⅟ ↑(fintype.card G) • ∑ (x : G), f (g * x) = ⅟ ↑(fintype.card G) • ∑ (x : G), f x,
  rw function.bijective.sum_comp (group.mul_left_bijective g) _,
end

/--
`average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) :
  average k G * finsupp.single g 1 = average k G :=
begin
  simp only [mul_one, finset.sum_mul, algebra.smul_mul_assoc, average, monoid_algebra.of_apply,
    finset.sum_congr, monoid_algebra.single_mul_single],
  set f : G → monoid_algebra k G := λ x, finsupp.single x 1,
  show ⅟ ↑(fintype.card G) • ∑ (x : G), f (x * g) = ⅟ ↑(fintype.card G) • ∑ (x : G), f x,
  rw function.bijective.sum_comp (group.mul_right_bijective g) _,
end

end group_algebra

namespace representation

section invariants

open group_algebra

variables {k G V : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/--
The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : submodule k V :=
{ carrier := set_of (λ v, ∀ (g : G), ρ g v = v),
  zero_mem' := λ g, by simp only [map_zero],
  add_mem' := λ v w hv hw g, by simp only [hv g, hw g, map_add],
  smul_mem' := λ r v hv g, by simp only [hv g, linear_map.map_smulₛₗ, ring_hom.id_apply]}

@[simp]
lemma mem_invariants (v : V) : v ∈ invariants ρ ↔ ∀ (g: G), ρ g v = v := by refl

lemma invariants_eq_inter :
  (invariants ρ).carrier = ⋂ g : G, function.fixed_points (ρ g) :=
by {ext, simp [function.is_fixed_pt]}

variables [fintype G] [invertible (fintype.card G : k)]

/--
The action of `average k G` gives a projection map onto the subspace of invariants.
-/
@[simp]
noncomputable def average_map : V →ₗ[k] V := as_algebra_hom ρ (average k G)

/--
The `average_map` sends elements of `V` to the subspace of invariants.
-/
theorem average_map_invariant (v : V) : average_map ρ v ∈ invariants ρ :=
λ g, by rw [average_map, ←as_algebra_hom_single_one, ←linear_map.mul_apply,
  ←map_mul (as_algebra_hom ρ), mul_average_left]

/--
The `average_map` acts as the identity on the subspace of invariants.
-/
theorem average_map_id (v : V) (hv : v ∈ invariants ρ) : average_map ρ v = v :=
begin
  rw mem_invariants at hv,
  simp [average, map_sum, hv, finset.card_univ, nsmul_eq_smul_cast k _ v, smul_smul],
end

theorem is_proj_average_map : linear_map.is_proj ρ.invariants ρ.average_map :=
⟨ρ.average_map_invariant, ρ.average_map_id⟩

end invariants

namespace lin_hom

universes u

open category_theory Action

section Rep

variables {k : Type u} [comm_ring k] {G : Group.{u}}

lemma mem_invariants_iff_comm {X Y : Rep k G} (f : X.V →ₗ[k] Y.V) (g : G) :
  (lin_hom X.ρ Y.ρ) g f = f ↔ f.comp (X.ρ g) = (Y.ρ g).comp f :=
begin
  dsimp,
  erw [←ρ_Aut_apply_inv],
  rw [←linear_map.comp_assoc, ←Module.comp_def, ←Module.comp_def, iso.inv_comp_eq, ρ_Aut_apply_hom],
  exact comm,
end

/-- The invariants of the representation `lin_hom X.ρ Y.ρ` correspond to the the representation
homomorphisms from `X` to `Y` -/
@[simps]
def invariants_equiv_Rep_hom (X Y : Rep k G) : (lin_hom X.ρ Y.ρ).invariants ≃ₗ[k] (X ⟶ Y) :=
{ to_fun := λ f, ⟨f.val, λ g, (mem_invariants_iff_comm _ g).1 (f.property g)⟩,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  inv_fun := λ f, ⟨f.hom, λ g, (mem_invariants_iff_comm _ g).2 (f.comm g)⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl } }

end Rep

section fdRep

variables {k : Type u} [field k] {G : Group.{u}}

/-- The invariants of the representation `lin_hom X.ρ Y.ρ` correspond to the the representation
homomorphisms from `X` to `Y` -/
def invariants_equiv_fdRep_hom (X Y : fdRep k G) : (lin_hom X.ρ Y.ρ).invariants ≃ₗ[k] (X ⟶ Y) :=
begin
  rw [←fdRep.forget₂_ρ, ←fdRep.forget₂_ρ],
  exact (lin_hom.invariants_equiv_Rep_hom _ _) ≪≫ₗ (fdRep.forget₂_hom_linear_equiv X Y),
end

end fdRep

end lin_hom

end representation
