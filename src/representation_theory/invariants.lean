/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import representation_theory.basic

/-!
# Subspace of invariants a group representation

This file introduce the subspace of invariants of a group representation
and proves basic result about it.
The main tool used is the average of all elements of the group, seen as an element of
`monoid_algebra k G`. Scalar multiplication by this special element gives a projection onto the
subspace of invariants.
In order for the definition of the average element to make sense, we need to assume for most of the
results that the order of `G` is invertible in `k` (e. g. `k` has characteristic `0`).
-/

open_locale big_operators
open monoid_algebra finset finite_dimensional linear_map representation

namespace representation

section average

variables (k G : Type*) [comm_semiring k] [group G]
variables [fintype G] [invertible (fintype.card G : k)]

/--
The average of all elements of the group `G`, considered as an element of `monoid_algebra k G`.
-/
noncomputable def average : monoid_algebra k G :=
  ⅟(fintype.card G : k) • ∑ g : G, of k G g

lemma average_def : average k G = ⅟(fintype.card G : k) • ∑ g : G, of k G g := rfl

/--
`average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) :
  (finsupp.single g 1 * average k G : monoid_algebra k G) = average k G :=
begin
  simp only [mul_one, finset.mul_sum, algebra.mul_smul_comm, average_def, monoid_algebra.of_apply,
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
  simp only [mul_one, finset.sum_mul, algebra.smul_mul_assoc, average_def, monoid_algebra.of_apply,
    finset.sum_congr, monoid_algebra.single_mul_single],
  set f : G → monoid_algebra k G := λ x, finsupp.single x 1,
  show ⅟ ↑(fintype.card G) • ∑ (x : G), f (x * g) = ⅟ ↑(fintype.card G) • ∑ (x : G), f x,
  rw function.bijective.sum_comp (group.mul_right_bijective g) _,
end

end average

section invariants

variables (k G V : Type*) [comm_semiring k] [group G] [add_comm_group V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
The subspace of invariants, consisting of the vectors fixed by all elements of `G`.
-/
def invariants : submodule k V :=
{ carrier := set_of (λ v, ∀ (g : G), g • v = v),
  zero_mem' := by simp only [forall_const, set.mem_set_of_eq, smul_zero],
  add_mem' := λ v w hv hw g, by simp only [smul_add, add_left_inj, eq_self_iff_true, hv g, hw g],
  smul_mem' := λ r v hv g, by simp only [eq_self_iff_true, smul_comm, hv g]}

@[simp]
lemma mem_invariants (v : V) : v ∈ (invariants k G V) ↔ ∀ (g: G), g • v = v := by refl

lemma invariants_eq_inter :
  (invariants k G V).carrier = ⋂ g : G, function.fixed_points (has_scalar.smul g) :=
by { ext, simp [function.is_fixed_pt] }

/--
The subspace of invariants, as a submodule over `monoid_algebra k G`.
-/
noncomputable def invariants' : submodule (monoid_algebra k G) V :=
  submodule_of_smul_mem (invariants k G V) (λ g v hv, by {rw [of_smul, hv g], exact hv})

@[simp] lemma invariants'_carrier :
  (invariants' k G V).carrier = (invariants k G V).carrier := rfl

variables [fintype G] [invertible (fintype.card G : k)]

/--
Scalar multiplication by `average k G` sends elements of `V` to the subspace of invariants.
-/
theorem smul_average_invariant (v : V) : (average k G) • v ∈ invariants k G V :=
λ g, by rw [←of_smul k, smul_smul, of_apply, mul_average_left]

/--
`average k G` acts as the identity on the subspace of invariants.
-/
theorem smul_average_id (v : V) (H : v ∈ invariants k G V) : (average k G) • v = v :=
begin
  rw [representation.mem_invariants] at H,
  simp_rw [average_def, smul_assoc, finset.sum_smul, representation.of_smul, H, finset.sum_const,
    finset.card_univ, nsmul_eq_smul_cast k _ v, smul_smul, inv_of_mul_self, one_smul],
end

/--
Scalar multiplication by `average k G` gives a projection map onto the subspace of invariants.
-/
noncomputable def average_map : V →ₗ[k] V := (as_algebra_hom k G V) (average k G)

end invariants

end representation
