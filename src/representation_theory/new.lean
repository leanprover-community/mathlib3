/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.character
import representation_theory.schur

open_locale big_operators

universes u

/-- The trivial representation maps all group elements to the identity endomorphism. -/
@[simp] def trivial_representation (k G V : Type*)
  [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V] :
  representation k G V := 1

section Rep

variables
  {k G V : Type u} [ring k] [monoid G] [add_comm_group V] [module k V]
  {ρ : G →* V →ₗ[k] V} {g : G}

@[simp] lemma Rep.of_apply : (Rep.of ρ).ρ g = ρ g := rfl

@[simp] lemma Rep.of_coe_sort : ↥(Rep.of ρ) = V := rfl

end Rep

section fdRep

variables
  {k G V : Type u} [field k] [monoid G] [add_comm_group V] [module k V]
  [finite_dimensional k V] {ρ : G →* V →ₗ[k] V} {g : G}

@[simp] lemma fdRep.of_apply : (fdRep.of ρ).ρ g = ρ g := rfl

@[simp] lemma fdRep.of_coe_sort : ↥(fdRep.of ρ) = V := rfl

@[simp] lemma fdRep.character_apply {V : fdRep k G} {g : G} :
  V.character g = (linear_map.trace k V) (V.ρ g) := rfl

/-- The character of the trivial representation is the dimension of the vector space V. -/
lemma char_of_trivial (g : G) :
  (fdRep.of $ trivial_representation k G V).character g = finite_dimensional.finrank k V :=
by {simp, congr}

end fdRep

/-- The mean of the representation over all group elements of a finite group. -/
def rep_hom.average' {k G V : Type u} [field k] [monoid G] [fintype G]
  [add_comm_group V] [module k V] [distrib_mul_action ℚ V] [smul_comm_class k ℚ V]
  (ρ : representation k G V) : V →ₗ[k] V :=
((fintype.card G) : ℚ)⁻¹ • finset.univ.sum (λ g' : G, (ρ g' : V →ₗ[k] V))

@[simp] lemma rep_hom.average_apply {k G V : Type u} [field k] [monoid G] [fintype G]
  [add_comm_group V] [module k V] [distrib_mul_action ℚ V] [smul_comm_class k ℚ V]
  (ρ : representation k G V) {x : V} : rep_hom.average' ρ x =
  ((fintype.card G) : ℚ)⁻¹ • finset.univ.sum (λ g' : G, (ρ g' : V →ₗ[k] V)) x := rfl

set_option trace.simplify.rewrite true
lemma rep_hom.average_apply' {k G V : Type u} [field k] [monoid G] [fintype G]
  [add_comm_group V] [module k V] [distrib_mul_action ℚ V] [smul_comm_class k ℚ V]
  (ρ : representation k G V) {x : V} : rep_hom.average' ρ x =
  ((fintype.card G) : ℚ)⁻¹ • finset.univ.sum (λ g' : G, ρ g' x) :=
by rw [rep_hom.average_apply, linear_map.coe_fn_sum, fintype.sum_apply]

/-- The mean of the representation over all group elements of a finite group commutes with the
group action. -/
lemma rep_hom.average_smulG {k G V : Type u} [field k] [group G] [fintype G]
  [add_comm_group V] [module k V] [distrib_mul_action ℚ V] [smul_comm_class k ℚ V]
  [linear_map.compatible_smul V V ℚ k] (ρ : representation k G V) (g : G) (x : V) :
  (rep_hom.average' ρ) (ρ g x) = ρ g ((rep_hom.average' ρ) x) :=
begin
  rw [rep_hom.average_apply, rep_hom.average_apply',
    linear_map.map_smul_of_tower (ρ g) (↑(fintype.card G))⁻¹],
  show has_smul ℚ V, apply_instance,
  show linear_map.compatible_smul V V ℚ k, apply_instance, -- pull 1/|G| out
  apply congr_arg,
  rw [linear_map.coe_fn_sum, fintype.sum_apply, linear_map.map_sum], -- push ρ g inside the sum
  rw ←equiv.perm.sum_comp (equiv.mul_right g⁻¹), -- conjugate c : G to g * c * g⁻¹
  show {a : G | (equiv.mul_right g⁻¹) a ≠ a} ⊆ ↑finset.univ,
  { rw finset.coe_univ,
    apply set.subset_univ },
  rw ←equiv.perm.sum_comp (equiv.mul_left g),
  show {a : G | (equiv.mul_left g) a ≠ a} ⊆ ↑finset.univ,
  { rw finset.coe_univ,
    apply set.subset_univ },
  congr,
  ext, -- equate summand
  rw [equiv.coe_mul_right, equiv.coe_mul_left, map_mul, ←linear_map.mul_apply,
      ←linear_map.mul_apply, ←map_mul, ←map_mul, ←map_mul, inv_mul_cancel_right], -- simplify
end

/-- `rep_hom.average'` as a representation endomorphism -/
def rep_hom.average {k G V : Type u} [field k] [group G] [fintype G]
  [add_comm_group V] [module k V] [distrib_mul_action ℚ V] [smul_comm_class k ℚ V]
  [linear_map.compatible_smul V V ℚ k] (ρ : representation k G V) : ρ →ᵣ ρ :=
{ map_smulG' := rep_hom.average_smulG ρ,
  ..rep_hom.average' ρ }

-- TODO: trace of rep_hom.average on the lin_hom representation is the dimension of ρ →ᵣ ρ₂
