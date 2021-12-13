/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Scheme
import ring_theory.nilpotent
import topology.sheaves.sheaf_condition.sites
import category_theory.limits.constructions.binary_products
import algebra.category.CommRing.constructions
import ring_theory.integral_domain

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `algebraic_geometry.is_integral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `algebraic_geometry.is_reduced`: A scheme is reduced if all the components of the structure sheaf
  is reduced.
-/

open topological_space opposite category_theory category_theory.limits Top

namespace algebraic_geometry

variable (X : Scheme)

/-- A scheme `X` is integral if its carrier is nonempty,
and `𝒪ₓ(U)` is an integral domain for each `U ≠ ∅`. -/
class is_integral : Prop :=
(nonempty : nonempty X.carrier . tactic.apply_instance)
(component_integral : ∀ (U : opens X.carrier) [_root_.nonempty U],
  is_domain (X.presheaf.obj (op U)) . tactic.apply_instance)

attribute [instance] is_integral.component_integral is_integral.nonempty

/-- A scheme `X` is reduced if all `𝒪ₓ(U)` are reduced. -/
class is_reduced : Prop :=
(component_reduced : ∀ U, _root_.is_reduced (X.presheaf.obj (op U)) . tactic.apply_instance)

attribute [instance] is_reduced.component_reduced

@[priority 900]
instance is_reduced_of_is_integral [is_integral X] : is_reduced X :=
begin
  constructor,
  intro U,
  cases U.1.eq_empty_or_nonempty,
  { have : U = ∅ := subtype.eq h,
    haveI := CommRing.subsingleton_of_is_terminal (X.sheaf.is_terminal_of_eq_empty this),
    change _root_.is_reduced (X.sheaf.val.obj (op U)),
    apply_instance },
  { haveI : nonempty U := by simpa, apply_instance }
end

instance is_irreducible_of_is_integral [is_integral X] : irreducible_space X.carrier :=
begin
  by_contradiction H,
  replace H : ¬ is_preirreducible (⊤ : set X.carrier) := λ h,
    H { to_preirreducible_space := ⟨h⟩, to_nonempty := infer_instance },
  simp_rw [is_preirreducible_iff_closed_union_closed, not_forall, not_or_distrib] at H,
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩,
  erw not_forall at h₂ h₃,
  simp_rw not_forall at h₂ h₃,
  haveI : nonempty (⟨Sᶜ, hS.1⟩ : opens X.carrier) := ⟨⟨_, h₂.some_spec.some_spec⟩⟩,
  haveI : nonempty (⟨Tᶜ, hT.1⟩ : opens X.carrier) := ⟨⟨_, h₃.some_spec.some_spec⟩⟩,
  haveI : nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : opens X.carrier) :=
    ⟨⟨_, or.inl h₂.some_spec.some_spec⟩⟩,
  let e : X.presheaf.obj _ ≅ CommRing.of _ := (X.sheaf.is_product_of_disjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ _)
    .cone_point_unique_up_to_iso (CommRing.prod_fan_is_limit _ _),
  apply_with false_of_nontrivial_of_product_domain { instances := ff },
  { exact e.symm.CommRing_iso_to_ring_equiv.is_domain _ },
  { apply X.to_LocallyRingedSpace.component_nontrivial },
  { apply X.to_LocallyRingedSpace.component_nontrivial },
  { ext x,
    split,
    { rintros ⟨hS,hT⟩,
      cases h₁ (show x ∈ ⊤, by trivial),
      exacts [hS h, hT h] },
    { intro x, exact x.rec _ } }
end

end algebraic_geometry
