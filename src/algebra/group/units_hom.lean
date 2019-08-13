/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard

Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/
import algebra.group.units algebra.group.hom

variables {α : Type*} {β : Type*} {γ : Type*} [monoid α] [monoid β] [monoid γ]

namespace units

variables (f : α → β) (g : β → γ) [is_monoid_hom f] [is_monoid_hom g]

definition map : units α → units β :=
λ u, ⟨f u.val, f u.inv,
      by rw [← is_monoid_hom.map_mul f, u.val_inv, is_monoid_hom.map_one f],
      by rw [← is_monoid_hom.map_mul f, u.inv_val, is_monoid_hom.map_one f] ⟩

instance : is_group_hom (units.map f) :=
{ map_mul := λ a b, by ext; exact is_monoid_hom.map_mul f a b }

instance coe_is_monoid_hom : is_monoid_hom (coe : units α → α) :=
{ map_one := rfl, map_mul := by simp }

@[simp] lemma coe_map (u : units α) : (map f u : β) = f u := rfl

@[simp] lemma map_id : map (id : α → α) = id := by ext; refl

lemma map_comp : map (g ∘ f) = map g ∘ map f := rfl

end units

namespace monoid_hom

variables (f : α →* β) (g : β →* γ)

definition units_map : units α →* units β :=
mk' (λ u, ⟨f u.val, f u.inv,
      by rw [← f.map_mul, u.val_inv, f.map_one],
      by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
(λ x y, by ext; exact f.map_mul x y)

@[simp] lemma coe_units_map (u : units α) : (f.units_map u : β) = f u := rfl

@[simp] lemma units_map_id : (monoid_hom.id α).units_map = monoid_hom.id (units α) := by ext; refl

lemma units_map_comp : (g.comp f).units_map = g.units_map.comp f.units_map := rfl

end monoid_hom
