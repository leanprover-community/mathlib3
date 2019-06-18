/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard

Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/
import algebra.group.units algebra.group.hom

namespace units
variables {α : Type*} {β : Type*}

variables {γ : Type*} [monoid α] [monoid β] [monoid γ] (f : α → β) (g : β → γ)
[is_monoid_hom f] [is_monoid_hom g]

definition map : units α → units β :=
λ u, ⟨f u.val, f u.inv,
      by rw [← is_monoid_hom.map_mul f, u.val_inv, is_monoid_hom.map_one f],
      by rw [← is_monoid_hom.map_mul f, u.inv_val, is_monoid_hom.map_one f] ⟩

instance : is_group_hom (units.map f) :=
⟨λ a b, by ext; exact is_monoid_hom.map_mul f ⟩

instance : is_monoid_hom (coe : units α → α) :=
{ map_one := rfl, map_mul := by simp }

@[simp] lemma coe_map (u : units α) : (map f u : β) = f u := rfl

@[simp] lemma map_id : map (id : α → α) = id := by ext; refl

lemma map_comp : map (g ∘ f) = map g ∘ map f := rfl

lemma map_comp' : map (λ x, g (f x)) = λ x, map g (map f x) := rfl

end units
