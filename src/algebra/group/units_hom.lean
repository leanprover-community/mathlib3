/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard

Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/
import algebra.group.units algebra.group.hom

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w} [monoid α] [monoid β] [monoid γ]

namespace units

@[to_additive] def map (f : α →* β) : units α →* units β :=
monoid_hom.mk'
  (λ u, ⟨f u.val, f u.inv,
                  by rw [← f.map_mul, u.val_inv, f.map_one],
                  by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
  (λ x y, ext (f.map_mul x y))

/-- The group homomorphism on units induced by a multiplicative morphism. -/
@[reducible] def map' (f : α → β) [is_monoid_hom f] : units α →* units β :=
  map (monoid_hom.of f)

@[simp, to_additive] lemma coe_map (f : α →* β) (x : units α) : ↑(map f x) = f x := rfl

@[simp, to_additive]
lemma map_comp (f : α →* β) (g : β →* γ) : map (g.comp f) = (map g).comp (map f) := rfl

variables (α)
@[simp, to_additive] lemma map_id : map (monoid_hom.id α) = monoid_hom.id (units α) :=
by ext; refl

/-- Coercion `units α → α` as a monoid homomorphism. -/
@[to_additive] def coe_hom : units α →* α := ⟨coe, coe_one, coe_mul⟩

@[simp, to_additive] lemma coe_hom_apply (x : units α) : coe_hom α x = ↑x := rfl

@[to_additive]
instance coe_is_monoid_hom : is_monoid_hom (coe : units α → α) := (coe_hom α).is_monoid_hom

end units
