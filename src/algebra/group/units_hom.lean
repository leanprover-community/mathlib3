/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard

Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/
import algebra.group.units algebra.group.hom

universes u v w

namespace units
variables {M : Type u} {N : Type v} {P : Type w} [monoid M] [monoid N] [monoid P]

/-- The group homomorphism on units induced by a `monoid_hom`. -/
def map (f : M →* N) : units M →* units N :=
monoid_hom.mk'
  (λ u, ⟨f u.val, f u.inv,
                  by rw [← f.map_mul, u.val_inv, f.map_one],
                  by rw [← f.map_mul, u.inv_val, f.map_one]⟩)
  (λ x y, ext (f.map_mul x y))

/-- The group homomorphism on units induced by a multiplicative morphism. -/
@[reducible] def map' (f : M → N) [is_monoid_hom f] : units M →* units N :=
  map (monoid_hom.of f)

@[simp] lemma coe_map (f : M →* N) (x : units M) : ↑(map f x) = f x := rfl

@[simp] lemma coe_map' (f : M → N) [is_monoid_hom f] (x : units M) :
  ↑((map' f : units M → units N) x) = f x :=
rfl

@[simp] lemma map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl

variables (M)
@[simp] lemma map_id : map (monoid_hom.id M) = monoid_hom.id (units M) :=
by ext; refl

/-- Coercion `units M → M` as a monoid homomorphism. -/
def coe_hom : units M →* M := ⟨coe, coe_one, coe_mul⟩

variable {M}

@[simp] lemma coe_hom_apply (x : units M) : coe_hom M x = ↑x := rfl

instance coe_is_monoid_hom : is_monoid_hom (coe : units M → M) := (coe_hom M).is_monoid_hom

end units
