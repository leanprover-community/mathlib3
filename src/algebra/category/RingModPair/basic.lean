/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Ring.basic
import algebra.category.Module.change_of_rings

/-!
# The category of ring-module pair

`RingModPair` is the category of pairs of the shape `(R, M)` where `R` is
a ring and `M` is an `R`-module. A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map).
-/

namespace category_theory

open category_theory.Module

section RingModPair

universes u v

/--
A ring-module pair is a pair `(R, M)` such that `R : Ring` and `M` is an `R`-module.
-/
@[nolint has_inhabited_instance]
structure RingModPair :=
(ring : Ring.{u})
(mod : Module.{v} ring)

namespace RingModPair

/--
A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map)
-/
def hom (P Q : RingModPair) :=
Σ (ring_hom : P.ring ⟶ Q.ring),
  P.mod ⟶ (category_theory.Module.restrict_scalars ring_hom).obj Q.mod

instance : category RingModPair :=
{ hom := hom,
  id := λ P, sigma.mk (𝟙 _)
  { to_fun := λ x, x,
    map_add' := λ _ _, rfl,
    map_smul' := λ _ _, rfl },
  comp := λ X Y Z f g, sigma.mk (f.1 ≫ g.1)
  { to_fun := λ x, g.2 $ f.2 x,
    map_add' := λ x y, by simp only [map_add],
    map_smul' := λ r x,
      by simp only [map_smul, ring_hom.id_apply, restrict_scalars.smul_def, comp_apply] },
  id_comp' := λ X Y ⟨f, g⟩, sigma.ext (category.id_comp _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  comp_id' := λ X Y ⟨f, g⟩, sigma.ext (category.comp_id _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  assoc' := λ A B C D ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, sigma.ext (category.assoc _ _ _) $ heq_of_eq $
    linear_map.ext $ λ x, rfl }

/--
The underlying ring homomorphism of a morphism between two ring-module pairs.
-/
def hom.ring_hom {P Q : RingModPair} (f : P ⟶ Q) : P.ring ⟶ Q.ring := f.1
/--
The underlying module homomorphism of a morphism between two ring-module pairs.
-/
def hom.mod_hom {P Q : RingModPair} (f : P ⟶ Q) :
  P.mod ⟶ (category_theory.Module.restrict_scalars f.ring_hom).obj Q.mod := f.2

/--
The canonical functor sending a ring-module pair to its underlying ring
-/
def forget_to_Ring : RingModPair ⥤ Ring :=
{ obj := λ P, P.ring,
  map := λ _ _ f, f.ring_hom,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

/--
The canonical functor sending a ring-module pair to its underlying abelian group
-/
def forget_to_Ab : RingModPair ⥤ Ab :=
{ obj := λ P, ⟨P.mod⟩,
  map := λ _ _ f, f.mod_hom.to_add_monoid_hom,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

end RingModPair

end RingModPair

end category_theory
