/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.ideal.local_ring
import algebra.category.Ring.basic

/-!
# Local rings in category theory settings

In this file we reformulate a few facts about local ring using the category theory language.
-/
open category_theory

universe u
variables {R S T : CommRing.{u}}

instance CommRing.is_local_ring_hom_comp (f : R ⟶ S) (g : S ⟶ T)
  [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (f ≫ g) := is_local_ring_hom_comp _ _

lemma is_local_ring_hom_of_iso (f : R ≅ S) : is_local_ring_hom f.hom :=
{ map_nonunit := λ a ha,
  begin
    convert f.inv.is_unit_map ha,
    rw category_theory.iso.hom_inv_id_apply,
  end }

@[priority 100] -- see Note [lower instance priority]
instance is_local_ring_hom_of_is_iso (f : R ⟶ S) [is_iso f] : is_local_ring_hom f :=
is_local_ring_hom_of_iso (as_iso f)
