/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebra.category.Ring.basic
import ring_theory.localization.away
import ring_theory.ideal.local_ring

/-!
# Ring-theoretic results in terms of categorical languages
-/

open category_theory

instance localization_unit_is_iso (R : CommRing) :
  is_iso (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
is_iso.of_iso (is_localization.at_one R (localization.away (1 : R))).to_ring_equiv.to_CommRing_iso

instance localization_unit_is_iso' (R : CommRing) :
  @is_iso CommRing _ R _ (CommRing.of_hom $ algebra_map R (localization.away (1 : R))) :=
by { cases R, exact localization_unit_is_iso _ }

lemma is_localization.epi {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
  [algebra R S] [is_localization M S] : epi (CommRing.of_hom $ algebra_map R S) :=
⟨λ T f₁ f₂, @is_localization.ring_hom_ext R _ M S _ _ T _ _ _ _⟩

instance localization.epi {R : Type*} [comm_ring R] (M : submonoid R) : epi
  (CommRing.of_hom $ algebra_map R $ localization M) :=
is_localization.epi M _

instance localization.epi' {R : CommRing} (M : submonoid R) : @epi CommRing _ R _
  (CommRing.of_hom $ algebra_map R $ localization M : _) :=
by { cases R, exact is_localization.epi M _ }

instance CommRing.is_local_ring_hom_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T)
  [is_local_ring_hom g] [is_local_ring_hom f] :
  is_local_ring_hom (f ≫ g) := is_local_ring_hom_comp _ _

lemma is_local_ring_hom_of_iso {R S : CommRing} (f : R ≅ S) : is_local_ring_hom f.hom :=
{ map_nonunit := λ a ha,
  begin
    convert f.inv.is_unit_map ha,
    rw category_theory.iso.hom_inv_id_apply,
  end }

@[priority 100] -- see Note [lower instance priority]
instance is_local_ring_hom_of_is_iso {R S : CommRing} (f : R ⟶ S) [is_iso f] :
  is_local_ring_hom f :=
is_local_ring_hom_of_iso (as_iso f)
