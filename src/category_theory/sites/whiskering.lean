/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.sites.sheaf

/-!

TODO

-/

namespace category_theory

open category_theory.limits

universes v₁ v₂ u₁ u₂ u₃

variables {C : Type u₁} [category.{v₁} C]
variables {A : Type u₂} [category.{max v₁ u₁} A]
variables {B : Type u₃} [category.{max v₁ u₁} B]
variables {J : grothendieck_topology C}
variables {U : C} (R : presieve U)
variables (F : A ⥤ B)
variables [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ A), preserves_limit (S.index P).multicospan F]

def grothendieck_topology.cover.multicospan_comp {P : Cᵒᵖ ⥤ A} {X : C} (S : J.cover X) :
  (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
nat_iso.of_components (λ t,
match t with
| walking_multicospan.left a := eq_to_iso rfl
| walking_multicospan.right b := eq_to_iso rfl
end) begin
  sorry
end

def grothendieck_topology.cover.map_multifork (P : Cᵒᵖ ⥤ A) {X : C} (S : J.cover X) :
  F.map_cone (S.multifork P) ≅ (limits.cones.postcompose
    (S.multicospan_comp F).hom).obj (S.multifork (P ⋙ F)) := sorry

lemma presheaf.is_sheaf.comp {P : Cᵒᵖ ⥤ A} (hP : presheaf.is_sheaf J P) :
  presheaf.is_sheaf J (P ⋙ F) :=
begin
  rw presheaf.is_sheaf_iff_multifork at ⊢ hP,
  intros X S,
  obtain ⟨h⟩ := hP X S,
  replace h := is_limit_of_preserves F h,
  replace h := limits.is_limit.of_iso_limit h (S.map_multifork F P),
  exact ⟨limits.is_limit.postcompose_hom_equiv (S.multicospan_comp F) _ h⟩,
end

end category_theory
