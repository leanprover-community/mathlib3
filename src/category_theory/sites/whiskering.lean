/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import category_theory.sites.sheaf

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


In this file we construct the functor `Sheaf J A ⥤ Sheaf J B` between sheaf categories
obtained by composition with a functor `F : A ⥤ B`.

In order for the sheaf condition to be preserved, `F` must preserve the correct limits.
The lemma `presheaf.is_sheaf.comp` says that composition with such an `F` indeed preserves the
sheaf condition.

The functor between sheaf categories is called `Sheaf_compose J F`.
Given a natural transformation `η : F ⟶ G`, we obtain a natural transformation
`Sheaf_compose J F ⟶ Sheaf_compose J G`, which we call `Sheaf_compose_map J η`.

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

namespace grothendieck_topology.cover

variables (P : Cᵒᵖ ⥤ A) {X : C} (S : J.cover X)

/-- The multicospan associated to a cover `S : J.cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospan_comp : (S.index (P ⋙ F)).multicospan ≅ (S.index P).multicospan ⋙ F :=
nat_iso.of_components (λ t,
match t with
| walking_multicospan.left a := eq_to_iso rfl
| walking_multicospan.right b := eq_to_iso rfl
end) begin
  rintros (a|b) (a|b) (f|f|f),
  any_goals { dsimp, erw [functor.map_id, functor.map_id, category.id_comp] },
  any_goals { dsimp, erw [category.comp_id, category.id_comp], refl }
end

@[simp] lemma multicospan_comp_app_left (a) :
  (S.multicospan_comp F P).app (walking_multicospan.left a) = eq_to_iso rfl := rfl

@[simp] lemma multicospan_comp_app_right (b) :
  (S.multicospan_comp F P).app (walking_multicospan.right b) = eq_to_iso rfl := rfl

@[simp] lemma multicospan_comp_hom_app_left (a) :
  (S.multicospan_comp F P).hom.app (walking_multicospan.left a) = eq_to_hom rfl := rfl

@[simp] lemma multicospan_comp_hom_app_right (b) :
  (S.multicospan_comp F P).hom.app (walking_multicospan.right b) = eq_to_hom rfl := rfl

@[simp] lemma multicospan_comp_hom_inv_left (P : Cᵒᵖ ⥤ A) {X : C}
  (S : J.cover X) (a) : (S.multicospan_comp F P).inv.app (walking_multicospan.left a) =
  eq_to_hom rfl := rfl

@[simp] lemma multicospan_comp_hom_inv_right (P : Cᵒᵖ ⥤ A) {X : C}
  (S : J.cover X) (b) : (S.multicospan_comp F P).inv.app (walking_multicospan.right b) =
  eq_to_hom rfl := rfl

/-- Mapping the multifork associated to a cover `S : J.cover X` and a presheaf `P` with
respect to a functor `F` is isomorphic (upto a natural isomorphism of the underlying functors)
to the multifork associated to `S` and `P ⋙ F`. -/
def map_multifork : F.map_cone (S.multifork P) ≅ (limits.cones.postcompose
    (S.multicospan_comp F P).hom).obj (S.multifork (P ⋙ F)) :=
cones.ext (eq_to_iso rfl) begin
  rintros (a|b),
  { dsimp, simpa },
  { dsimp, simp, dsimp [multifork.of_ι], simpa }
end

end grothendieck_topology.cover

variables [∀ (X : C) (S : J.cover X) (P : Cᵒᵖ ⥤ A), preserves_limit (S.index P).multicospan F]

lemma presheaf.is_sheaf.comp {P : Cᵒᵖ ⥤ A} (hP : presheaf.is_sheaf J P) :
  presheaf.is_sheaf J (P ⋙ F) :=
begin
  rw presheaf.is_sheaf_iff_multifork at ⊢ hP,
  intros X S,
  obtain ⟨h⟩ := hP X S,
  replace h := is_limit_of_preserves F h,
  replace h := limits.is_limit.of_iso_limit h (S.map_multifork F P),
  exact ⟨limits.is_limit.postcompose_hom_equiv (S.multicospan_comp F P) _ h⟩,
end

variable (J)

/-- Composing a sheaf with a functor preserving the appropriate limits yields a functor
between sheaf categories. -/
@[simps]
def Sheaf_compose : Sheaf J A ⥤ Sheaf J B :=
{ obj := λ G, ⟨G.val ⋙ F, presheaf.is_sheaf.comp _ G.2⟩,
  map := λ G H η, ⟨whisker_right η.val _⟩,
  map_id' := λ G, Sheaf.hom.ext _ _ $ whisker_right_id _,
  map_comp' := λ G H W f g, Sheaf.hom.ext _ _ $ whisker_right_comp _ _ _ }

end category_theory
