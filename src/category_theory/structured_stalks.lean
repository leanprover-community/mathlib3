import category_theory.stalks

universes v₁ v₂ u₁ u₂

open category_theory.limits

namespace category_theory

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
variables (V : Type u₂) [𝒱 : category.{v₂+1} V]
include 𝒞 𝒱
variables [has_colimits.{v₁} C]

structure StructuredStalkPresheafedSpace (F : V ⥤ C) extends PresheafedSpace.{v₁} C :=
(structured_stalk : Π x : X, V)
(compatible : Π x : X, F.obj (structured_stalk x) ≅ (to_PresheafedSpace.stalk x))

namespace StructuredStalkPresheafedSpace
variables {C V}
variables {F : V ⥤ C}

structure hom (X Y : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) :=
(hom : X.to_PresheafedSpace ⟶ Y.to_PresheafedSpace)
(structured_stalk_map : Π (x : X.X), Y.structured_stalk ((hom : X.X → Y.X) x) ⟶ X.structured_stalk x)
(compatible : Π (x : X.X), F.map (structured_stalk_map x) = (Y.compatible (hom x)).hom ≫ PresheafedSpace.stalk_map hom x ≫ (X.compatible x).inv)

@[extensionality] lemma hom.ext
  {X Y : StructuredStalkPresheafedSpace.{v₁ v₂} C V F} {f g : hom X Y}
  (w : f.hom = g.hom) (h : sorry): f = g :=
begin
  cases f, cases g,
  congr,
  assumption,
  sorry,
  sorry,
end


def id (X : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) : hom X X :=
{ hom := 𝟙 _,
  structured_stalk_map := λ x, 𝟙 _,
  compatible := sorry, }

def comp (X Y Z : StructuredStalkPresheafedSpace.{v₁ v₂} C V F) (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ hom := f.hom ≫ g.hom,
  structured_stalk_map := λ x, g.structured_stalk_map ((f.hom : X.X → Y.X) x) ≫ f.structured_stalk_map x,
  compatible := sorry, }

instance category_of_structured_presheaves : category (StructuredStalkPresheafedSpace.{v₁ v₂} C V F) :=
{ hom  := hom,
  id   := id,
  comp := comp,
  comp_id' := sorry,
  id_comp' := sorry,
  assoc' := sorry }


end StructuredStalkPresheafedSpace

end category_theory
