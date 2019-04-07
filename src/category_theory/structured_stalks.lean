import category_theory.stalks

universes v₁ v₂ u₁ u₂

open category_theory.limits

namespace category_theory

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
include 𝒞
variables [H : has_colimits.{v₁} C]

structure StructuredStalkPresheafedSpace (F : C ⥤ Type v₁) extends PresheafedSpace.{v₁} C :=
(stalk_structure : Π x : X, F.obj (@PresheafedSpace.stalk C _ H to_PresheafedSpace x))

end category_theory
