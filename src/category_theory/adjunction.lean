import category_theory.limits.preserves
import category_theory.whiskering
import data.equiv.basic

namespace category_theory
open category
open category_theory.limits

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

structure adjunction.core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π {X Y}, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(hom_equiv_naturality_left : Π {X' X Y} (f : X' ⟶ X) (g : F.obj X ⟶ Y),
  hom_equiv.to_fun (F.map f ≫ g) = f ≫ hom_equiv.to_fun g)
(hom_equiv_naturality_right : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  hom_equiv.to_fun (f ≫ g) = hom_equiv.to_fun f ≫  G.map g)
(hom_equiv_naturality_left_symm : Π {X' X Y} (f : X' ⟶ X) (g : X ⟶  G.obj Y),
  hom_equiv.inv_fun (f ≫ g) = F.map f ≫ hom_equiv.inv_fun g)
(hom_equiv_naturality_right_symm : Π {X Y Y'} (f : X ⟶  G.obj Y) (g : Y ⟶ Y'),
  hom_equiv.inv_fun (f ≫ G.map g) = hom_equiv.inv_fun f ≫  g)

structure adjunction.core_unit_counit (F : C ⥤ D) (G : D ⥤ C) :=
(unit : functor.id C ⟹ F.comp G)
(counit : G.comp F ⟹ functor.id D)
(left_triangle : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _)
(right_triangle : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _)

/--
`adjunction F G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) extends
  (adjunction.core_hom_equiv F G), (adjunction.core_unit_counit F G) :=
(hom_equiv_id_left : Π {X}, hom_equiv.to_fun (𝟙 (F.obj X)) = unit.app X)
(hom_equiv_id_right : Π {Y}, hom_equiv.inv_fun (𝟙 (G.obj Y)) = counit.app Y)

namespace adjunction
variables {F : C ⥤ D} {G : D ⥤ C}

def of_core_hom_equiv (adj : core_hom_equiv F G) : adjunction F G :=
{ unit : _,
  .. adj }

end adjunction

end category_theory
