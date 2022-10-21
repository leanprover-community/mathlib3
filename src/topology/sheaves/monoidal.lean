import category_theory.monoidal.internal.functor_category
import algebra.category.Group.monoidal
import category_theory.functor.equivalence
import category_theory.sites.sheafification

noncomputable theory

open category_theory category_theory.monoidal category_theory.limits

section Ab

namespace presheaf

universes w u₁ v₁
variables {C : Type u₁} [category.{v₁} C]

local attribute [instance] AddCommGroup.Mon_.tensor_monoidal_category

@[simps] def Mon_presheaf_Ab_equiv_presheaf_ring :
  Mon_ (Cᵒᵖ ⥤ AddCommGroup.{w}) ≌ (Cᵒᵖ ⥤ Ring.{w}) :=
(Mon_functor_category_equivalence Cᵒᵖ AddCommGroup).trans $
  category_theory.functor.equivalence_of_target_equivalence _ _ _ $
    AddCommGroup.Mon_.Mon_equiv_Ring

end presheaf

end Ab

namespace Sheaf

-- need sheafification
universes w v u
variables {C : Type u} [category.{v} C] {J : grothendieck_topology C}
variables {D : Type w} [category.{max v u} D]

def iso.mk (X Y : Sheaf J D) (α : X.val ≅ Y.val) : X ≅ Y :=
{ hom := ⟨α.hom⟩,
  inv := ⟨α.inv⟩,
  hom_inv_id' := Sheaf.hom.ext _ _ α.hom_inv_id',
  inv_hom_id' := Sheaf.hom.ext _ _ α.inv_hom_id' }

variables
  [monoidal_category D]
  [concrete_category.{max v u} D]
  [preserves_limits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
  [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
  [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
  [reflects_isomorphisms (forget D)]


namespace monoidal

@[simps] def tensor_obj' (X Y : Sheaf J D) : Sheaf J D :=
(presheaf_to_Sheaf J D).obj (X.val ⊗ Y.val : Cᵒᵖ ⥤ D)

@[simps] def tensor_hom' {X X' Y Y' : Sheaf J D} (f : X ⟶ X') (g : Y ⟶ Y') :
  tensor_obj' X Y ⟶ tensor_obj' X' Y' :=
(presheaf_to_Sheaf J D).map (f.val ⊗ g.val)

@[simps] def tensor_unit' : Sheaf J D :=
(presheaf_to_Sheaf J D).obj
{ obj := λ c, 𝟙_ D,
  map := λ a b f, 𝟙 _,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, (category.comp_id _).symm }

instance : monoidal_category (Sheaf J D) :=
{ -- data
  tensor_obj := tensor_obj',
  tensor_hom := λ _ _ _ _, tensor_hom',
  tensor_unit := tensor_unit',
  associator := _,
  left_unitor := _,
  right_unitor := _,


  tensor_id' := _,
  tensor_comp' := _,

  associator_naturality' := _,

  left_unitor_naturality' := _,
  right_unitor_naturality' := _,

  pentagon' := _,
  triangle' := _ }

end monoidal

end Sheaf
