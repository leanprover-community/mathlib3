import category_theory.presheaf

universes u₁ u₂ v

namespace category_theory
open category_theory.limits

section
variables (C : Type u₁) [𝒞 : category.{u₁ v} C] (D : Type u₂) [𝒟 : category.{u₂ v} D]
include 𝒞 𝒟

structure cocontinuous_functor :=
(F : C ⥤ D)
(preserves : preserves_colimits F)

instance cocontinuous_functor.category : category (cocontinuous_functor.{u₁ u₂ v} C D) :=
{ hom  := λ F G, F.1 ⟹ G.1,
  id   := λ F, nat_trans.id F.1,
  comp := λ F G H s t, s ⊟ t }

variables {C D}
@[extensionality] def cocontinuous_functor.ext {F G : cocontinuous_functor.{u₁ u₂ v} C D}
  (i : F.F ≅ G.F) : F ≅ G :=
{ hom := i.hom,
  inv := i.inv,
  hom_inv_id' := by ext; erw i.hom_inv_id; refl,
  inv_hom_id' := by ext; erw i.inv_hom_id; refl }

end

section
variables (C : Type v) [𝒞 : small_category C] (D : Type u₂) [𝒟 : category.{u₂ v} D]
include 𝒞 𝒟
variables [has_colimits.{u₂ v} D]

def extension : (C ⥤ D) ⥤ cocontinuous_functor.{(v+1) u₂ v} (presheaf C) D :=
{ obj := λ F,
    ⟨yoneda_extension F, adjunction.left_adjoint_preserves_colimits (yoneda_extension_adj F)⟩,
  map := λ F G t,
  { app := λ X, colim.map (whisker_left _ t),
    naturality' := begin
      intros X Y f, dsimp { iota := tt },
      rw [yoneda_extension_map_eq, yoneda_extension_map_eq],
      dsimp [yoneda_extension_map],
      rw colimit.map_pre,
      refl
    end },
  map_id' := λ F, by ext1; exact colim.map_id _,
  map_comp' := λ F G H s t, by ext1; exact colim.map_comp (whisker_left _ s) (whisker_left _ t) }

def restriction : cocontinuous_functor.{(v+1) u₂ v} (presheaf C) D ⥤ (C ⥤ D) :=
{ obj := λ F, yoneda ⋙ F.1,
  map := λ F G t, { app := λ X, t.app _, naturality' := by intros; apply t.naturality } }

def extension_restriction : extension C D ⋙ restriction C D ≅ functor.id _ :=
nat_iso.of_components (λ F, yoneda_extension_is_extension F)
  begin
    intros F G t,
    ext1 X,
    dsimp [extension, restriction, yoneda_extension_is_extension, nat_iso.of_components],
    dsimp [coext_equiv, equiv.trans, equiv.symm, equiv.refl],
    dsimp [yoneda_extension_adj],
    rw [adjunction.adjunction_of_equiv_left_equiv, adjunction.adjunction_of_equiv_left_equiv],
    dsimp [yoneda_extension_e, equiv.trans, equiv.symm, equiv.refl, is_colimit.equiv,
      equiv.subtype_equiv_subtype, equiv.subtype_equiv_of_subtype, equiv.Pi_congr_right,
      equiv.arrow_congr],
    rw [colimit.map_desc, ←colimit.desc_extend],
    dsimp [cocone.precompose, cocone.extend], congr' 2,
    ext j,
    dsimp [restricted_yoneda, yoneda_equiv],
    rw [category.comp_id, category.comp_id],
    rw t.naturality, refl
  end

def restriction_extension : restriction C D ⋙ extension C D ≅ functor.id _ :=
nat_iso.of_components (λ F, by haveI := F.2; ext; exact (colimit_preserving_is_extension F.1).symm)
  begin
    rintros ⟨F, hF⟩ ⟨G, hG⟩ t, resetI, change F ⟹ G at t,
    ext1 X,
    dsimp [cocontinuous_functor.ext, colimit_preserving_is_extension, nat_iso.of_components],
    dsimp [colimit_cocone.ext, cocones.vertex, extension],
    change _ ≫ _ = _ ≫ _, dsimp { iota := tt },
    erw colimit.map_desc,
    rw ←colimit.desc_extend,
    dsimp [cocone.precompose, cocone.extend], congr' 2,
    ext j,
    dsimp [canonical_diagram.cocone],
    rw [t.naturality],
    refl
  end

end

end category_theory
