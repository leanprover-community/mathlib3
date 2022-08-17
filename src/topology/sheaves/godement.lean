import topology.sheaves.sheaf
import topology.sheaves.limits
import topology.sheaves.skyscraper
import topology.sheaves.stalks
import category_theory.preadditive.injective

noncomputable theory

section presheaf

open Top
open topological_space
open category_theory
open category_theory.limits

universes u v

variables {X : Top.{u}} {C : Type v} [category.{u} C]
variables [has_limits C] [has_terminal C] [has_colimits C]
variables [Π (x : X) (U : opens X), decidable (x ∈ U)]
variable (𝓕 : presheaf C X)

def godement : presheaf C X :=
∏ (λ x, skyscraper_presheaf x (𝓕.stalk x) : X → presheaf C X)

@[simps] def godement_app (U : (opens X)ᵒᵖ) :
  (godement 𝓕).obj U ≅ ∏ (λ x, (skyscraper_presheaf x (𝓕.stalk x)).obj U) :=
limit_obj_iso_limit_comp_evaluation _ _ ≪≫
{ hom := lim_map
  { app := λ _, 𝟙 _,
    naturality' := by { rintros ⟨x⟩ ⟨y⟩ ⟨⟨(rfl : x = y)⟩⟩, refl } },
  inv := lim_map
  { app := λ _, 𝟙 _,
    naturality' := by { rintros ⟨x⟩ ⟨y⟩ ⟨⟨(rfl : x = y)⟩⟩, refl } },
  hom_inv_id' :=
  begin
    dsimp,
    ext,
    erw [category.assoc, lim_map_π, ←category.assoc, lim_map_π, category.id_comp, category.comp_id,
      category.comp_id],
  end,
  inv_hom_id' :=
  begin
    dsimp,
    ext,
    erw [category.assoc, lim_map_π, ←category.assoc, lim_map_π, category.comp_id, category.id_comp,
      category.comp_id],
  end }

@[reducible]
def to_godement_aux (U : (opens X)ᵒᵖ) :
  𝓕.obj U ⟶ ∏ λ (x : X), ite (x ∈ opposite.unop U) (𝓕.stalk x) (⊤_ C) :=
pi.lift (λ x, if m : x ∈ U.unop
  then 𝓕.germ ⟨x, m⟩ ≫ eq_to_hom ((skyscraper_presheaf_obj_of_mem _ m).symm.trans (by congr) :
    𝓕.stalk (⟨x, m⟩ : U.unop) = (skyscraper_presheaf x (𝓕.stalk x)).obj U)
  else terminal.from _ ≫ eq_to_hom (skyscraper_presheaf_obj_of_not_mem _ m).symm)

@[simps] def to_godement : 𝓕 ⟶ godement 𝓕 :=
{ app := λ U, to_godement_aux 𝓕 U ≫ (godement_app 𝓕 U).inv,
  naturality' :=
  begin
    intros U V inc,
    ext ⟨x⟩,
    dsimp,
    simp only [category.assoc, limit_obj_iso_limit_comp_evaluation_inv_π_app, lim_map_π,
      category.comp_id, nat_trans.naturality],
    simp only [←category.assoc _ _ ((skyscraper_presheaf _ _).map inc),
      limit_obj_iso_limit_comp_evaluation_inv_π_app, lim_map_π, category.comp_id],
    simp only [limit.lift_π, fan.mk_π_app, skyscraper_presheaf_map, category.id_comp,
      eq_to_hom_trans, comp_dite],
    dsimp,
    split_ifs with hV,
    { have hU : x ∈ U.unop := (le_of_hom inc.unop) hV,
      split_ifs,
      erw [category.assoc, eq_to_hom_trans, ←category.assoc, eq_comp_eq_to_hom,
        category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id, 𝓕.germ_res inc.unop],
      refl },
    { rw [←category.assoc, eq_comp_eq_to_hom, category.assoc, category.assoc, eq_to_hom_trans,
        eq_to_hom_refl, category.comp_id],
      exact terminal_is_terminal.hom_ext _ _ },
  end }

lemma godement_is_sheaf (h : 𝓕.is_sheaf) : (godement 𝓕).is_sheaf :=
_

end presheaf
