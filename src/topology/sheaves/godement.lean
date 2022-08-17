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

variables {X : Top.{u}} {C : Type u} [category.{u} C]
variables [has_limits C] [has_terminal C] [has_colimits C]
variables [Π (x : X) (U : opens X), decidable (x ∈ U)]
variables (𝓕 : presheaf C X) (𝓖 : sheaf C X)

def godement_presheaf : presheaf C X :=
∏ (λ x, skyscraper_presheaf x (𝓕.stalk x) : X → presheaf C X)

@[simps] def godement_presheaf_app (U : (opens X)ᵒᵖ) :
  (godement_presheaf 𝓕).obj U ≅ ∏ (λ x, (skyscraper_presheaf x (𝓕.stalk x)).obj U) :=
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
def to_godement_presheaf_aux (U : (opens X)ᵒᵖ) :
  𝓕.obj U ⟶ ∏ λ (x : X), ite (x ∈ opposite.unop U) (𝓕.stalk x) (⊤_ C) :=
pi.lift (λ x, if m : x ∈ U.unop
  then 𝓕.germ ⟨x, m⟩ ≫ eq_to_hom ((skyscraper_presheaf_obj_of_mem _ m).symm.trans (by congr) :
    𝓕.stalk (⟨x, m⟩ : U.unop) = (skyscraper_presheaf x (𝓕.stalk x)).obj U)
  else terminal.from _ ≫ eq_to_hom (skyscraper_presheaf_obj_of_not_mem _ m).symm)

@[simps] def to_godement_presheaf : 𝓕 ⟶ godement_presheaf 𝓕 :=
{ app := λ U, to_godement_presheaf_aux 𝓕 U ≫ (godement_presheaf_app 𝓕 U).inv,
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

lemma godement_presheaf_is_sheaf (h : 𝓕.is_sheaf) : (godement_presheaf 𝓕).is_sheaf :=
limit_is_sheaf _ $ λ ⟨x⟩, (skyscraper_sheaf x _).2

def godement_sheaf : sheaf C X :=
⟨godement_presheaf 𝓖.1, godement_presheaf_is_sheaf _ 𝓖.2⟩

def godement_sheaf_app (U : (opens X)ᵒᵖ) :
  (godement_sheaf 𝓖).1.obj U ≅ ∏ (λ x, (skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U) :=
godement_presheaf_app 𝓖.1 U

def to_godement_sheaf : 𝓖 ⟶ godement_sheaf 𝓖 :=
⟨to_godement_presheaf 𝓖.1⟩

variables [concrete_category.{u} C] [preserves_limits (forget C)]
variables [Π (U : opens X), preserves_colimits_of_shape
  ((opens.grothendieck_topology X).cover U)ᵒᵖ (forget C)]
variables [reflects_isomorphisms (forget C)]

instance : mono $ to_godement_sheaf 𝓖 := sorry

end presheaf
