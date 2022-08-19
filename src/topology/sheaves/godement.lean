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

@[simps] def godement_presheaf_obj (U : (opens X)ᵒᵖ) :
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
{ app := λ U, to_godement_presheaf_aux 𝓕 U ≫ (godement_presheaf_obj 𝓕 U).inv,
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

lemma godement_presheaf_stalk [decidable_eq X] (x : X) :
  (godement_presheaf 𝓕).stalk x ≅ 𝓕.stalk x :=
let ccc : colimit_cocone ((open_nhds.inclusion x).op ⋙ 𝓕) :=
{ cocone :=
  { X := (godement_presheaf 𝓕).stalk x,
    ι :=
    { app := λ U, _,
      naturality' := _ } },
  is_colimit := _ } in
(colimit.iso_colimit_cocone ccc)

lemma godement_presheaf_is_sheaf (h : 𝓕.is_sheaf) : (godement_presheaf 𝓕).is_sheaf :=
limit_is_sheaf _ $ λ ⟨x⟩, (skyscraper_sheaf x _).2

def godement_sheaf : sheaf C X :=
⟨godement_presheaf 𝓖.1, godement_presheaf_is_sheaf _ 𝓖.2⟩

def godement_sheaf_obj (U : (opens X)ᵒᵖ) :
  (godement_sheaf 𝓖).1.obj U ≅ ∏ (λ x, (skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U) :=
godement_presheaf_obj 𝓖.1 U

def to_godement_sheaf : 𝓖 ⟶ godement_sheaf 𝓖 :=
⟨to_godement_presheaf 𝓖.1⟩

variables [concrete_category.{u} C] [preserves_limits (forget C)]
variables [Π (U : opens X), preserves_colimits_of_shape
  ((opens.grothendieck_topology X).cover U)ᵒᵖ (forget C)]
variables [reflects_isomorphisms (forget C)] [preserves_filtered_colimits (forget C)]

def sheaf_in_Type : sheaf C X ⥤ sheaf (Type u) X :=
{ obj := λ F, ⟨F.1 ⋙ forget C, (presheaf.is_sheaf_iff_is_sheaf_comp (forget C) F.1).mp F.2⟩,
  map := λ F G f, Sheaf.hom.mk
  { app := λ U, (forget C).map (f.1.app U),
    naturality' := λ U V inc, by erw [←(forget C).map_comp, ←(forget C).map_comp, f.1.naturality] },
  map_id' := λ F, by { ext, dsimp, rw [id_apply] },
  map_comp' := λ F G H f g, by { ext, dsimp, rw [comp_apply] } }

example : true := trivial


def godement_sheaf_in_Type : sheaf (Type u) X := sheaf_in_Type.obj (godement_sheaf 𝓖)

def godement_sheaf_in_Type_obj_aux (U : (opens X)ᵒᵖ) :
  (forget C).obj ∏ (λ x, (skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U) ≅
  ∏ (λ x, (forget C).obj ((skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U)) :=
{ hom := pi.lift $ λ p, (forget C).map $ pi.π _ p,
  inv :=
  begin
    refine lim_map _ ≫ (preserves_limit_iso (forget C) _).inv,
    refine { app := λ p x, x, naturality' := _ },
    rintros ⟨p⟩ ⟨q⟩ ⟨⟨(eq1 : p = q)⟩⟩,
    dsimp,
    induction eq1,
    ext1,
    dsimp,
    simp only [discrete.functor_map_id, types_id_apply, id_apply],
  end,
  hom_inv_id' :=
  begin
    rw [←category.assoc, limit.lift_map, iso.comp_inv_eq, category.id_comp],
    refine limit.hom_ext _,
    rintros ⟨p⟩,
    rw [preserves_limits_iso_hom_π, limit.lift_π],
    simpa only [cones.postcompose_obj_π, nat_trans.comp_app, fan.mk_π_app, forget_map_eq_coe],
  end,
  inv_hom_id' :=
  begin
    ext1 ⟨p⟩,
    rw [category.assoc, limit.lift_π, fan.mk_π_app, category.assoc, preserves_limits_iso_inv_π,
      lim_map_π, category.id_comp],
    refl,
  end }

def godement_sheaf_in_Type_obj (U : (opens X)ᵒᵖ) :
  (godement_sheaf_in_Type 𝓖).1.obj U ≅
  ∏ (λ x, (forget C).obj $ (skyscraper_presheaf x (𝓖.presheaf.stalk x)).obj U) :=
((forget C).map_iso $ godement_sheaf_obj 𝓖 U) ≪≫ godement_sheaf_in_Type_obj_aux 𝓖 U

def sheaf_in_Type_skyscraper_sheaf (x : X) (c : C) :
  (sheaf_in_Type.obj $ skyscraper_sheaf x c) ≅
  skyscraper_sheaf x ((forget C).obj c) :=
{ hom := Sheaf.hom.mk
  { app := λ U, eq_to_hom
    begin
      change (forget C).obj _ = (skyscraper_sheaf x ((forget C).obj c)).1.obj _,
      by_cases hU : x ∈ U.unop,
      { erw [skyscraper_presheaf_obj_of_mem _ hU, skyscraper_presheaf_obj_of_mem _ hU], },
      { erw [skyscraper_presheaf_obj_of_not_mem _ hU, skyscraper_presheaf_obj_of_not_mem _ hU],
        -- need to make "skyscraper_presheaf_with_specified_terminal_object"
          },
    end,
    naturality' := λ U V inc,
    begin
      dsimp,
      rw [comp_dite, dite_comp],
      by_cases hV : x ∈ V.unop,
      { have hU : x ∈ U.unop := le_of_hom inc.unop hV,
        split_ifs,
        -- generalize_proofs _ h1 h2 h3 h4,
        change (sheaf_in_Type.obj (skyscraper_sheaf x c)).val.map inc ≫
            (forget C).map (eq_to_hom _) ≫ eq_to_hom _ =
          ((forget C).map (eq_to_hom _) ≫ eq_to_hom _) ≫
            (skyscraper_sheaf x ((forget C).obj c)).val.map inc,
        rw [eq_to_hom_map, eq_to_hom_map, eq_to_hom_trans, eq_to_hom_trans],
        generalize_proofs _ h1 h2,

        sorry,
        -- have := (sheaf_in_Type.obj (skyscraper_sheaf x c)).1.map_comp,
        -- unfold_coes,
        -- erw show (forget C).map (eq_to_hom h1) = _, from rfl,
        -- erw [eq_to_hom_map (forget C) h1],
        },
      { split_ifs,
        rw [←category.assoc, eq_comp_eq_to_hom],
        exact terminal_is_terminal.hom_ext _ _, },
    end },
  inv := Sheaf.hom.mk
  { app := λ U, if m : x ∈ U.unop
      then eq_to_hom _
      else _,
    naturality' := _ },
  hom_inv_id' := _,
  inv_hom_id' := _ }

lemma stalk_bundles (U : (opens X)ᵒᵖ) (s : (sheaf_in_Type.obj 𝓖).1.obj U)
  (x : U.unop) : presheaf.stalk (sheaf_in_Type.obj 𝓖).1 x :=
-- let S : (sheaf_in_Type.obj (skyscraper_sheaf x.val (𝓖.presheaf.stalk x.val))).1.obj U :=
--    in
-- presheaf.germ
begin
  have : (sheaf_in_Type.obj (skyscraper_sheaf x.val (𝓖.presheaf.stalk x.val))).1.obj U,
  {  },
  -- (types.product_iso _).hom (((godement_sheaf_in_Type_obj 𝓖 U).hom ((sheaf_in_Type.map (to_godement_sheaf 𝓖)).1.app U s))) x.1,
  dsimp at S,
  have := (sheaf_in_Type.obj 𝓖).presheaf.germ x,
  -- have := ,
  have := (types.product_iso _).hom (((godement_sheaf_in_Type_obj 𝓖 U).hom ((sheaf_in_Type.map (to_godement_sheaf 𝓖)).1.app U s))) x.1,
end


lemma to_godement_sheaf_app_injective (U : opens X) :
  function.injective $ (forget C).map ((to_godement_sheaf 𝓖).1.app (opposite.op U)) :=
λ x y eq1,
begin
  change (sheaf_in_Type.obj 𝓖).1.obj (opposite.op U) at x,
  change (sheaf_in_Type.obj 𝓖).1.obj (opposite.op U) at y,
  change (sheaf_in_Type.map (to_godement_sheaf 𝓖)).1.app (opposite.op U) x =
    (sheaf_in_Type.map (to_godement_sheaf 𝓖)).1.app (opposite.op U) y at eq1,
  apply presheaf.section_ext,
  /-
  U : opens ↥X,
  x y : (sheaf_in_Type.obj 𝓖).val.obj (opposite.op U),
  eq1 :
    (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app (opposite.op U) x =
      (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app (opposite.op U) y,
  p : ↥U
  ⊢ ⇑(𝓖.presheaf.germ p) x = ⇑(𝓖.presheaf.germ p) y
  -/

  intros p,
  have := presheaf.germ_ext 𝓖.1 U p.2;
  -- ext,
  sorry
end

instance : mono $ to_godement_sheaf 𝓖 :=
begin
  rw presheaf.mono_iff_stalk_mono,
  intros x,
  change mono ((presheaf.stalk_functor C x).map (to_godement_presheaf 𝓖.1)),
  rw concrete_category.mono_iff_injective_of_preserves_pullback,
  exact (presheaf.app_injective_iff_stalk_functor_map_injective (to_godement_presheaf 𝓖.1)).mpr
    (to_godement_sheaf_app_injective 𝓖) x,
end

end presheaf
