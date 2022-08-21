/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import topology.sheaves.sheaf
import topology.sheaves.limits
import topology.sheaves.skyscraper
import topology.sheaves.stalks
import category_theory.preadditive.injective

/-!
# Godement resolution

For a presheaf `𝓕 : (opens X)ᵒᵖ ⥤ C`, we can embedded `𝓕` into a sheaf `∏ₓ skyscraper(𝓕ₓ)` where
`x` ranges over `X` and `𝓕 ⟶ ∏ₓ skyscraper(𝓕ₓ)` is mono.

## Main definition
* `godement_presheaf`: for a presheaf `𝓕`, its Godement presheaf is `∏ₓ skyscraper(𝓕ₓ)`
* `to_godement_presheaf`: the canonical map `𝓕 ⟶ godement_presheaf 𝓕` sending `s : 𝓕(U)` to a
  bundle of stalks `x ↦ sₓ`.
* `godement_sheaf`: the Godement presheaf of any presheaf is a sheaf.
* `to_godement_sheaf`: for a sheaf `𝓖`, the canonical sheaf morphism `𝓖 ⟶ godement_sheaf 𝓖.1`.
For a sheaf `𝓖 : sheaf C X` where `C` is concrete and the forgetful functor preserves limits and
filtered colimits
* `mono_to_godement_sheaf`: the canonical map `𝓖 ⟶ godement_sheaf 𝓖` is mono.
If further `C` has enough injectives
* `sheaf_enough_inj_aux.injective_sheaf`: since each `𝓕ₓ` can be embedded into `𝓕ₓ ⟶ I(x)` via a
  monomorphism, `𝓖` can be embedded into `∏ₓ skyscraper(I(x))`.
* `sheaf_enough_inj_aux.injective_J`: `∏ₓ skyscraper(I(x))` is injective.
* `sheaf_enough_inj_aux.to_J_mono`: the canonical map `𝓖 ⟶ ∏ₓ skyscraper(I(x))` is mono.
* `sheaf_has_enough_injectives`: the category of sheaves on `X` in `C` has enough injectives.
-/


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

@[reducible]
def to_godement_presheaf_aux_comp_π {U : (opens X)ᵒᵖ} (p : U.unop) :
  𝓕.obj U ⟶ 𝓕.stalk p :=
to_godement_presheaf_aux 𝓕 U ≫ pi.π _ p ≫ eq_to_hom (if_pos p.2)

lemma to_godement_presheaf_aux_comp_π_eq {U : (opens X)ᵒᵖ} (p : U.unop) :
  to_godement_presheaf_aux_comp_π 𝓕 p = presheaf.germ 𝓕 p :=
begin
  dunfold to_godement_presheaf_aux_comp_π presheaf.germ to_godement_presheaf_aux,
  rw [←category.assoc, limit.lift_π],
  simp only [fan.mk_π_app],
  split_ifs,
  { rw [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id],
    refl },
  { exfalso, exact h p.2, },
end

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
variables [reflects_isomorphisms (forget C)] [preserves_filtered_colimits (forget C)]

@[simps] def sheaf_in_Type : sheaf C X ⥤ sheaf (Type u) X :=
{ obj := λ F, ⟨F.1 ⋙ forget C, (presheaf.is_sheaf_iff_is_sheaf_comp (forget C) F.1).mp F.2⟩,
  map := λ F G f, Sheaf.hom.mk
  { app := λ U, (forget C).map (f.1.app U),
    naturality' := λ U V inc, by erw [←(forget C).map_comp, ←(forget C).map_comp, f.1.naturality] },
  map_id' := λ F, by { ext, dsimp, rw [id_apply] },
  map_comp' := λ F G H f g, by { ext, dsimp, rw [comp_apply] } }

def stalk_bundles_eq0 (U : (opens X)ᵒᵖ) (x y : (sheaf_in_Type.obj 𝓖).1.obj U)
  (eq1 : (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app U x =
      (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app U y) (p : U.unop) :
  (forget C).map (to_godement_presheaf_aux 𝓖.presheaf U) x =
  (forget C).map (to_godement_presheaf_aux 𝓖.presheaf U) y :=
begin
  change (forget C).map ((to_godement_presheaf 𝓖.presheaf).app _) x =
    (forget C).map ((to_godement_presheaf 𝓖.presheaf).app _) y at eq1,
  dsimp at eq1,
  change (forget C).map _ x = (forget C).map _ y at eq1,
  have eq2 := congr_arg ((forget C).map (limit_obj_iso_limit_comp_evaluation (discrete.functor _) U).hom) eq1,
  dsimp at eq2,
  erw [←comp_apply, ←comp_apply, ←category.assoc] at eq2,
  simp only [category.assoc, iso.inv_hom_id, category.comp_id] at eq2,
  set α : nat_trans (discrete.functor (λ (x : ↥X), ite (x ∈ opposite.unop U) (𝓖.presheaf.stalk x) (⊤_ C)))
  (discrete.functor (λ (x : ↥X), skyscraper_presheaf x (𝓖.presheaf.stalk x)) ⋙
     (evaluation (opens ↥X)ᵒᵖ C).obj U) := _,
  change (forget C).map (_ ≫ lim_map α) x = (forget C).map (_ ≫ lim_map α) y at eq2,
  haveI : is_iso (lim_map α),
  { refine is_iso.mk ⟨lim_map { app := λ x, 𝟙 _, naturality' := _ }, _, _⟩,
    { rintros ⟨x⟩ ⟨y⟩ ⟨⟨eq0 : x = y⟩⟩, subst eq0, refl},
    { ext1, simp only [category.assoc, lim_map_π, category.comp_id, category.id_comp], },
    { ext1, simp only [category.assoc, lim_map_π, category.comp_id, category.id_comp], }, },
  have eq3 := congr_arg ((forget C).map (inv (lim_map α))) eq2,
  change ((forget C).map _ ≫ (forget C).map _) _ = ((forget C).map _ ≫ (forget C).map _) _ at eq3,
  simpa only [←(forget C).map_comp, category.assoc, is_iso.hom_inv_id,category.comp_id] using eq3,
end

def stalk_bundles_eq (U : (opens X)ᵒᵖ) (x y : (sheaf_in_Type.obj 𝓖).1.obj U)
  (eq1 : (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app U x =
      (sheaf_in_Type.map (to_godement_sheaf 𝓖)).val.app U y) (p : U.unop) :
  (forget C).map (𝓖.presheaf.germ p) x = (forget C).map (𝓖.presheaf.germ p) y :=
begin
  have eq1' := stalk_bundles_eq0 𝓖 U x y eq1 p,
  have eq1'' : (forget C).map (to_godement_presheaf_aux_comp_π 𝓖.presheaf p) x =
    (forget C).map (to_godement_presheaf_aux_comp_π 𝓖.presheaf p) y,
  { dsimp at eq1' ⊢,
    dunfold to_godement_presheaf_aux_comp_π,
    simp only [comp_apply, eq1'], },
  rwa to_godement_presheaf_aux_comp_π_eq at eq1'',
end

example : true := trivial

instance mono_to_godement_sheaf : mono $ to_godement_sheaf 𝓖 :=
begin
  rw presheaf.mono_iff_stalk_mono,
  intros x,
  change mono ((presheaf.stalk_functor C x).map (to_godement_presheaf 𝓖.1)),
  rw concrete_category.mono_iff_injective_of_preserves_pullback,
  exact (presheaf.app_injective_iff_stalk_functor_map_injective (to_godement_presheaf 𝓖.1)).mpr
    (λ U x y H, presheaf.section_ext _ _ _ _ (λ p, stalk_bundles_eq 𝓖 (opposite.op U) x y H p)) x,
end

section enough_injectives

variables [enough_injectives C]

namespace sheaf_enough_inj_aux

def injective_sheaf : sheaf C X :=
⟨∏ (λ x, skyscraper_presheaf x (injective.under $ 𝓕.stalk x) : X → presheaf C X),
 limit_is_sheaf _ $ λ ⟨x⟩, (skyscraper_sheaf x _).2⟩

def injective_sheaf_iso :
  injective_sheaf 𝓖.1 ≅
  ∏ (λ x, skyscraper_sheaf x (injective.under $ 𝓖.presheaf.stalk x)) :=
{ hom := Sheaf.hom.mk $ eq_to_hom begin
    change limit _ = limit _, congr, apply category_theory.functor.ext,
    { rintros ⟨p⟩ ⟨q⟩ ⟨⟨(eq1 : p = q)⟩⟩, subst eq1,
      rw [eq_to_hom_refl, category.id_comp, eq_to_hom_refl, category.comp_id], refl, },
    { rintros ⟨p⟩, dsimp, refl, },
  end ≫ (preserves_limit_iso (sheaf.forget C X) _).inv,
  inv := Sheaf.hom.mk $ (preserves_limit_iso (sheaf.forget C X) _).hom ≫ eq_to_hom begin
    change limit _ = limit _, congr, apply category_theory.functor.ext,
    { rintros ⟨p⟩ ⟨q⟩ ⟨⟨(eq1 : p = q)⟩⟩, subst eq1,
      rw [eq_to_hom_refl, category.id_comp, eq_to_hom_refl, category.comp_id], refl, },
    { rintros ⟨p⟩, dsimp, refl, },
  end,
  hom_inv_id' :=
  begin
    ext ⟨p⟩ U, dsimp,
    rw [←category.assoc, category.assoc _ _ ((preserves_limit_iso (sheaf.forget C X) _).hom.app U),
      iso.inv_hom_id_app, category.comp_id, category.id_comp, ←nat_trans.comp_app, eq_to_hom_trans,
      eq_to_hom_refl],
    convert category.id_comp _,
  end,
  inv_hom_id' :=
  begin
    ext ⟨p⟩ U, dsimp,
    rw [←category.assoc, category.assoc _ _ (eq_to_hom _), eq_to_hom_trans, eq_to_hom_refl,
      category.comp_id, iso.hom_inv_id],
  end }

local notation `J` := injective_sheaf 𝓖.1

instance injective_J : injective J :=
injective.of_iso (injective_sheaf_iso 𝓖).symm $
@@injective.category_theory.limits.pi_obj.injective _ _ _ $ λ p,
(skyscraper_sheaf_injective p _ : injective
  (skyscraper_sheaf p (injective.under (𝓖.presheaf.stalk p))))

def to_J : 𝓖 ⟶ J :=
Sheaf.hom.mk $ to_godement_presheaf _ ≫
  pi.map (λ p, (skyscraper_presheaf_functor p).map $ injective.ι _)

instance mono_to_J : mono (to_J 𝓖) :=
(Sheaf.hom.mono_iff_presheaf_mono _ _ _).mpr
begin
  haveI t1 : mono (to_godement_sheaf 𝓖) := infer_instance,
  rw Sheaf.hom.mono_iff_presheaf_mono at t1,
  change mono (to_godement_presheaf 𝓖.1) at t1,
  resetI,
  have t21 : ∀ (p : X), mono ((skyscraper_presheaf_functor p).map
    (injective.ι (presheaf.stalk 𝓖.val p))),
  { exact λ p, @@functor.map_mono _ _ (skyscraper_presheaf_functor p)
      (functor.preserves_monomorphisms_of_adjunction (stalk_skyscraper_presheaf_adj p))
      (injective.ι (presheaf.stalk 𝓖.val p)) _, },
  haveI t22 : mono (pi.map (λ p, (skyscraper_presheaf_functor p).map
    (injective.ι (presheaf.stalk 𝓖.val p)))) := @pi.map_mono _ _ _ _ _ _ _ _ t21,
  apply mono_comp,
end

end sheaf_enough_inj_aux

instance sheaf_has_enough_injectives : enough_injectives (sheaf C X) :=
{ presentation := λ 𝓖, nonempty.intro
  { J := sheaf_enough_inj_aux.injective_sheaf 𝓖.1,
    injective := sheaf_enough_inj_aux.injective_J _,
    f := sheaf_enough_inj_aux.to_J _,
    mono := sheaf_enough_inj_aux.mono_to_J 𝓖 } }

end enough_injectives

end presheaf
