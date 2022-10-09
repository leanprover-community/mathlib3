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
variables (𝓕 : presheaf C X)

/--
The `godement_presheaf` for a presheaf `𝓕` is defined as a product presheaf `∏ₓ skyscraper(𝓕ₓ)`
-/
def godement_presheaf : presheaf C X :=
∏ (λ x, skyscraper_presheaf x (𝓕.stalk x) : X → presheaf C X)

/--
The sections of `godement_presheaf` on opens `U` is isomorphic to `∏ₓ skyscraper(x, 𝓕ₓ)(U)`, i.e.
the categorical definition and the concrete definition agree.
-/
@[simps] def godement_presheaf_obj (U : (opens X)ᵒᵖ) :
  (godement_presheaf 𝓕).obj U ≅ ∏ (λ x, (skyscraper_presheaf x (𝓕.stalk x)).obj U) :=
limit_obj_iso_limit_comp_evaluation _ _ ≪≫
{ hom := lim_map { app := λ _, 𝟙 _, naturality' := by { rintros ⟨x⟩ ⟨y⟩ ⟨⟨(rfl : x = y)⟩⟩, refl } },
  inv := lim_map { app := λ _, 𝟙 _, naturality' := by { rintros ⟨x⟩ ⟨y⟩ ⟨⟨(rfl : x = y)⟩⟩, refl } },
  hom_inv_id' :=
  begin
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

/--
Let `U` be an open set, since `𝓕(U) ⟶ 𝓕ₓ` or `𝓕(U) ⟶ *` depending on `x ∈ U` or not where `*`
is a terminal object, there is a product map `𝓕(U) ⟶ ∏ₓ, 𝓕ₓ or *`.
-/
def to_godement_presheaf_aux (U : (opens X)ᵒᵖ) :
  𝓕.obj U ⟶ ∏ λ (x : X), (skyscraper_presheaf x (𝓕.stalk x)).obj U :=
pi.lift $ λ x, if m : x ∈ U.unop
  then 𝓕.germ ⟨x, m⟩ ≫ eq_to_hom (by rw [skyscraper_presheaf_obj, if_pos m, subtype.coe_mk])
  else terminal.from _ ≫ eq_to_hom (by rw [skyscraper_presheaf_obj, if_neg m])

/--
Let `U` be an open set, if `p ∈ U`, then there is morphism `𝓕(U) ⟶ 𝓕ₚ` by composing the product
map `to_godement_presheaf_aux` with projection map `pi.π`. This agrees with the `germ` morphism.
-/
def to_godement_presheaf_aux_comp_π {U : (opens X)ᵒᵖ} (p : U.unop) :
  𝓕.obj U ⟶ 𝓕.stalk p :=
to_godement_presheaf_aux 𝓕 U ≫ pi.π _ p ≫ eq_to_hom (if_pos p.2)

@[simp] lemma to_godement_presheaf_aux_comp_π_eq {U : (opens X)ᵒᵖ} (p : U.unop) :
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

/--
Under the isomorphism `godement_presheaf(𝓕, U) ≅ ∏ₓ skyscraper(x, 𝓕ₓ)(U)`, there is a morphism
`𝓕 ⟶ ∏ₓ skyscraper(x, 𝓕ₓ) ≅ godement_presheaf(𝓕)`
-/
@[simps] def to_godement_presheaf : 𝓕 ⟶ godement_presheaf 𝓕 :=
{ app := λ U, to_godement_presheaf_aux 𝓕 U ≫ (godement_presheaf_obj 𝓕 U).inv,
  naturality' := λ U V inc,
  begin
    ext ⟨x⟩,
    dunfold to_godement_presheaf_aux godement_presheaf_obj discrete.functor,
    simp only [iso.trans_inv, category.assoc, limit_obj_iso_limit_comp_evaluation_inv_π_app,
      lim_map_π, category.comp_id, nat_trans.naturality, skyscraper_presheaf_map, category.id_comp,
      limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc, lim_map_π_assoc],
    erw [limit.lift_π, fan.mk_π_app, ←category.assoc, limit.lift_π, fan.mk_π_app],
    dsimp only,
    by_cases hV : x ∈ opposite.unop V,
    { have hU : x ∈ U.unop := (le_of_hom inc.unop) hV,
      simp_rw [dif_pos hV, dif_pos hU],
      erw [←category.assoc, 𝓕.germ_res inc.unop, category.assoc, eq_to_hom_trans],
      refl, },
    { simp_rw [dif_neg hV],
      apply ((if_neg hV).symm.rec terminal_is_terminal).hom_ext, },
  end }

end presheaf
