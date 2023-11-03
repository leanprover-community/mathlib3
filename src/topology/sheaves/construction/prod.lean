/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import topology.sheaves.limits
import category_theory.limits.functor_category

/-!
# Products in category of (pre)sheaves
-/


noncomputable theory

open category_theory category_theory.limits Top topological_space

universes u v w u'

namespace Top.presheaf

variables {X : Top.{u}} {C : Type v} [category.{w} C]
variables {ι : Type u'} (f : ι → presheaf C X)
variables [has_products_of_shape X C] [has_products_of_shape ι C]

instance has_products_of_shape_X : has_products_of_shape X (presheaf C X) :=
category_theory.limits.functor_category_has_limits_of_shape

instance has_products_of_shape_ι : has_products_of_shape ι (presheaf C X) :=
category_theory.limits.functor_category_has_limits_of_shape

/--
sections of product presheaf is product of sections of presheaves.
-/
def section_product_equiv_product_section (U : (opens X)ᵒᵖ) :
  (∏ f).obj U ≅ ∏ (λ x, (f x).obj U) :=
limit_obj_iso_limit_comp_evaluation _ _ ≪≫ limits.lim.map_iso (discrete.nat_iso $ λ X, iso.refl _)

/--
Let `f : ι → presheaf C X`, `product_presheaf'` is defined by `U ↦ ∏ᵢ (f i)(U)`
-/
@[simps] def product_presheaf' : presheaf C X :=
{ obj := λ U, ∏ (λ x, (f x).obj U),
  map := λ U V inc, pi.map $ λ i, (f i).map inc,
  map_id' := λ U,
  begin
    ext,
    rw [lim_map_π, discrete.nat_trans_app, category.id_comp],
    dsimp only,
    erw [category_theory.functor.map_id, category.comp_id],
  end,
  map_comp' := λ U V W iUV iVW,
  begin
    ext,
    rw [lim_map_π, category.assoc, lim_map_π, discrete.nat_trans_app, discrete.nat_trans_app,
      ←category.assoc, lim_map_π, discrete.nat_trans_app, category.assoc],
    dsimp only,
    rw [(f j.as).map_comp],
  end }

/--
The categorical product of presheaves agree with the concrete representation.
-/
def product_presheaf_iso_product_presheaf' :
  ∏ f ≅ product_presheaf' f :=
nat_iso.of_components (λ U, section_product_equiv_product_section _ _) $
λ U V inc,
begin
  ext1 ⟨j⟩,
  simp only [section_product_equiv_product_section, iso.trans_hom, functor.map_iso_hom,
    lim_map_eq_lim_map, limit_map_limit_obj_iso_limit_comp_evaluation_hom_assoc, category.assoc,
    lim_map_π, discrete.nat_iso_hom_app, iso.refl_hom, category.comp_id, whisker_left_app,
    evaluation_map_app, limit_obj_iso_limit_comp_evaluation_hom_π_assoc, product_presheaf'_map,
    discrete.nat_trans_app, lim_map_π_assoc, category.id_comp],
  refl,
end

end Top.presheaf

namespace sheaf

variables {X : Top.{w}} {C : Type v} [category.{w} C]
variables {ι : Type w} (f : ι → sheaf C X) [has_limits.{w} C]

/--
let `f : ι → sheaf C X`, then the underlying presheaf of categorical product `∏ f` is the product
of `∏ᵢ (f i).presheaf`
-/
def product_sheaf_iso_product_presheaf :
  (∏ f) ≅ ⟨∏ (λ i, (f i).presheaf), Top.limit_is_sheaf _ $ λ ⟨j⟩, (f j).2⟩ :=
let c : cone (discrete.functor f) :=
{ X := ⟨∏ (λ i, (f i).presheaf), Top.limit_is_sheaf _ $ λ ⟨j⟩, (f j).2⟩,
  π := discrete.nat_trans $ λ j, ⟨pi.π _ _⟩ },
is_limit_c : is_limit c :=
{ lift := λ s, ⟨pi.lift $ λ j, (s.π.app ⟨j⟩).1⟩,
  fac' := λ s j,
  begin
    ext,
    simp only [discrete.nat_trans_app, Sheaf.category_theory.category_comp_val, limit.lift_π,
      fan.mk_π_app],
    congr' 3,
    ext,
    refl,
  end,
  uniq' := λ s m h,
  begin
    ext,
    dsimp only,
    simp only [nat_trans.comp_app, limit.lift_π, fan.mk_π_app],
    rw ←h,
    simp only [discrete.nat_trans_app, Sheaf.category_theory.category_comp_val, nat_trans.comp_app],
    congr,
    ext,
    refl,
  end } in
(is_limit.cone_point_unique_up_to_iso (product_is_product f) is_limit_c)

/--
sections of product sheaf is product of sections of sheaves
-/
def section_product_sheaf_equiv_product_section (U : (opens X)ᵒᵖ) :
  (∏ f).presheaf.obj U ≅ ∏ (λ i, (f i).presheaf.obj U) :=
{ hom := (product_sheaf_iso_product_presheaf f).hom.1.app U,
  inv := (product_sheaf_iso_product_presheaf f).inv.1.app U,
  hom_inv_id' :=
  begin
    change ((product_sheaf_iso_product_presheaf f).hom ≫
      (product_sheaf_iso_product_presheaf f).inv).1.app U = _,
    simp only [iso.hom_inv_id, Sheaf.category_theory.category_id_val, nat_trans.id_app],
  end,
  inv_hom_id' :=
  begin
    change ((product_sheaf_iso_product_presheaf f).inv ≫
      (product_sheaf_iso_product_presheaf f).hom).1.app U = _,
    simp only [iso.inv_hom_id, Sheaf.category_theory.category_id_val, nat_trans.id_app],
  end } ≪≫ Top.presheaf.section_product_equiv_product_section _ _

end sheaf
