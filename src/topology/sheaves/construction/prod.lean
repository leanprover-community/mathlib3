import topology.sheaves.limits
import category_theory.limits.functor_category

noncomputable theory

open category_theory category_theory.limits Top topological_space

universes u v w u'

namespace presheaf

variables {X : Top.{u}} {C : Type v} [category.{w} C]
variables {ι : Type u'} (f : ι → presheaf C X) [has_products.{u'} C]

instance : has_products.{u'} (presheaf C X) :=
λ J, category_theory.limits.functor_category_has_limits_of_shape

def section_product_equiv_product_section
  (U : (opens X)ᵒᵖ) : (∏ f).obj U ≅ ∏ (λ x, (f x).obj U) :=
limit_obj_iso_limit_comp_evaluation _ _ ≪≫ limits.lim.map_iso (discrete.nat_iso $ λ X, iso.refl _)

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

end presheaf
