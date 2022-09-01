-- import all

import category_theory.abelian.functor_category
import category_theory.abelian.transfer
import category_theory.sites.left_exact

namespace category_theory

open category_theory.limits

section abelian

variables {C : Type} [category.{0} C] {J : grothendieck_topology C}
variables {D : Type} [category.{0} D]
variables [abelian D] [has_finite_limits D] [concrete_category.{0} D]
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
variables [preserves_limits (forget D)]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

-- variables {C' : Type u} [category.{u} C'] {J' : grothendieck_topology C'}
-- variables {D' : Type u} [category.{u} D'] [abelian D'] [has_finite_products D']
-- set_option pp.all true
noncomputable instance : abelian (Sheaf J D) :=
begin
  haveI : abelian (Cᵒᵖ ⥤ D) := @abelian.functor_category_abelian.{0 0 0 0} Cᵒᵖ _ D _ _,
  haveI i2 : has_finite_products (Sheaf J D),
  { refine ⟨λ j fj, _⟩, resetI,
    haveI i2 : has_limits_of_shape (discrete j) (Cᵒᵖ ⥤ D),
    { exact @has_finite_products.out _ _ _ j fj },
    haveI i3 : creates_limits_of_shape (discrete j) (Sheaf_to_presheaf J D),
    { refine ⟨λ k, _⟩,
      exactI @Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limit.{0 0} C _ J D _
        (discrete j) _ (@has_finite_products.out _ _ _ j fj) k, },
    exact has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (Sheaf_to_presheaf J D) },
  have i3 : (Sheaf_to_presheaf J D).preserves_zero_morphisms,
  { refine ⟨λ P Q, _⟩, ext, dsimp, change (0 : P.1 ⟶ Q.1).app _ = _, simp only [nat_trans.app_zero], },
  have i4 : (presheaf_to_Sheaf J D).preserves_zero_morphisms,
  { refine ⟨λ P Q, _⟩, ext, dsimp,
    have : J.sheafify_map (0 : P ⟶ Q) = 0,
    { dunfold grothendieck_topology.sheafify_map grothendieck_topology.plus_map,
      ext1, ext1 γ, dsimp,
      apply colimit.hom_ext, intros j,
      erw [comp_zero, colimit.ι_map], dsimp,
      convert_to 0 ≫ colimit.ι _ j = 0,
      { congr, convert_to (J.diagram_nat_trans 0 γ.unop).app _ = 0,
        { congr, ext x' j', erw [colimit.ι_map, comp_zero],
          convert zero_comp, dsimp [grothendieck_topology.diagram_nat_trans],
          simp_rw [comp_zero], ext1, erw [limits.multiequalizer.lift_ι, zero_comp], },
        dsimp [grothendieck_topology.diagram_nat_trans], simp_rw [comp_zero],
        ext1, erw [limits.multiequalizer.lift_ι, zero_comp], },
      rw zero_comp, },
    rw this, clear this, refl },
  refine @abelian_of_adjunction (Sheaf J D) _ _ _ (Cᵒᵖ ⥤ D) _ _ (Sheaf_to_presheaf J D) sorry -- this should just be i3?
    (presheaf_to_Sheaf J D) sorry -- should just be i4
    _ _ _,
  { haveI : is_iso ((sheafification_adjunction J D).counit) := category_theory.sheafification_reflective,
    -- exact as_iso (sheafification_adjunction J D).counit,
    refine { hom := (sheafification_adjunction J D).counit,
      inv := inv (sheafification_adjunction J D).counit,
      hom_inv_id' := _,
      inv_hom_id' := _ },
    { simp only [is_iso.hom_inv_id], },
    { simp only [is_iso.inv_hom_id], }, },
  exact sheafification_adjunction J D,
end

end abelian

end category_theory
