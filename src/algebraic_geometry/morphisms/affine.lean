/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.ring_hom_properties
import algebraic_geometry.morphisms.quasi_compact
import ring_theory.ring_hom.finite_type

/-!

# Affine morphisms

A morphism of schemes is affine if the preimages of affine open sets are affine.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is `affine` if the preimages of affine open sets are affine. -/
@[mk_iff]
class affine (f : X ⟶ Y) : Prop :=
(is_affine_preimage : ∀ U : opens Y.carrier,
  is_affine_open U → is_affine_open ((opens.map f.1.base).obj U))

/-- The `affine_target_morphism_property` corresponding to affine morphisms. -/
def affine.affine_property : affine_target_morphism_property :=
λ X Y f hf, is_affine X

@[simp] lemma affine_affine_property_to_property {X Y : Scheme} (f : X ⟶ Y) :
  affine_target_morphism_property.to_property affine.affine_property f ↔
    is_affine Y ∧ is_affine X :=
by { delta affine_target_morphism_property.to_property affine.affine_property, simp }

@[priority 900]
instance affine_of_is_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] : affine f :=
⟨λ U hU, hU.map_is_iso f⟩

instance affine_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [affine f] [affine g] : affine (f ≫ g) :=
begin
  constructor,
  intros U hU,
  rw [Scheme.comp_val_base, opens.map_comp_obj],
  apply affine.is_affine_preimage,
  apply affine.is_affine_preimage,
  exact hU
end

lemma affine_iff_affine_property :
  affine f ↔ target_affine_locally affine.affine_property f :=
(affine_iff f).trans ⟨λ H U, H U U.prop, λ H U hU, H ⟨U, hU⟩⟩

lemma affine_eq_affine_property :
  @affine = target_affine_locally affine.affine_property :=
by { ext, exact affine_iff_affine_property _ }

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
  affine (X.of_restrict (X.basic_open r).open_embedding) :=
begin
  constructor,
  intros U hU,
  fapply (is_affine_open_iff_of_is_open_immersion (X.of_restrict _) _).mp,
  swap,
  { apply_instance },
  convert hU.basic_open_is_affine (X.presheaf.map (hom_of_le le_top).op r),
  rw X.basic_open_res,
  ext1,
  refine set.image_preimage_eq_inter_range.trans _,
  erw subtype.range_coe,
  refl
end

/-- The preimage of an affine open as an `Scheme.affine_opens`. -/
@[simps]
def affine_preimage {X Y : Scheme} (f : X ⟶ Y) [affine f] (U : Y.affine_opens) :
  X.affine_opens :=
⟨(opens.map f.1.base).obj (U : opens Y.carrier), affine.is_affine_preimage _ U.prop⟩

lemma affine_affine_property_stable_under_base_change :
  affine_target_morphism_property.stable_under_base_change affine.affine_property :=
begin
  introv X H,
  delta affine.affine_property at H ⊢,
  resetI,
  apply_instance
end

end algebraic_geometry
