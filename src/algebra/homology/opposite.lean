/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston
-/

import category_theory.abelian.opposite
import category_theory.abelian.homology
import algebra.homology.additive

/-!
# Opposite categories of complexes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analagous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analagous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `op_symm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/


noncomputable theory

open opposite category_theory category_theory.limits

section

variables {V : Type*} [category V] [abelian V]

lemma image_to_kernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  image_to_kernel g.op f.op (by rw [←op_comp, w, op_zero]) = ((image_subobject_iso _)
  ≪≫ (image_op_op _).symm).hom ≫ (cokernel.desc f (factor_thru_image g)
    (by rw [←cancel_mono (image.ι g), category.assoc, image.fac, w, zero_comp])).op
  ≫ ((kernel_subobject_iso _) ≪≫ (kernel_op_op _)).inv :=
begin
  ext,
  simpa only [iso.trans_hom, iso.symm_hom, iso.trans_inv, kernel_op_op_inv, category.assoc,
    image_to_kernel_arrow, kernel_subobject_arrow', kernel.lift_ι, ←op_comp, cokernel.π_desc,
    ←image_subobject_arrow, ←image_unop_op_inv_comp_op_factor_thru_image g.op],
end

lemma image_to_kernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  image_to_kernel g.unop f.unop (by rw [←unop_comp, w, unop_zero]) = ((image_subobject_iso _)
  ≪≫ (image_unop_unop _).symm).hom ≫ (cokernel.desc f (factor_thru_image g)
    (by rw [←cancel_mono (image.ι g), category.assoc, image.fac, w, zero_comp])).unop
  ≫ ((kernel_subobject_iso _) ≪≫ (kernel_unop_unop _)).inv :=
begin
  ext,
  dunfold image_unop_unop,
  simp only [iso.trans_hom, iso.symm_hom, iso.trans_inv, kernel_unop_unop_inv, category.assoc,
    image_to_kernel_arrow, kernel_subobject_arrow', kernel.lift_ι, cokernel.π_desc,
    iso.unop_inv, ←unop_comp, factor_thru_image_comp_image_unop_op_inv, quiver.hom.unop_op,
    image_subobject_arrow],
end

/-- Given `f, g` with `f ≫ g = 0`, the homology of `g.op, f.op` is the opposite of the homology of
`f, g`. -/
def homology_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
   homology g.op f.op (by rw [←op_comp, w, op_zero]) ≅ opposite.op (homology f g w) :=
cokernel_iso_of_eq (image_to_kernel_op _ _ w) ≪≫ (cokernel_epi_comp _ _)
  ≪≫ cokernel_comp_is_iso _ _ ≪≫ cokernel_op_op _ ≪≫ ((homology_iso_kernel_desc _ _ _)
  ≪≫ (kernel_iso_of_eq (by ext; simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]))
  ≪≫ (kernel_comp_mono _ (image.ι g))).op

/-- Given morphisms `f, g` in `Vᵒᵖ` with `f ≫ g = 0`, the homology of `g.unop, f.unop` is the
opposite of the homology of `f, g`. -/
def homology_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
  homology g.unop f.unop (by rw [←unop_comp, w, unop_zero]) ≅ opposite.unop (homology f g w) :=
cokernel_iso_of_eq (image_to_kernel_unop _ _ w) ≪≫ (cokernel_epi_comp _ _)
  ≪≫ cokernel_comp_is_iso _ _ ≪≫ cokernel_unop_unop _
  ≪≫ ((homology_iso_kernel_desc _ _ _)
  ≪≫ (kernel_iso_of_eq (by ext; simp only [image.fac, cokernel.π_desc, cokernel.π_desc_assoc]))
  ≪≫ (kernel_comp_mono _ (image.ι g))).unop

end

namespace homological_complex

variables {ι V : Type*} [category V] {c : complex_shape ι}

section
variables [preadditive V]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps] protected def op (X : homological_complex V c) : homological_complex Vᵒᵖ c.symm :=
{ X := λ i, op (X.X i),
  d := λ i j, (X.d j i).op,
  shape' := λ i j hij, by { rw [X.shape j i hij, op_zero], },
  d_comp_d' := by { intros, rw [← op_comp, X.d_comp_d, op_zero], } }

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps] protected def op_symm (X : homological_complex V c.symm) : homological_complex Vᵒᵖ c :=
{ X := λ i, op (X.X i),
  d := λ i j, (X.d j i).op,
  shape' := λ i j hij, by { rw [X.shape j i hij, op_zero], },
  d_comp_d' := by { intros, rw [← op_comp, X.d_comp_d, op_zero], } }

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps] protected def unop (X : homological_complex Vᵒᵖ c) : homological_complex V c.symm :=
{ X := λ i, unop (X.X i),
  d := λ i j, (X.d j i).unop,
  shape' := λ i j hij, by { rw [X.shape j i hij, unop_zero], },
  d_comp_d' := by { intros, rw [← unop_comp, X.d_comp_d, unop_zero], } }

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps] protected def unop_symm (X : homological_complex Vᵒᵖ c.symm) : homological_complex V c :=
{ X := λ i, unop (X.X i),
  d := λ i j, (X.d j i).unop,
  shape' := λ i j hij, by { rw [X.shape j i hij, unop_zero], },
  d_comp_d' := by { intros, rw [← unop_comp, X.d_comp_d, unop_zero], } }

variables (V c)

/-- Auxilliary definition for `op_equivalence`. -/
@[simps] def op_functor : (homological_complex V c)ᵒᵖ ⥤ homological_complex Vᵒᵖ c.symm :=
{ obj := λ X, (unop X).op,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).op,
    comm' := λ i j hij, by simp only [op_d, ← op_comp, f.unop.comm] }, }

/-- Auxilliary definition for `op_equivalence`. -/
@[simps] def op_inverse : homological_complex Vᵒᵖ c.symm ⥤ (homological_complex V c)ᵒᵖ :=
{ obj := λ X, op X.unop_symm,
  map := λ X Y f, quiver.hom.op
  { f := λ i, (f.f i).unop,
    comm' := λ i j hij, by simp only [unop_symm_d, ←unop_comp, f.comm], }}

/-- Auxilliary definition for `op_equivalence`. -/
def op_unit_iso : 𝟭 (homological_complex V c)ᵒᵖ ≅ op_functor V c ⋙ op_inverse V c :=
nat_iso.of_components (λ X, (homological_complex.hom.iso_of_components (λ i, iso.refl _)
  (λ i j hij, by simp only [iso.refl_hom, category.id_comp, unop_symm_d, op_d, quiver.hom.unop_op,
        category.comp_id]) : (opposite.unop X).op.unop_symm ≅ unop X).op)
  begin
    intros X Y f,
    refine quiver.hom.unop_inj _,
    ext,
    simp only [quiver.hom.unop_op, functor.id_map, iso.op_hom, functor.comp_map,
      unop_comp, comp_f, hom.iso_of_components_hom_f],
    erw [category.id_comp, category.comp_id (f.unop.f x)],
  end

/-- Auxilliary definition for `op_equivalence`. -/
def op_counit_iso : op_inverse V c ⋙ op_functor V c ≅ 𝟭 (homological_complex Vᵒᵖ c.symm) :=
nat_iso.of_components (λ X, homological_complex.hom.iso_of_components (λ i, iso.refl _)
  (λ i j hij, by simpa only [iso.refl_hom, category.id_comp, category.comp_id]))
  begin
    intros X Y f,
    ext,
    simpa only [quiver.hom.unop_op, quiver.hom.op_unop, functor.comp_map, functor.id_map,
      iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f],
  end

/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps] def op_equivalence : (homological_complex V c)ᵒᵖ ≌ homological_complex Vᵒᵖ c.symm :=
{ functor := op_functor V c,
  inverse := op_inverse V c,
  unit_iso := op_unit_iso V c,
  counit_iso := op_counit_iso V c,
  functor_unit_iso_comp' :=
  begin
    intro X,
    ext,
    simp only [op_unit_iso, op_counit_iso, nat_iso.of_components_hom_app, iso.op_hom,
      comp_f, op_functor_map_f, quiver.hom.unop_op, hom.iso_of_components_hom_f],
    exact category.comp_id _,
  end }

/-- Auxilliary definition for `unop_equivalence`. -/
@[simps] def unop_functor : (homological_complex Vᵒᵖ c)ᵒᵖ ⥤ homological_complex V c.symm :=
{ obj := λ X, (unop X).unop,
  map := λ X Y f,
  { f := λ i, (f.unop.f i).unop,
    comm' := λ i j hij, by simp only [unop_d, ← unop_comp, f.unop.comm] }, }

/-- Auxilliary definition for `unop_equivalence`. -/
@[simps] def unop_inverse : homological_complex V c.symm ⥤ (homological_complex Vᵒᵖ c)ᵒᵖ :=
{ obj := λ X, op X.op_symm,
  map := λ X Y f, quiver.hom.op
  { f := λ i, (f.f i).op,
    comm' := λ i j hij, by simp only [op_symm_d, ←op_comp, f.comm], }}

/-- Auxilliary definition for `unop_equivalence`. -/
def unop_unit_iso : 𝟭 (homological_complex Vᵒᵖ c)ᵒᵖ ≅ unop_functor V c ⋙ unop_inverse V c :=
nat_iso.of_components (λ X, (homological_complex.hom.iso_of_components (λ i, iso.refl _)
  (λ i j hij, by simp only [iso.refl_hom, category.id_comp, unop_symm_d, op_d, quiver.hom.unop_op,
        category.comp_id]) : (opposite.unop X).op.unop_symm ≅ unop X).op)
  begin
    intros X Y f,
    refine quiver.hom.unop_inj _,
    ext,
    simp only [quiver.hom.unop_op, functor.id_map, iso.op_hom, functor.comp_map,
      unop_comp, comp_f, hom.iso_of_components_hom_f],
    erw [category.id_comp, category.comp_id (f.unop.f x)],
  end

/-- Auxilliary definition for `unop_equivalence`. -/
def unop_counit_iso : unop_inverse V c ⋙ unop_functor V c ≅ 𝟭 (homological_complex V c.symm) :=
nat_iso.of_components (λ X, homological_complex.hom.iso_of_components (λ i, iso.refl _)
  (λ i j hij, by simpa only [iso.refl_hom, category.id_comp, category.comp_id]))
  begin
    intros X Y f,
    ext,
    simpa only [quiver.hom.unop_op, quiver.hom.op_unop, functor.comp_map, functor.id_map,
      iso.refl_hom, category.id_comp, category.comp_id, comp_f, hom.iso_of_components_hom_f],
  end

/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps] def unop_equivalence : (homological_complex Vᵒᵖ c)ᵒᵖ ≌ homological_complex V c.symm :=
{ functor := unop_functor V c,
  inverse := unop_inverse V c,
  unit_iso := unop_unit_iso V c,
  counit_iso := unop_counit_iso V c,
  functor_unit_iso_comp' :=
  begin
    intro X,
    ext,
    simp only [op_unit_iso, op_counit_iso, nat_iso.of_components_hom_app, iso.op_hom,
      comp_f, op_functor_map_f, quiver.hom.unop_op, hom.iso_of_components_hom_f],
    exact category.comp_id _,
  end }

variables {V c}
instance op_functor_additive : (@op_functor ι V _ c _).additive := {}

instance unop_functor_additive : (@unop_functor ι V _ c _).additive := {}

end

variables [abelian V] (C : homological_complex V c) (i : ι)

/-- Auxilliary tautological definition for `homology_op`. -/
def homology_op_def :
  C.op.homology i ≅ _root_.homology (C.d_from i).op (C.d_to i).op
    (by rw [←op_comp, C.d_to_comp_d_from i, op_zero]) := iso.refl _

/-- Given a complex `C` of objects in `V`, the `i`th homology of its 'opposite' complex (with
objects in `Vᵒᵖ`) is the opposite of the `i`th homology of `C`. -/
def homology_op : C.op.homology i ≅ opposite.op (C.homology i) :=
homology_op_def _ _ ≪≫ homology_op _ _ _

/-- Auxilliary tautological definition for `homology_unop`. -/
def homology_unop_def (C : homological_complex Vᵒᵖ c) :
  C.unop.homology i ≅ _root_.homology (C.d_from i).unop (C.d_to i).unop
    (by rw [←unop_comp, C.d_to_comp_d_from i, unop_zero]) := iso.refl _

/-- Given a complex `C` of objects in `Vᵒᵖ`, the `i`th homology of its 'opposite' complex (with
objects in `V`) is the opposite of the `i`th homology of `C`. -/
def homology_unop (C : homological_complex Vᵒᵖ c) :
  C.unop.homology i ≅ opposite.unop (C.homology i) :=
homology_unop_def _ _ ≪≫ homology_unop _ _ _

end homological_complex
