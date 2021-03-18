/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.terminal
import category_theory.adjunction.fully_faithful

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`category_theory.monad.limits`.
-/

universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open limits category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]

/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class reflective (R : D ⥤ C) extends is_right_adjoint R, full R, faithful R.

variables {i : D ⥤ C}

/--
For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
lemma unit_obj_eq_map_unit [reflective i] (X : C) :
  (adjunction.of_right_adjoint i).unit.app (i.obj ((left_adjoint i).obj X))
    = i.map ((left_adjoint i).map ((adjunction.of_right_adjoint i).unit.app X)) :=
begin
 rw [←cancel_mono (i.map ((adjunction.of_right_adjoint i).counit.app ((left_adjoint i).obj X))),
     ←i.map_comp],
 simp,
end

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`functor.ess_image.unit_iso`.
-/
instance is_iso_unit_obj [reflective i] {B : D} :
  is_iso ((adjunction.of_right_adjoint i).unit.app (i.obj B)) :=
begin
  have : (adjunction.of_right_adjoint i).unit.app (i.obj B) =
            inv (i.map ((adjunction.of_right_adjoint i).counit.app B)),
  { rw ← comp_hom_eq_id,
    apply (adjunction.of_right_adjoint i).right_triangle_components },
  rw this,
  exact is_iso.inv_is_iso,
end

/--
If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
lemma functor.ess_image.unit_is_iso [reflective i] {A : C} (h : A ∈ i.ess_image) :
  is_iso ((adjunction.of_right_adjoint i).unit.app A) :=
begin
  suffices : (adjunction.of_right_adjoint i).unit.app A =
                h.get_iso.inv ≫ (adjunction.of_right_adjoint i).unit.app (i.obj h.witness) ≫
                  (left_adjoint i ⋙ i).map h.get_iso.hom,
  { rw this,
    apply_instance },
  rw ← nat_trans.naturality,
  simp,
end

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
lemma mem_ess_image_of_unit_is_iso [is_right_adjoint i] (A : C)
  [is_iso ((adjunction.of_right_adjoint i).unit.app A)] : A ∈ i.ess_image :=
⟨(left_adjoint i).obj A, ⟨(as_iso ((adjunction.of_right_adjoint i).unit.app A)).symm⟩⟩

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
lemma mem_ess_image_of_unit_split_mono [reflective i] {A : C}
  [split_mono ((adjunction.of_right_adjoint i).unit.app A)] : A ∈ i.ess_image :=
begin
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := (adjunction.of_right_adjoint i).unit,
  haveI : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (i.obj_mem_ess_image _).unit_is_iso,
  have : epi (η.app A),
  { apply epi_of_epi (retraction (η.app A)) _,
    rw (show retraction _ ≫ η.app A = _, from η.naturality (retraction (η.app A))),
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A))) },
  resetI,
  haveI := is_iso_of_epi_of_split_mono (η.app A),
  exact mem_ess_image_of_unit_is_iso A,
end

universes v₃ u₃
variables {E : Type u₃} [category.{v₃} E]

/-- Composition of reflective functors. -/
instance reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Fr : reflective F] [Gr : reflective G] :
  reflective (F ⋙ G) := { to_faithful := faithful.comp F G, }

end category_theory
