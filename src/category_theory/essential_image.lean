/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.natural_isomorphism

/-!
# Essential image of a functor

The essential image of a functor consists of the objects in the target category which are isomorphic
to an object in the image of the object function.
-/
universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {F : C ⥤ D}

namespace functor

/--
The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def ess_image (F : C ⥤ D) : set D := λ Y, ∃ (X : C), nonempty (F.obj X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def ess_image.witness {Y : D} (h : Y ∈ F.ess_image) : C := h.some

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def ess_image.get_iso {Y : D} (h : Y ∈ F.ess_image) : F.obj h.witness ≅ Y :=
classical.choice h.some_spec

/-- Being in the subcategory is a "hygenic" property: it is preserved under isomorphism. -/
lemma ess_image.of_iso {Y Y' : D} (h : Y ≅ Y') (hY : Y ∈ ess_image F) :
  Y' ∈ ess_image F :=
hY.imp (λ B, nonempty.map (≪≫ h))

/--
If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
lemma ess_image.of_nat_iso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ ess_image F) :
  Y ∈ ess_image F' :=
hY.imp (λ X, nonempty.map (λ t, h.symm.app X ≪≫ t))

/-- Isomorphic functors have equal essential images. -/
lemma image_eq_of_nat_iso {F' : C ⥤ D} (h : F ≅ F') :
  ess_image F = ess_image F' :=
begin
  ext A,
  split,
  { apply ess_image.of_nat_iso h },
  { apply ess_image.of_nat_iso h.symm },
end

lemma obj_mem_ess_image (F : D ⥤ C) (Y : D) : F.obj Y ∈ ess_image F := ⟨Y, ⟨iso.refl _⟩⟩

end functor

/--
A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class ess_surj (F : C ⥤ D) : Prop :=
(mem_ess_image [] (Y : D) : Y ∈ F.ess_image)

variables (F) [ess_surj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
def functor.obj_preimage (Y : D) : C := (ess_surj.mem_ess_image F Y).witness
/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
    isomorphic to `Y`. -/
def functor.obj_obj_preimage_iso (Y : D) : F.obj (F.obj_preimage Y) ≅ Y :=
(ess_surj.mem_ess_image F Y).get_iso

end category_theory
