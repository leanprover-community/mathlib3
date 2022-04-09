/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.shift.basic

/-!
# Functors between categories with shifts.

A `shift_structure` on a functor `F : C ⥤ D` between categories with shifts
consists not just of isomorphisms `shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a`,
but also some axioms relating these via the monoid structure on `A`.
-/

namespace category_theory

variables {C D : Type*} [category C] [category D]
variables (A : Type*) [add_monoid A] [has_shift C A] [has_shift D A]

/-- A weak shift structure on a functor `F : C ⥤ D` between categories with shifts by `A`
is a family of isomorphisms `shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a`
but without the compabitilities relating these to the monoid structure on `A`. -/
class weak_shift_structure (F : C ⥤ D) :=
(comm : Π (a : A), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)

/-- A shift structure on a functor `F : C ⥤ D` between categories with shifts by `A`
is a family of isomorphisms `shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a` satisfying
appropriate compatibilities with the monoid structure on `A`. -/
class shift_structure (F : C ⥤ D) extends weak_shift_structure A F :=
(zero [] : comm 0 = iso_whisker_right (shift_functor_zero C A) F ≪≫ F.left_unitor ≪≫
  F.right_unitor.symm ≪≫ iso_whisker_left F (shift_functor_zero D A).symm . obviously)
(add [] : ∀ a b, comm (a + b) = (calc
  shift_functor C (a + b) ⋙ F ≅ (shift_functor C a ⋙ shift_functor C b) ⋙ F :
    iso_whisker_right (shift_functor_add C a b) F
  ... ≅ shift_functor C a ⋙ (shift_functor C b ⋙ F) : functor.associator _ _ _
  ... ≅ shift_functor C a ⋙ (F ⋙ shift_functor D b) : iso_whisker_left _ (comm b)
  ... ≅ (shift_functor C a ⋙ F) ⋙ shift_functor D b : (functor.associator _ _ _).symm
  ... ≅ (F ⋙ shift_functor D a) ⋙ shift_functor D b : iso_whisker_right (comm a) _
  ... ≅ F ⋙ shift_functor D a ⋙ shift_functor D b : functor.associator _ _ _
  ... ≅ F ⋙ shift_functor D (a + b) : iso_whisker_left _ (shift_functor_add D a b).symm)
   . obviously)

namespace functor

variables {A}

/-- A functor with a shift structure commutes with the shift functors. -/
def comm_shift (F : C ⥤ D) [weak_shift_structure A F] (a : A) :
  shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a :=
weak_shift_structure.comm a

end functor

namespace weak_shift_structure

instance : inhabited (weak_shift_structure A (𝟭 C)) :=
⟨{ comm := λ a, functor.right_unitor _ ≪≫ (functor.left_unitor _).symm, }⟩

instance comp {E : Type*} [category E] [has_shift E A]
  (F : C ⥤ D) [weak_shift_structure A F] (G : D ⥤ E) [weak_shift_structure A G] :
  weak_shift_structure A (F ⋙ G) :=
{ comm := λ a, (calc
    shift_functor C a ⋙ (F ⋙ G) ≅ (shift_functor C a ⋙ F) ⋙ G : (functor.associator _ _ _).symm
    ... ≅ (F ⋙ shift_functor D a) ⋙ G : iso_whisker_right (F.comm_shift a) _
    ... ≅ F ⋙ (shift_functor D a ⋙ G) : functor.associator _ _ _
    ... ≅ F ⋙ (G ⋙ shift_functor E a) : iso_whisker_left _ (G.comm_shift a)
    ... ≅ (F ⋙ G) ⋙ shift_functor E a : (functor.associator _ _ _).symm), }

variables {E : Type*} [category E] [has_shift E A]
  (F : C ⥤ D) [weak_shift_structure A F] (G : D ⥤ E) [weak_shift_structure A G]

@[simp] lemma comp_comm_shift_hom_app (a : A) (X : C) :
  ((F ⋙ G).comm_shift a).hom.app X =
    G.map ((F.comm_shift a).hom.app X) ≫ (G.comm_shift a).hom.app (F.obj X) :=
begin
  dsimp [weak_shift_structure.comp, functor.comm_shift],
  simp,
end

@[simp] lemma comp_comm_shift_inv_app (a : A) (X : C) :
  ((F ⋙ G).comm_shift a).inv.app X =
    (G.comm_shift a).inv.app (F.obj X) ≫ G.map ((F.comm_shift a).inv.app X) :=
begin
  dsimp [weak_shift_structure.comp, functor.comm_shift],
  simp,
end

@[simp] lemma comp_comm_shift_app (a : A) (X : C) :
  ((F ⋙ G).comm_shift a).app X =
    G.map_iso ((F.comm_shift a).app X) ≪≫ (G.comm_shift a).app (F.obj X) :=
by { ext, dsimp, simp, }

end weak_shift_structure

namespace shift_structure

instance id : shift_structure A (𝟭 C) :=
{ comm := λ a, functor.right_unitor _ ≪≫ (functor.left_unitor _).symm, }

@[simp] lemma id_comm_shift_hom_app (a : A) (X : C) :
  ((𝟭 C).comm_shift a).hom.app X = 𝟙 ((shift_functor C a).obj X) :=
category.comp_id _
@[simp] lemma id_comm_shift_inv_app (a : A) (X : C) :
  ((𝟭 C).comm_shift a).inv.app X = 𝟙 ((shift_functor C a).obj X) :=
category.comp_id _
@[simp] lemma id_comm_shift_app (a : A) (X : C) :
  ((𝟭 C).comm_shift a).app X = iso.refl ((shift_functor C a).obj X) :=
by { ext, dsimp, simp, }

instance : inhabited (shift_structure A (𝟭 C)) := ⟨shift_structure.id A⟩

instance comp {E : Type*} [category E] [has_shift E A]
  (F : C ⥤ D) [shift_structure A F] (G : D ⥤ E) [shift_structure A G] :
  shift_structure A (F ⋙ G) :=
{ zero := begin
    dsimp [weak_shift_structure.comp],
    have := shift_structure.zero A F, change F.comm_shift _ = _ at this, rw this, clear this,
    have := shift_structure.zero A G, change G.comm_shift _ = _ at this, rw this, clear this,
    ext,
    dsimp,
    simp only [category.comp_id, category.id_comp, category.assoc, ←G.map_comp_assoc,
      ε_hom_inv_app],
    erw [category.comp_id],
  end,
  add := λ a b, begin
    dsimp [weak_shift_structure.comp],
    have := shift_structure.add A F a b, change F.comm_shift _ = _ at this, rw this, clear this,
    have := shift_structure.add A G a b, change G.comm_shift _ = _ at this, rw this, clear this,
    ext,
    dsimp,
    simp only [category.comp_id, category.id_comp, category.assoc, G.map_comp],
    congr' 2,
    slice_lhs 2 3 { simp only [←G.map_comp, μ_hom_inv_app], erw [G.map_id], },
    simp only [category.id_comp, category.assoc],
    have := (G.comm_shift b).hom.naturality_assoc, dsimp at this, erw [this], clear this,
    congr' 1,
    simp only [←(shift_functor E b).map_comp_assoc],
    refl,
  end, }

end shift_structure

end category_theory
