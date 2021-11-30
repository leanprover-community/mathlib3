/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero

/-!
# Shift

A `shift` on a category is nothing more than an automorphism of the category. An example to
keep in mind might be the category of complexes ⋯ → C_{n-1} → C_n → C_{n+1} → ⋯ with the shift
operator re-indexing the terms, so the degree `n` term of `shift C` would be the degree `n+1`
term of `C`.

-/
namespace category_theory

universes v u

variables (C : Type u) [category.{v} C]

-- TODO: do we want to allow shifts indexed by arbitrary `add_monoid`s?

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift :=
(shift : Π (i : ℤ), C ⥤ C)
(shift_zero : shift 0 ≅ 𝟭 C)
(shift_add : Π i j, shift (i + j) ≅ shift i ⋙ shift j)
(whisker_left_shift_zero : ∀ i, whisker_left (shift i) shift_zero.hom =
  (shift_add i 0).inv ≫ (eq_to_hom $ by simp) ≫ (functor.right_unitor _).inv)
(whisker_right_shift_zero : ∀ i, whisker_right shift_zero.hom (shift i) =
  (shift_add 0 i).inv ≫ (eq_to_hom $ by simp) ≫ (functor.right_unitor _).inv)
(whisker_right_shift_add : ∀ i j k, whisker_right (shift_add i j).hom (shift k) =
  (shift_add (i+j) k).inv ≫ (eq_to_hom $ by rw add_assoc) ≫ (shift_add i (j+k)).hom ≫
    whisker_left _ (shift_add j k).hom ≫ (functor.associator _ _ _).inv)

variables [has_shift C]

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift_functor (i : ℤ) : C ⥤ C := has_shift.shift i

/-- Shifting by zero is the identity functor. -/
def shift_functor_zero : shift_functor C 0 ≅ 𝟭 C := has_shift.shift_zero

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_functor_add (i j : ℤ) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
has_shift.shift_add i j

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
def shift_functor_comp_shift_functor_neg (i : ℤ) :
  shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
(shift_functor_add C i (-i)).symm ≪≫ (eq_to_iso $ by simp) ≪≫ (shift_functor_zero C)

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
def shift_functor_neg_comp_shift_functor (i : ℤ) :
  shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
(shift_functor_add C (-i) i).symm ≪≫ (eq_to_iso $ by simp) ≪≫ (shift_functor_zero C)

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

example {X Y : C} (f : X ⟶ Y) : X⟦1⟧ ⟶ Y⟦1⟧ := f⟦1⟧'
example {X Y : C} (f : X ⟶ Y) : X⟦-2⟧ ⟶ Y⟦-2⟧ := f⟦-2⟧'

variables {C} (X Y : C) (f : X ⟶ Y)

/-- Shifting by zero is the identity functor. -/
def shift_zero : X⟦0⟧ ≅ X := (shift_functor_zero C).app _

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_add (i j : ℤ) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

/-- Shifting by `i` and then by `j` is the same as shifting by `i + j`. -/
abbreviation shift_shift (i j : ℤ) : X⟦i⟧⟦j⟧ ≅ X⟦i + j⟧ := (shift_add X i j).symm

@[simp] lemma shift_add_symm (i j : ℤ) : (shift_add X i j).symm = shift_shift X i j := rfl

@[simp] lemma shift_shift_symm (i j : ℤ) : (shift_shift X i j).symm = shift_add X i j :=
(shift_add X i j).symm_symm_eq

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
def shift_shift_neg (i : ℤ) : X⟦i⟧⟦-i⟧ ≅ X := (shift_functor_comp_shift_functor_neg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
def shift_neg_shift (i : ℤ) : X⟦-i⟧⟦i⟧ ≅ X := (shift_functor_neg_comp_shift_functor C i).app _

lemma shift_shift_zero_hom' (i : ℤ) :
  (shift_zero X).hom⟦i⟧' = (shift_add X 0 i).inv ≫ (eq_to_hom $ by simp) :=
by simpa only [functor.right_unitor_inv_app, eq_to_hom_app, category.comp_id, nat_trans.comp_app]
  using congr_arg (λ α, nat_trans.app α X) (has_shift.whisker_right_shift_zero i)

lemma shift_zero_shift_hom (i : ℤ) :
  (shift_zero $ X⟦i⟧).hom = (shift_add X i 0).inv ≫ (eq_to_hom $ by simp) :=
by simpa only [functor.right_unitor_inv_app, eq_to_hom_app, category.comp_id, nat_trans.comp_app]
  using congr_arg (λ α, nat_trans.app α X) (has_shift.whisker_left_shift_zero i)

lemma shift_shift_add_hom' (i j k : ℤ) :
  (shift_add X i j).hom⟦k⟧' =
    (shift_add X (i+j) k).inv ≫ (eq_to_hom $ by rw add_assoc) ≫ (shift_add X i (j+k)).hom ≫
      (shift_add (X⟦i⟧) j k).hom :=
by simpa only [functor.associator_inv_app, eq_to_hom_app, category.comp_id, nat_trans.comp_app]
  using congr_arg (λ α, nat_trans.app α X) (has_shift.whisker_right_shift_add i j k)

variables {X Y}

lemma shift_zero' : f⟦0⟧' = (shift_zero X).hom ≫ f ≫ (shift_zero Y).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_add' (i j : ℤ) :
  f⟦i + j⟧' = (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' ≫ (shift_add Y i j).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_shift' (i j : ℤ) :
  f⟦i⟧'⟦j⟧' = (shift_shift X i j).hom ≫ f⟦i + j⟧' ≫ (shift_shift Y i j).inv :=
by { symmetry, apply nat_iso.naturality_1 }

lemma shift_shift_neg' (i : ℤ) :
  f⟦i⟧'⟦-i⟧' = (shift_shift_neg X i).hom ≫ f ≫ (shift_shift_neg Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_neg_shift' (i : ℤ) :
  f⟦-i⟧'⟦i⟧' = (shift_neg_shift X i).hom ≫ f ≫ (shift_neg_shift Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

def has_shift_of_equiv {C : Type*} [category C] (S : C ≌ C) : has_shift C :=
{ shift := λ i, (S^i).functor,
  shift_zero := iso.refl _,
  shift_add := λ i j, eq_to_iso $ by {  },
  whisker_left_shift_zero := _,
  whisker_right_shift_zero := _,
  whisker_right_shift_add := _ }


variables (C)

/-- Shifting by `n` is an equivalence, whose inverse is shifting by `-n`. -/
@[simps] def shift_equiv (n : ℤ) : C ≌ C :=
{ functor := shift_functor C n,
  inverse := shift_functor C (-n),
  unit_iso := (shift_functor_comp_shift_functor_neg C n).symm,
  counit_iso := shift_functor_neg_comp_shift_functor C n,
  functor_unit_iso_comp' := λ X,
  begin
    dsimp only [shift_functor_comp_shift_functor_neg, shift_functor_neg_comp_shift_functor],
    simp only [iso.symm_hom, iso.trans_hom, functor.map_comp, nat_trans.comp_app, category.assoc],
    sorry
  end }

open category_theory.limits
variables [has_zero_morphisms C]

@[simp]
lemma shift_zero_eq_zero (X Y : C) (n : ℤ) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
by apply equivalence_preserves_zero_morphisms _ (shift_equiv C n)

end category_theory
