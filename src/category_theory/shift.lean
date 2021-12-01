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

variables (C : Type u) (A : Type*) [category.{v} C]

section defs

variables [add_monoid A]

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift (C : Type u) (A : out_param $ Type*) [category.{v} C] [add_monoid A] :=
(shift : Π (i : A), C ⥤ C)
(shift_add : Π i j, shift (i + j) ≅ shift i ⋙ shift j)
(iso_whisker_right_shift_add : ∀ i j k, iso_whisker_right (shift_add i j) (shift k) =
  (shift_add (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫ (shift_add i (j+k)) ≪≫
    iso_whisker_left _ (shift_add j k) ≪≫ (functor.associator _ _ _).symm)

variables [has_shift C A] {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift_functor (i : A) : C ⥤ C := has_shift.shift i

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_functor_add (i j : A) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
has_shift.shift_add i j

lemma iso_whisker_right_shift_functor_add (i j k : A) :
  iso_whisker_right (shift_functor_add C i j) (shift_functor C k) =
  (shift_functor_add C (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫
    (shift_functor_add C i (j+k)) ≪≫
    iso_whisker_left _ (shift_functor_add C j k) ≪≫ (functor.associator _ _ _).symm :=
has_shift.iso_whisker_right_shift_add i j k

variables (A)

/-- Shifting by zero is the identity functor. -/
def shift_functor_zero [is_equivalence (shift_functor C (0:A))] :
  shift_functor C (0 : A) ≅ 𝟭 C :=
(functor.right_unitor _).symm ≪≫
  iso_whisker_left (shift_functor _ _) is_equivalence.unit_iso ≪≫
  (iso_whisker_right (eq_to_iso (by rw add_zero) ≪≫ (shift_functor_add C (0:A) 0))
    (shift_functor C (0 : A)).inv ≪≫
  (functor.associator _ _ _)).symm ≪≫
  is_equivalence.unit_iso.symm

end defs

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

section examples
variables [has_shift C ℤ]

example {X Y : C} (f : X ⟶ Y) : X⟦(1 : ℤ)⟧ ⟶ Y⟦1⟧ := f⟦1⟧'
example {X Y : C} (f : X ⟶ Y) : X⟦(-2 : ℤ)⟧ ⟶ Y⟦-2⟧ := f⟦-2⟧'

end examples

section add_monoid

variables {C A} [add_monoid A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

/-- Shifting by `i` and then by `j` is the same as shifting by `i + j`. -/
abbreviation shift_shift (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦i + j⟧ := (shift_add X i j).symm

@[simp] lemma shift_add_symm (i j : A) : (shift_add X i j).symm = shift_shift X i j := rfl

@[simp] lemma shift_shift_symm (i j : A) : (shift_shift X i j).symm = shift_add X i j :=
(shift_add X i j).symm_symm_eq

lemma shift_add' (i j : A) :
  f⟦i + j⟧' = (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' ≫ (shift_add Y i j).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_shift' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_shift X i j).hom ≫ f⟦i + j⟧' ≫ (shift_shift Y i j).inv :=
by { symmetry, apply nat_iso.naturality_1 }

lemma shift_shift_add_hom' (i j k : A) :
  (shift_add X i j).hom⟦k⟧' =
    (shift_add X (i+j) k).inv ≫ (eq_to_hom $ by rw add_assoc) ≫ (shift_add X i (j+k)).hom ≫
      (shift_add (X⟦i⟧) j k).hom :=
begin
  have := congr_arg iso.hom (iso_whisker_right_shift_functor_add C i j k),
  apply_fun (λ α, nat_trans.app α X) at this,
  simpa only [iso_whisker_left_hom, iso_whisker_right_hom, iso.symm_hom, functor.associator_inv_app,
    eq_to_hom_app, whisker_right_app, whisker_left_app, eq_to_iso.hom, category.comp_id,
    iso.trans_hom, nat_trans.comp_app] using this,
end

lemma shift_functor_map_iso_shift_add (i j k : A) :
  (shift_functor C k).map_iso (shift_add X i j) =
    (shift_add X (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫ (shift_add X i (j+k)) ≪≫
      (shift_add (X⟦i⟧) j k) :=
by { ext, apply shift_shift_add_hom', }

lemma shift_add_assoc (i j k : A) :
  shift_add X (i + j) k =
    eq_to_iso (by rw add_assoc) ≪≫ shift_add X i (j + k) ≪≫
    shift_add _ j k ≪≫ (functor.map_iso _ (shift_add X i j)).symm :=
begin
  ext,
  simp only [iso.symm_hom, eq_to_iso.hom, iso.trans_hom, ← category.assoc],
  rw [iso.eq_comp_inv, ← iso.eq_inv_comp, functor.map_iso_hom, shift_shift_add_hom',
    category.assoc],
end

/-- Shifting by zero is the identity functor. -/
def shift_zero [is_equivalence (shift_functor C (0:A))] :
  X⟦0⟧ ≅ X := (shift_functor_zero C A).app _

lemma shift_zero' [is_equivalence (shift_functor C (0:A))] :
  f⟦(0 : A)⟧' = (shift_zero X).hom ≫ f ≫ (shift_zero Y).inv :=
by { symmetry, apply nat_iso.naturality_2 }

end add_monoid

section add_group

variables {A} [add_group A] [has_shift C A] [is_equivalence (shift_functor C (0 : A))]
variables (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
def shift_functor_comp_shift_functor_neg (i : A) :
  shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
(shift_functor_add C i (-i)).symm ≪≫ (eq_to_iso $ by simp) ≪≫ (shift_functor_zero C A)

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
def shift_functor_neg_comp_shift_functor (i : A) :
  shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
(shift_functor_add C (-i) i).symm ≪≫ (eq_to_iso $ by simp) ≪≫ (shift_functor_zero C A)

instance shift_functor_faithful (i : A) : faithful (shift_functor C i) :=
faithful.of_comp_iso (shift_functor_comp_shift_functor_neg C i)

instance shift_functor_full (i : A) : full (shift_functor C i) :=
begin
  haveI : full (shift_functor C i ⋙ shift_functor C (-i)) :=
    full.of_iso (shift_functor_comp_shift_functor_neg C i).symm,
  exact full.of_comp_faithful _ (shift_functor C (-i))
end

instance shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) :=
{ mem_ess_image := λ Y, ⟨Y⟦-i⟧, ⟨(shift_functor_neg_comp_shift_functor C i).app Y⟩⟩ }

variables {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
def shift_shift_neg (i : A) : X⟦i⟧⟦-i⟧ ≅ X := (shift_functor_comp_shift_functor_neg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
def shift_neg_shift (i : A) : X⟦-i⟧⟦i⟧ ≅ X := (shift_functor_neg_comp_shift_functor C i).app _

variables {X Y}

lemma shift_shift_neg' (i : A) :
  f⟦i⟧'⟦-i⟧' = (shift_shift_neg X i).hom ≫ f ≫ (shift_shift_neg Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_neg_shift' (i : A) :
  f⟦-i⟧'⟦i⟧' = (shift_neg_shift X i).hom ≫ f ≫ (shift_neg_shift Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

variables (C)

/-- Shifting by `n` is an equivalence, whose inverse is shifting by `-n`. -/
noncomputable instance (n : A) : is_equivalence (shift_functor C n) :=
equivalence.of_fully_faithfully_ess_surj _

open category_theory.limits
variables [has_zero_morphisms C]

@[simp]
lemma shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
by apply is_equivalence_preserves_zero_morphisms _ (shift_functor C n)

end add_group

end category_theory
