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
class has_shift (C : Type u) (A : Type*) [category.{v} C] [add_monoid A] :=
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

@[simp] lemma has_shift.shift_app (n : A) (X : C) : (has_shift.shift n).obj X = X⟦n⟧ := rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

@[simp] lemma has_shift.shift_add_app (i j : A) :
  (has_shift.shift_add i j).app X = shift_add X i j := rfl

@[simp] lemma shift_functor_add_app (i j : A) :
  (shift_functor_add C i j).app X = shift_add X i j := rfl

lemma shift_add' (i j : A) :
  f⟦i + j⟧' = (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' ≫ (shift_add Y i j).inv :=
by { symmetry, apply nat_iso.naturality_2 }

@[reassoc] lemma shift_add_hom_comp (i j : A) :
  (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' = f⟦i + j⟧' ≫ (shift_add Y i j).hom :=
by rw [shift_add', category.assoc, category.assoc, iso.inv_hom_id, category.comp_id]

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

lemma shift_shift_add_inv' (i j k : A) :
  (shift_add X i j).inv⟦k⟧' =
    (shift_add (X⟦i⟧) j k).inv ≫ (shift_add X i (j+k)).inv ≫ (eq_to_hom $ by rw add_assoc) ≫
      (shift_add X (i+j) k).hom :=
begin
  have := congr_arg iso.inv (iso_whisker_right_shift_functor_add C i j k),
  apply_fun (λ α, nat_trans.app α X) at this,
  simpa only [iso_whisker_right_inv, whisker_right_app, functor.associator_hom_app, iso.trans_inv, eq_to_iso.inv, eq_to_hom_app,
    whisker_left_app, iso.symm_inv, category.id_comp, iso_whisker_left_inv, nat_trans.comp_app,
    category.assoc] using this,
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

@[simp, reassoc] lemma shift_add_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i' j).hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc] lemma shift_add_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i j').hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc] lemma shift_add_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw [h₁, h₂]) =
    eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').hom :=
by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc] lemma eq_to_hom_comp_shift_add_inv₁ (i i' j : A) (h : i = i') :
  eq_to_hom (by rw h) ≫ (shift_add X i' j).inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]

@[simp, reassoc] lemma eq_to_hom_comp_shift_add_inv₂ (i j j' : A) (h : j = j') :
  eq_to_hom (by rw h) ≫ (shift_add X i j').inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]

@[simp, reassoc] lemma eq_to_hom_comp_shift_add_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').inv =
    (shift_add X i j).inv ≫ eq_to_hom (by rw [h₁, h₂]) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]

lemma shift_shift' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_add X i j).inv ≫ f⟦i + j⟧' ≫ (shift_add Y i j).hom :=
by { symmetry, apply nat_iso.naturality_1 }

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

section

variables (C)

/-- Shifting by `n` is a faithful functor. -/
lemma shift_functor_faithful (i : A) : faithful (shift_functor C i) :=
faithful.of_comp_iso (shift_functor_comp_shift_functor_neg C i)

local attribute [instance] shift_functor_faithful

/-- Shifting by `n` is a full functor. -/
def shift_functor_full (i : A) : full (shift_functor C i) :=
begin
  haveI : full (shift_functor C i ⋙ shift_functor C (-i)) :=
    full.of_iso (shift_functor_comp_shift_functor_neg C i).symm,
  exact full.of_comp_faithful _ (shift_functor C (-i))
end

/-- Shifting by `n` is an essentially surjective functor. -/
lemma shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) :=
{ mem_ess_image := λ Y, ⟨Y⟦-i⟧, ⟨(shift_functor_neg_comp_shift_functor C i).app Y⟩⟩ }

local attribute [instance] shift_functor_full shift_functor_ess_surj

/-- Shifting by `n` is an equivalence. -/
noncomputable def shift_functor_is_equivalence (n : A) : is_equivalence (shift_functor C n) :=
equivalence.of_fully_faithfully_ess_surj _

end

-- Unfortunately it is dangerous to make this a global instance,
-- because it creates a loop for `shift_functor C 0`.
local attribute [instance] shift_functor_is_equivalence

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

open category_theory.limits
variables [has_zero_morphisms C]

@[simp]
lemma shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
by apply is_equivalence_preserves_zero_morphisms _ (shift_functor C n)

end add_group

section add_comm_monoid

variables {C A} [add_comm_monoid A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shift_comm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
(shift_add X i j).symm ≪≫ eq_to_iso (by rw add_comm) ≪≫ shift_add X j i

@[simp] lemma shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i :=
begin
  ext, dsimp [shift_comm],
  simp only [iso.hom_inv_id_assoc, category.id_comp, eq_to_hom_refl,
    eq_to_hom_trans_assoc, iso.inv_hom_id, category.assoc],
end

variables {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
lemma shift_comm' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).hom :=
begin
  rw [shift_shift', shift_shift'],
  dsimp [shift_comm],
  simp only [← category.assoc, cancel_mono],
  simp only [iso.hom_inv_id_assoc, iso.cancel_iso_inv_left, category.assoc],
  generalize_proofs h1 h2, revert h1 h2,
  generalize hij : i + j = ij, generalize hji : j + i = ji, intros h1 h2,
  obtain rfl : ij = ji, { rw [← hij, add_comm, hji] }, clear hij hji,
  rw [eq_to_hom_refl, eq_to_hom_refl, category.comp_id, category.id_comp],
end

@[reassoc] lemma shift_comm_hom_comp (i j : A) :
  (shift_comm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).hom :=
by rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end add_comm_monoid

end category_theory
