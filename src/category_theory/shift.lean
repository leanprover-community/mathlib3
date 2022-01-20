/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang
-/
import category_theory.limits.shapes.zero
import category_theory.monoidal.End
import category_theory.monoidal.discrete

/-!
# Shift

A `shift` on a category `C` indexed by a monoid `A` is is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexing the terms, so the degree `i` term of `shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `has_shift`: A typeclass asserting the existence of a shift functor.
* `shift_equiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shift_comm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

Most of the definitions in this file is marked as an `abbreviation` so that the simp lemmas in
`category_theory/monoidal/End` could apply.

-/
namespace category_theory

noncomputable theory

universes v u

variables (C : Type u) (A : Type*) [category.{v} C]

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

section eq_to_hom

variables {A C}

variables [add_monoid A] (F : monoidal_functor (discrete A) (C ⥤ C))

 @[simp, reassoc] lemma eq_to_hom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
   eq_to_hom (by rw [h₁, h₂]) ≫ (F.μ i' j').app X =
     (F.μ i j).app X ≫ eq_to_hom (by rw [h₁, h₂]) :=
 by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

 @[simp, reassoc] lemma μ_inv_app_eq_to_hom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
   (F.μ_iso i j).inv.app X ≫ eq_to_hom (by rw [h₁, h₂]) =
     eq_to_hom (by rw [h₁, h₂]) ≫ (F.μ_iso i' j').inv.app X :=
 by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

end eq_to_hom

variables {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def add_neg_equiv [add_group A] (F : monoidal_functor (discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
equiv_of_tensor_iso_unit F n (-n : A)
  (eq_to_iso (add_neg_self n)) (eq_to_iso (neg_add_self n)) (subsingleton.elim _ _)

section defs

variables (A C) [add_monoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class has_shift (C : Type u) (A : Type*) [category.{v} C] [add_monoid A] :=
(shift : monoidal_functor (discrete A) (C ⥤ C))

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_inhabited_instance]
structure shift_mk_core :=
(F : A → (C ⥤ C))
(ε : 𝟭 C ≅ F 0)
(μ : Π n m : A, F n ⋙ F m ≅ F (n + m))
(associativity : ∀ (m₁ m₂ m₃ : A) (X : C),
  (F m₃).map ((μ m₁ m₂).hom.app X) ≫ (μ (m₁ + m₂) m₃).hom.app X ≫
    eq_to_hom (by { congr' 2, exact add_assoc _ _ _ }) =
    (μ m₂ m₃).hom.app ((F m₁).obj X) ≫ (μ m₁ (m₂ + m₃)).hom.app X . obviously)
(left_unitality : ∀ (n : A) (X : C),
  (F n).map (ε.hom.app X) ≫ (μ 0 n).hom.app X =
    eq_to_hom (by { dsimp, rw zero_add }) . obviously)
(right_unitality : ∀ (n : A) (X : C),
  ε.hom.app ((F n).obj X) ≫ (μ n 0).hom.app X =
    eq_to_hom (by { dsimp, rw add_zero }) . obviously)

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
@[simps]
def has_shift_mk (h : shift_mk_core C A) : has_shift C A :=
⟨{ ε := h.ε.hom,
   μ := λ m n, (h.μ m n).hom,
   μ_natural' := by { rintros _ _ _ _ ⟨⟨rfl⟩⟩ ⟨⟨rfl⟩⟩, ext, dsimp, simp, dsimp, simp },
   associativity' := by { introv, ext, dsimp, simpa using h.associativity _ _ _ _, },
   left_unitality' :=
    by { introv, ext, dsimp, rw [category.id_comp, ← category.assoc, h.left_unitality], simp },
   right_unitality' :=
    by { introv, ext, dsimp, rw [functor.map_id, category.comp_id,
      ← category.assoc, h.right_unitality], simp },
 ..(discrete.functor h.F) }⟩

variables [has_shift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shift_monoidal_functor : monoidal_functor (discrete A) (C ⥤ C) := has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbreviation shift_functor (i : A) : C ⥤ C := (shift_monoidal_functor C A).obj i

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_functor_add (i j : A) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
((shift_monoidal_functor C A).μ_iso i j).symm

variables (A)

/-- Shifting by zero is the identity functor. -/
abbreviation shift_functor_zero : shift_functor C (0 : A) ≅ 𝟭 C :=
(shift_monoidal_functor C A).ε_iso.symm

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

end defs

section examples
variables [has_shift C ℤ]

example {X Y : C} (f : X ⟶ Y) : X⟦(1 : ℤ)⟧ ⟶ Y⟦1⟧ := f⟦1⟧'
example {X Y : C} (f : X ⟶ Y) : X⟦(-2 : ℤ)⟧ ⟶ Y⟦-2⟧ := f⟦-2⟧'

end examples

section add_monoid

variables {C A} [add_monoid A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

@[simp] lemma has_shift.shift_obj_obj (n : A) (X : C) : (has_shift.shift.obj n).obj X = X⟦n⟧ := rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

@[reassoc] lemma shift_add_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i' j).hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[reassoc] lemma shift_add_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i j').hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[reassoc] lemma shift_add_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw [h₁, h₂]) =
    eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').hom :=
by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[reassoc] lemma eq_to_hom_comp_shift_add_inv₁ (i i' j : A) (h : i = i') :
  eq_to_hom (by rw h) ≫ (shift_add X i' j).inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]

@[reassoc] lemma eq_to_hom_comp_shift_add_inv₂ (i j j' : A) (h : j = j') :
  eq_to_hom (by rw h) ≫ (shift_add X i j').inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]

@[reassoc] lemma eq_to_hom_comp_shift_add_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').inv =
    (shift_add X i j).inv ≫ eq_to_hom (by rw [h₁, h₂]) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]

lemma shift_shift' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_add X i j).inv ≫ f⟦i + j⟧' ≫ (shift_add Y i j).hom :=
by { symmetry, apply nat_iso.naturality_1 }

variables (A)

/-- Shifting by zero is the identity functor. -/
abbreviation shift_zero  :
  X⟦0⟧ ≅ X := (shift_functor_zero C A).app _

lemma shift_zero' :
  f⟦(0 : A)⟧' = (shift_zero A X).hom ≫ f ≫ (shift_zero A Y).inv :=
by { symmetry, apply nat_iso.naturality_2 }

end add_monoid

section opaque_eq_to_iso

variables {ι : Type*} {i j k : ι}

/-- This definition is used instead of `eq_to_iso` so that the proof of `i = j` is visible
to the simplifier -/
def opaque_eq_to_iso (h : i = j) : @iso (discrete ι) _ i j := eq_to_iso h

@[simp]
lemma opaque_eq_to_iso_symm (h : i = j) :
  (opaque_eq_to_iso h).symm = opaque_eq_to_iso h.symm := rfl

@[simp]
lemma opaque_eq_to_iso_inv (h : i = j) :
  (opaque_eq_to_iso h).inv = (opaque_eq_to_iso h.symm).hom := rfl

@[simp, reassoc]
lemma map_opaque_eq_to_iso_comp_app (F : discrete ι ⥤ C ⥤ C) (h : i = j) (h' : j = k) (X : C) :
  (F.map (opaque_eq_to_iso h).hom).app X ≫ (F.map (opaque_eq_to_iso h').hom).app X =
    (F.map (opaque_eq_to_iso $ h.trans h').hom).app X := by { delta opaque_eq_to_iso, simp }

end opaque_eq_to_iso

section add_group

variables (C) {A} [add_group A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)


/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_functor_comp_shift_functor_neg (i : A) :
  shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) i (-i : A) (opaque_eq_to_iso (add_neg_self i))

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_functor_neg_comp_shift_functor (i : A) :
  shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) (-i : A) i (opaque_eq_to_iso (neg_add_self i))

section

variables (C)

/-- Shifting by `n` is a faithful functor. -/
instance shift_functor_faithful (i : A) : faithful (shift_functor C i) :=
faithful.of_comp_iso (shift_functor_comp_shift_functor_neg C i)

/-- Shifting by `n` is a full functor. -/
instance shift_functor_full (i : A) : full (shift_functor C i) :=
begin
  haveI : full (shift_functor C i ⋙ shift_functor C (-i)) :=
    full.of_iso (shift_functor_comp_shift_functor_neg C i).symm,
  exact full.of_comp_faithful _ (shift_functor C (-i))
end

/-- Shifting by `n` is an essentially surjective functor. -/
instance shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) :=
{ mem_ess_image := λ Y, ⟨Y⟦-i⟧, ⟨(shift_functor_neg_comp_shift_functor C i).app Y⟩⟩ }

/-- Shifting by `n` is an equivalence. -/
noncomputable instance shift_functor_is_equivalence (n : A) : is_equivalence (shift_functor C n) :=
equivalence.of_fully_faithfully_ess_surj _

end

variables {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_shift_neg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
(shift_functor_comp_shift_functor_neg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_neg_shift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
(shift_functor_neg_comp_shift_functor C i).app _

variables {X Y}

lemma shift_shift_neg' (i : A) :
  f⟦i⟧'⟦-i⟧' = (shift_shift_neg X i).hom ≫ f ≫ (shift_shift_neg Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_neg_shift' (i : A) :
  f⟦-i⟧'⟦i⟧' = (shift_neg_shift X i).hom ≫ f ≫ (shift_neg_shift Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_equiv_triangle (n : A) (X : C) :
  (shift_shift_neg X n).inv⟦n⟧' ≫ (shift_neg_shift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
(add_neg_equiv (shift_monoidal_functor C A) n).functor_unit_iso_comp X

lemma shift_shift_neg_hom_shift (n : A) (X : C) :
  (shift_shift_neg X n).hom ⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).hom :=
by simp

lemma shift_shift_neg_inv_shift (n : A) (X : C) :
  (shift_shift_neg X n).inv ⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).inv :=
by { ext, rw [← shift_shift_neg_hom_shift, ← functor.map_comp, iso.hom_inv_id, functor.map_id] }

@[simp]
lemma shift_shift_neg_shift_eq (n : A) (X : C) :
  (shift_functor C n).map_iso (shift_shift_neg X n) = shift_neg_shift (X⟦n⟧) n :=
category_theory.iso.ext $ shift_shift_neg_hom_shift _ _

variables (C)

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shift_equiv (n : A) : C ≌ C :=
{ functor := shift_functor C n,
  inverse := shift_functor C (-n),
  ..(add_neg_equiv (shift_monoidal_functor C A) n) }

variable {C}

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
(shift_add X i j).symm ≪≫ ((shift_monoidal_functor C A).to_functor.map_iso
  (opaque_eq_to_iso $ add_comm i j : _)).app X ≪≫ shift_add X j i

@[simp] lemma shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i :=
begin
  ext, dsimp [shift_comm], simpa
end

variables {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
lemma shift_comm' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).hom :=
by simp [shift_comm]

@[reassoc] lemma shift_comm_hom_comp (i j : A) :
  (shift_comm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).hom :=
by rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end add_comm_monoid

end category_theory
