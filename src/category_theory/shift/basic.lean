/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang, Joël Riou
-/
import category_theory.limits.preserves.shapes.zero
import category_theory.monoidal.End
import category_theory.monoidal.discrete

/-!
# Shift

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A `shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `has_shift`: A typeclass asserting the existence of a shift functor.
* `shift_equiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  an self-equivalence of `C`.
* `shift_comm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[has_shift C A]` is implemented using `monoidal_functor (discrete A) (C ⥤ C)`.
However, the API of monodial functors is used only internally: one should use the API of
shifts functors which includes `shift_functor C a : C ⥤ C` for `a : A`,
`shift_functor_zero C A : shift_functor C (0 : A) ≅ 𝟭 C` and
`shift_functor_add C i j : shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j`
(and its variant `shift_functor_add'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shift_functor_add'_assoc`, `shift_functor_add'_zero_add` and
`shift_functor_add'_add_zero`.

-/
namespace category_theory

noncomputable theory

universes v u

variables (C : Type u) (A : Type*) [category.{v} C]

local attribute [instance] endofunctor_monoidal_category

section defs

variables (A C) [add_monoid A]

/-- A category has a shift indexed by an additive monoid `A`
if there is a monoidal functor from `A` to `C ⥤ C`. -/
class has_shift (C : Type u) (A : Type*) [category.{v} C] [add_monoid A] :=
(shift : monoidal_functor (discrete A) (C ⥤ C))

/-- A helper structure to construct the shift functor `(discrete A) ⥤ (C ⥤ C)`. -/
@[nolint has_nonempty_instance]
structure shift_mk_core :=
(F : A → (C ⥤ C))
(zero : F 0 ≅ 𝟭 C)
(add : Π n m : A, F (n + m) ≅ F n ⋙ F m)
(assoc_hom_app : ∀ (m₁ m₂ m₃ : A) (X : C),
  (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) =
    eq_to_hom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫
      (add m₂ m₃).hom.app ((F m₁).obj X))
(zero_add_hom_app : ∀ (n : A) (X : C), (add 0 n).hom.app X =
  eq_to_hom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X))
(add_zero_hom_app : ∀ (n : A)  (X : C), (add n 0).hom.app X =
  eq_to_hom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X))

namespace shift_mk_core

variables {C A}

attribute [reassoc] assoc_hom_app

@[reassoc]
lemma assoc_inv_app (h : shift_mk_core C A) (m₁ m₂ m₃ : A) (X : C) :
  (h.F m₃).map ((h.add m₁ m₂).inv.app X) ≫ (h.add (m₁ + m₂) m₃).inv.app X =
    (h.add m₂ m₃).inv.app ((h.F m₁).obj X) ≫ (h.add m₁ (m₂ + m₃)).inv.app X ≫
      eq_to_hom (by rw [add_assoc]) :=
begin
  rw [← cancel_mono ((h.add (m₁ + m₂) m₃).hom.app X ≫ (h.F m₃).map ((h.add m₁ m₂).hom.app X)),
    category.assoc, category.assoc, category.assoc, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    iso.inv_hom_id_app, functor.map_id, h.assoc_hom_app, eq_to_hom_trans_assoc, eq_to_hom_refl,
    category.id_comp, iso.inv_hom_id_app_assoc, iso.inv_hom_id_app],
  refl,
end

lemma zero_add_inv_app (h : shift_mk_core C A) (n : A) (X : C) :
  (h.add 0 n).inv.app X = (h.F n).map (h.zero.hom.app X) ≫
    eq_to_hom (by dsimp; rw [zero_add]) :=
by rw [← cancel_epi ((h.add 0 n).hom.app X), iso.hom_inv_id_app, h.zero_add_hom_app,
  category.assoc, ← functor.map_comp_assoc, iso.inv_hom_id_app, functor.map_id,
  category.id_comp, eq_to_hom_trans, eq_to_hom_refl]

lemma add_zero_inv_app (h : shift_mk_core C A) (n : A) (X : C) :
    (h.add n 0).inv.app X = h.zero.hom.app ((h.F n).obj X) ≫
      eq_to_hom (by dsimp; rw [add_zero]) :=
by rw [← cancel_epi ((h.add n 0).hom.app X), iso.hom_inv_id_app, h.add_zero_hom_app,
  category.assoc, iso.inv_hom_id_app_assoc, eq_to_hom_trans, eq_to_hom_refl]

end shift_mk_core

section

local attribute [simp] eq_to_hom_map
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
def has_shift_mk (h : shift_mk_core C A) : has_shift C A :=
⟨ { ε := h.zero.inv,
    μ := λ m n, (h.add m.as n.as).inv,
    μ_natural' := by { rintros ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨Y'⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨⟨⟨rfl⟩⟩⟩, ext,
      dsimp, simp only [discrete.functor_map_id, category.assoc], dsimp, simp },
    associativity' :=
    begin
      rintros ⟨m₁⟩ ⟨m₂⟩ ⟨m₃⟩,
      ext X,
      dsimp,
      simp [h.assoc_inv_app_assoc m₁ m₂ m₃ X],
    end,
    left_unitality' :=
    begin
      rintro ⟨n⟩,
      ext X,
      dsimp,
      simp only [h.zero_add_inv_app, ←functor.map_comp, category.id_comp, eq_to_hom_map,
        eq_to_hom_app, category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id,
        iso.inv_hom_id_app],
      erw [functor.map_id],
    end,
    right_unitality' :=
    begin
      rintro ⟨n⟩,
      ext X,
      dsimp,
      simpa only [h.add_zero_inv_app, functor.map_id, category.comp_id, eq_to_hom_map,
        eq_to_hom_app, category.assoc, eq_to_hom_trans, eq_to_hom_refl, iso.inv_hom_id_app],
    end,
    ..(discrete.functor h.F) }⟩

end

section

variables [has_shift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shift_monoidal_functor : monoidal_functor (discrete A) (C ⥤ C) := has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift_functor (i : A) : C ⥤ C := (shift_monoidal_functor C A).obj ⟨i⟩

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
def shift_functor_add (i j : A) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
((shift_monoidal_functor C A).μ_iso ⟨i⟩ ⟨j⟩).symm

/-- When `k = i + j`, shifting by `k` is the same as shifting by `i` and then shifting by `j`. -/
def shift_functor_add' (i j k : A) (h : i + j = k) :
  shift_functor C k ≅ shift_functor C i ⋙ shift_functor C j :=
eq_to_iso (by rw [h]) ≪≫ shift_functor_add C i j

lemma shift_functor_add'_eq_shift_functor_add (i j : A) :
  shift_functor_add' C i j (i+j) rfl = shift_functor_add C i j :=
by { ext1, apply category.id_comp }

variables (A)

/-- Shifting by zero is the identity functor. -/
def shift_functor_zero : shift_functor C (0 : A) ≅ 𝟭 C :=
(shift_monoidal_functor C A).ε_iso.symm

end

variables {C A}

lemma shift_mk_core.shift_functor_eq (h : shift_mk_core C A) (a : A) :
    @shift_functor _ _ _ _ (has_shift_mk C A h) a = h.F a :=
functor.ext (by tidy) (by tidy)

lemma shift_mk_core.shift_functor_zero_eq (h : shift_mk_core C A) :
  @shift_functor_zero _ _ _ _ (has_shift_mk C A h) = h.zero :=
begin
  letI := has_shift_mk C A h,
  ext1,
  suffices : (shift_functor_zero C A).inv = h.zero.inv,
  { rw [← cancel_mono (h.zero.inv), h.zero.hom_inv_id, ← this, iso.hom_inv_id],
    refl, },
  refl,
end

lemma shift_mk_core.shift_functor_add_eq (h : shift_mk_core C A) (a b : A) :
  @shift_functor_add _ _ _ _ (has_shift_mk C A h) a b = h.add a b :=
begin
  letI := has_shift_mk C A h,
  ext1,
  suffices : (shift_functor_add C a b).inv = (h.add a b).inv,
  { rw [← cancel_mono ((h.add a b).inv), (h.add a b).hom_inv_id, ← this, iso.hom_inv_id],
    refl, },
  refl,
end

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

variable (C)

variables [has_shift C A]

local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

lemma shift_functor_add'_zero_add (a : A) :
  shift_functor_add' C 0 a a (zero_add a) = (functor.left_unitor _).symm ≪≫
    iso_whisker_right (shift_functor_zero C A).symm (shift_functor C a) :=
begin
  ext X,
  dsimp [shift_functor_add'],
  erw [obj_ε_app],
  simpa [eq_to_hom_map],
end

lemma shift_functor_add'_add_zero (a : A) :
  shift_functor_add' C a 0 a (add_zero a) = (functor.right_unitor _).symm ≪≫
    iso_whisker_left (shift_functor C a) (shift_functor_zero C A).symm :=
begin
  ext X,
  dsimp [shift_functor_add'],
  erw [ε_app_obj],
  simpa [eq_to_hom_map],
end

lemma shift_functor_add'_assoc (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) :
  shift_functor_add' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃]) ≪≫
    iso_whisker_right (shift_functor_add' C a₁ a₂ a₁₂ h₁₂) _ ≪≫ functor.associator _ _ _  =
  shift_functor_add' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃]) ≪≫
    iso_whisker_left _ (shift_functor_add' C a₂ a₃ a₂₃ h₂₃) :=
begin
  substs h₁₂ h₂₃ h₁₂₃,
  ext X,
  dsimp,
  simp only [shift_functor_add'_eq_shift_functor_add, category.comp_id],
  dsimp [shift_functor_add', shift_functor_add, shift_functor],
  simp [obj_μ_inv_app, eq_to_hom_map],
end

lemma shift_functor_add_assoc (a₁ a₂ a₃ : A) :
  shift_functor_add C (a₁ + a₂) a₃ ≪≫
    iso_whisker_right (shift_functor_add C a₁ a₂) _ ≪≫ functor.associator _ _ _  =
  shift_functor_add' C a₁ (a₂ + a₃) _ (add_assoc a₁ a₂ a₃).symm ≪≫
    iso_whisker_left _ (shift_functor_add C a₂ a₃) :=
begin
  ext X,
  simpa [shift_functor_add'_eq_shift_functor_add]
    using nat_trans.congr_app (congr_arg iso.hom
      (shift_functor_add'_assoc C a₁ a₂ a₃ _ _ _ rfl rfl rfl)) X,
end

variable {C}

lemma shift_functor_add'_zero_add_hom_app (a : A) (X : C) :
  (shift_functor_add' C 0 a a (zero_add a)).hom.app X =
    ((shift_functor_zero C A).inv.app X)⟦a⟧' :=
by simpa using nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_zero_add C a)) X

lemma shift_functor_add_zero_add_hom_app (a : A) (X : C) :
  (shift_functor_add C 0 a).hom.app X =
    eq_to_hom (by dsimp; rw [zero_add]) ≫ ((shift_functor_zero C A).inv.app X)⟦a⟧' :=
begin
  erw [← shift_functor_add'_zero_add_hom_app],
  dsimp [shift_functor_add'],
  simp,
end

lemma shift_functor_add'_zero_add_inv_app (a : A) (X : C) :
  (shift_functor_add' C 0 a a (zero_add a)).inv.app X =
    ((shift_functor_zero C A).hom.app X)⟦a⟧' :=
begin
  have := nat_trans.congr_app (congr_arg iso.inv (shift_functor_add'_zero_add C a)) X,
  simp only [iso.trans_inv, iso_whisker_right_inv, iso.symm_inv, nat_trans.comp_app,
    whisker_right_app, functor.left_unitor_hom_app] at this,
  dsimp at this,
  simpa only [category.comp_id] using this,
end

lemma shift_functor_add_zero_add_inv_app (a : A) (X : C) :
  (shift_functor_add C 0 a).inv.app X =
    ((shift_functor_zero C A).hom.app X)⟦a⟧' ≫ eq_to_hom (by dsimp; rw [zero_add]) :=
begin
  erw [← shift_functor_add'_zero_add_inv_app],
  dsimp [shift_functor_add'],
  simp,
end

lemma shift_functor_add'_add_zero_hom_app (a : A) (X : C):
  (shift_functor_add' C a 0 a (add_zero a)).hom.app X =
    (shift_functor_zero C A).inv.app (X⟦a⟧) :=
by simpa using nat_trans.congr_app (congr_arg iso.hom (shift_functor_add'_add_zero C a)) X

lemma shift_functor_add_add_zero_hom_app (a : A) (X : C):
  (shift_functor_add C a 0).hom.app X =
    eq_to_hom (by dsimp; rw [add_zero]) ≫ (shift_functor_zero C A).inv.app (X⟦a⟧) :=
begin
  rw [← shift_functor_add'_add_zero_hom_app],
  dsimp [shift_functor_add'],
  simp,
end

lemma shift_functor_add'_add_zero_inv_app (a : A) (X : C):
  (shift_functor_add' C a 0 a (add_zero a)).inv.app X =
    (shift_functor_zero C A).hom.app (X⟦a⟧) :=
begin
  have := nat_trans.congr_app (congr_arg iso.inv (shift_functor_add'_add_zero C a)) X,
  simp only [iso.trans_inv, iso_whisker_left_inv, iso.symm_inv, nat_trans.comp_app,
    whisker_left_app, functor.right_unitor_hom_app] at this,
  dsimp at this,
  simpa only [category.comp_id] using this,
end

lemma shift_functor_add_add_zero_inv_app (a : A) (X : C):
  (shift_functor_add C a 0).inv.app X =
    (shift_functor_zero C A).hom.app (X⟦a⟧) ≫ eq_to_hom (by dsimp; rw [add_zero]) :=
begin
  rw [← shift_functor_add'_add_zero_inv_app],
  dsimp [shift_functor_add'],
  simp,
end

@[reassoc]
lemma shift_functor_add'_assoc_hom_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
  (shift_functor_add' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).hom.app X ≫
    ((shift_functor_add' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' =
  (shift_functor_add' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).hom.app X ≫
    (shift_functor_add' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) :=
by simpa using nat_trans.congr_app (congr_arg iso.hom
  (shift_functor_add'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

@[reassoc]
lemma shift_functor_add'_assoc_inv_app (a₁ a₂ a₃ a₁₂ a₂₃ a₁₂₃ : A)
  (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h₁₂₃ : a₁ + a₂ + a₃ = a₁₂₃) (X : C) :
  ((shift_functor_add' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
    (shift_functor_add' C a₁₂ a₃ a₁₂₃ (by rw [← h₁₂, h₁₂₃])).inv.app X =
  (shift_functor_add' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
    (shift_functor_add' C a₁ a₂₃ a₁₂₃ (by rw [← h₂₃, ← add_assoc, h₁₂₃])).inv.app X :=
by simpa using nat_trans.congr_app (congr_arg iso.inv
  (shift_functor_add'_assoc C _ _ _ _ _ _ h₁₂ h₂₃ h₁₂₃)) X

@[reassoc]
lemma shift_functor_add_assoc_hom_app (a₁ a₂ a₃ : A) (X : C) :
  (shift_functor_add C (a₁ + a₂) a₃).hom.app X ≫
    ((shift_functor_add C a₁ a₂).hom.app X)⟦a₃⟧' =
  (shift_functor_add' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).hom.app X ≫
    (shift_functor_add C a₂ a₃).hom.app (X⟦a₁⟧) :=
by simpa using nat_trans.congr_app (congr_arg iso.hom
  (shift_functor_add_assoc C a₁ a₂ a₃)) X

@[reassoc]
lemma shift_functor_add_assoc_inv_app (a₁ a₂ a₃ : A) (X : C) :
  ((shift_functor_add C a₁ a₂).inv.app X)⟦a₃⟧' ≫
    (shift_functor_add C (a₁ + a₂) a₃).inv.app X =
  (shift_functor_add C a₂ a₃).inv.app (X⟦a₁⟧) ≫
    (shift_functor_add' C a₁ (a₂ + a₃) (a₁ + a₂ + a₃) (add_assoc _ _ _).symm).inv.app X :=
by simpa using nat_trans.congr_app (congr_arg iso.inv
  (shift_functor_add_assoc C a₁ a₂ a₃)) X

end defs

section add_monoid

variables {C A} [add_monoid A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

@[simp] lemma has_shift.shift_obj_obj (n : A) (X : C) : (has_shift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

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

variables (C) {A}

/-- When `i + j = 0`, shifting by `i` and by `j` gives the identity functor -/
def shift_functor_comp_iso_id (i j : A) (h : i + j = 0) :
  shift_functor C i ⋙ shift_functor C j ≅ 𝟭 C :=
(shift_functor_add' C i j 0 h).symm ≪≫ shift_functor_zero C A

end add_monoid

section add_group

variables (C) {A} [add_group A] [has_shift C A]

/-- shifting by `i` and shifting by `j` forms an equivalence when `i + j = 0`. -/
@[simps]
def shift_equiv' (i j : A) (h : i + j = 0) : C ≌ C :=
{ functor := shift_functor C i,
  inverse := shift_functor C j,
  unit_iso := (shift_functor_comp_iso_id C i j h).symm,
  counit_iso := (shift_functor_comp_iso_id C j i
    (by rw [← add_left_inj j, add_assoc, h, zero_add, add_zero])),
  functor_unit_iso_comp' := λ X, begin
    let E := equiv_of_tensor_iso_unit (shift_monoidal_functor C A) ⟨i⟩ ⟨j⟩
      (eq_to_iso (by ext; exact h))
      (eq_to_iso (by ext; dsimp; rw [← add_left_inj j, add_assoc, h, zero_add, add_zero]))
      (subsingleton.elim _ _),
    convert equivalence.functor_unit_iso_comp E X,
    all_goals
    { ext X,
      dsimp [shift_functor_comp_iso_id, unit_of_tensor_iso_unit, shift_functor_add'],
      simpa only [eq_to_hom_map, category.assoc], },
  end }

/-- shifting by `n` and shifting by `-n` forms an equivalence. -/
abbreviation shift_equiv (i : A) : C ≌ C := shift_equiv' C i (-i) (add_neg_self i)

variables (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : is_equivalence (shift_functor C i) :=
is_equivalence.of_equivalence (shift_equiv C i)

@[simp] lemma shift_functor_inv (i : A) :
  (shift_functor C i).inv = shift_functor C (-i) :=
rfl

section

variables (C)

/-- Shifting by `n` is an essentially surjective functor. -/
instance shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) :=
  equivalence.ess_surj_of_equivalence _

end

variables {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_shift_neg (i : A) : X⟦i⟧⟦-i⟧ ≅ X :=
(shift_equiv C i).unit_iso.symm.app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_neg_shift (i : A) : X⟦-i⟧⟦i⟧ ≅ X :=
(shift_equiv C i).counit_iso.app _

variables {X Y}

lemma shift_shift_neg' (i : A) :
  f⟦i⟧'⟦-i⟧' = (shift_functor_comp_iso_id C i (-i) (add_neg_self i)).hom.app X ≫
    f ≫ (shift_functor_comp_iso_id C i (-i) (add_neg_self i)).inv.app Y :=
(nat_iso.naturality_2 (shift_functor_comp_iso_id C i (-i) (add_neg_self i)) f).symm

lemma shift_neg_shift' (i : A) :
  f⟦-i⟧'⟦i⟧' = (shift_functor_comp_iso_id C (-i) i (neg_add_self i)).hom.app X ≫ f ≫
    (shift_functor_comp_iso_id C (-i) i (neg_add_self i)).inv.app Y :=
(nat_iso.naturality_2 (shift_functor_comp_iso_id C (-i) i (neg_add_self i)) f).symm

lemma shift_equiv_triangle (n : A) (X : C) :
  (shift_shift_neg X n).inv⟦n⟧' ≫ (shift_neg_shift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
(shift_equiv C n).functor_unit_iso_comp X

section

lemma shift_shift_functor_comp_iso_id_hom_app (n m : A) (h : n + m = 0) (X : C) :
  ((shift_functor_comp_iso_id C n m h).hom.app X)⟦n⟧' =
    (shift_functor_comp_iso_id C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).hom.app (X⟦n⟧) :=
begin
  dsimp [shift_functor_comp_iso_id],
  simpa only [functor.map_comp, ← shift_functor_add'_zero_add_inv_app n X,
    ← shift_functor_add'_add_zero_inv_app n X ]
    using shift_functor_add'_assoc_inv_app n m n 0 0 n h
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg]) (by rw [h, zero_add]) X,
end

lemma shift_shift_functor_comp_iso_id_inv_app (n m : A) (h : n + m = 0) (X : C) :
  ((shift_functor_comp_iso_id C n m h).inv.app X)⟦n⟧' =
    ((shift_functor_comp_iso_id C m n
      (by rw [← neg_eq_of_add_eq_zero_left h, add_right_neg])).inv.app (X⟦n⟧)) :=
begin
  rw [← cancel_mono (((shift_functor_comp_iso_id C n m h).hom.app X)⟦n⟧'),
    ← functor.map_comp, iso.inv_hom_id_app, functor.map_id,
    shift_shift_functor_comp_iso_id_hom_app, iso.inv_hom_id_app],
  refl,
end

lemma shift_shift_functor_comp_iso_id_add_neg_self_hom_app (n : A) (X : C) :
  ((shift_functor_comp_iso_id C n (-n) (add_neg_self n)).hom.app X)⟦n⟧' =
    (shift_functor_comp_iso_id C (-n) n (neg_add_self n)).hom.app (X⟦n⟧) :=
by apply shift_shift_functor_comp_iso_id_hom_app

lemma shift_shift_functor_comp_iso_id_add_neg_self_inv_app (n : A) (X : C) :
  ((shift_functor_comp_iso_id C n (-n) (add_neg_self n)).inv.app X)⟦n⟧' =
    (shift_functor_comp_iso_id C (-n) n (neg_add_self n)).inv.app (X⟦n⟧) :=
by apply shift_shift_functor_comp_iso_id_inv_app

lemma shift_shift_functor_comp_iso_id_neg_add_self_hom_app (n : A) (X : C) :
  ((shift_functor_comp_iso_id C (-n) n (neg_add_self n)).hom.app X)⟦-n⟧' =
    (shift_functor_comp_iso_id C n (-n) (add_neg_self n)).hom.app (X⟦-n⟧) :=
by apply shift_shift_functor_comp_iso_id_hom_app

lemma shift_shift_functor_comp_iso_id_neg_add_self_inv_app (n : A) (X : C) :
  ((shift_functor_comp_iso_id C (-n) n (neg_add_self n)).inv.app X)⟦-n⟧' =
    (shift_functor_comp_iso_id C n (-n) (add_neg_self n)).inv.app (X⟦-n⟧) :=
by apply shift_shift_functor_comp_iso_id_inv_app

end

variables {A C}

open category_theory.limits

variables [has_zero_morphisms C]

lemma shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
category_theory.functor.map_zero _ _ _

end add_group

section add_comm_monoid

variables (C) {A} [add_comm_monoid A] [has_shift C A]

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shift_functor_comm (i j : A) :
  shift_functor C i ⋙ shift_functor C j ≅
    shift_functor C j ⋙ shift_functor C i :=
(shift_functor_add C i j).symm ≪≫ shift_functor_add' C j i (i + j) (add_comm j i)

lemma shift_functor_comm_eq (i j k : A) (h : i + j = k):
  shift_functor_comm C i j = (shift_functor_add' C i j k h).symm ≪≫
    shift_functor_add' C j i k (by rw [add_comm j i, h]) :=
begin
  subst h,
  rw [shift_functor_add'_eq_shift_functor_add],
  refl,
end

lemma shift_functor_comm_symm (i j : A) :
  (shift_functor_comm C i j).symm = shift_functor_comm C j i :=
begin
  ext1,
  dsimp,
  simpa only [shift_functor_comm_eq C i j (i + j) rfl,
    shift_functor_comm_eq C j i (i + j) (add_comm j i)],
end

variables {C} (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
abbreviation shift_comm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
  (shift_functor_comm C i j).app X

@[simp] lemma shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i :=
begin
  ext1,
  exact nat_trans.congr_app (congr_arg iso.hom (shift_functor_comm_symm C i j)) X,
end

variables {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
lemma shift_comm' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).hom :=
begin
  erw [← shift_comm_symm Y i j, ← ((shift_functor_comm C i j).hom.naturality_assoc f),
    iso.hom_inv_id_app, category.comp_id],
  refl,
end

@[reassoc] lemma shift_comm_hom_comp (i j : A) :
  (shift_comm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).hom :=
by rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

lemma shift_functor_zero_hom_app_shift (n : A) :
  (shift_functor_zero C A).hom.app (X⟦n⟧) =
    (shift_functor_comm C n 0).hom.app X ≫ ((shift_functor_zero C A).hom.app X)⟦n⟧' :=
begin
  rw [← shift_functor_add'_zero_add_inv_app n X, shift_functor_comm_eq C n 0 n (add_zero n)],
  dsimp,
  rw [category.assoc, iso.hom_inv_id_app, category.comp_id, shift_functor_add'_add_zero_inv_app],
end

lemma shift_functor_zero_inv_app_shift (n : A) :
  (shift_functor_zero C A).inv.app (X⟦n⟧) =
  ((shift_functor_zero C A).inv.app X)⟦n⟧' ≫ (shift_functor_comm C n 0).inv.app X :=
begin
  rw [← cancel_mono ((shift_functor_zero C A).hom.app (X⟦n⟧)), category.assoc, iso.inv_hom_id_app,
    shift_functor_zero_hom_app_shift, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    iso.inv_hom_id_app],
  dsimp,
  rw [functor.map_id],
end

@[reassoc]
lemma shift_functor_comm_hom_app_comp_shift_shift_functor_add_hom_app (m₁ m₂ m₃ : A) (X : C) :
  (shift_functor_comm C m₁ (m₂ + m₃)).hom.app X ≫
    ((shift_functor_add C m₂ m₃).hom.app X)⟦m₁⟧' =
  (shift_functor_add C m₂ m₃).hom.app (X⟦m₁⟧) ≫
    ((shift_functor_comm C m₁ m₂).hom.app X)⟦m₃⟧' ≫
    (shift_functor_comm C m₁ m₃).hom.app (X⟦m₂⟧) :=
begin
  simp only [← cancel_mono ((shift_functor_comm C m₁ m₃).inv.app (X⟦m₂⟧)),
    ← cancel_mono (((shift_functor_comm C m₁ m₂).inv.app X)⟦m₃⟧'),
    category.assoc, iso.hom_inv_id_app],
  dsimp,
  simp only [category.id_comp, ← functor.map_comp, iso.hom_inv_id_app],
  dsimp,
  simp only [functor.map_id, category.comp_id,
    shift_functor_comm_eq C _ _ _ rfl, ← shift_functor_add'_eq_shift_functor_add],
  dsimp,
  simp only [category.assoc, iso.hom_inv_id_app_assoc, iso.inv_hom_id_app_assoc,
    ← functor.map_comp,
    shift_functor_add'_assoc_hom_app_assoc m₂ m₃ m₁ (m₂ + m₃) (m₁ + m₃) (m₁ + (m₂ + m₃)) rfl
      (add_comm m₃ m₁) (add_comm _ m₁) X,
    ← shift_functor_add'_assoc_hom_app_assoc m₂ m₁ m₃ (m₁ + m₂) (m₁ + m₃)
      (m₁ + (m₂ + m₃)) (add_comm _ _) rfl (by rw [add_comm m₂ m₁, add_assoc]) X,
    shift_functor_add'_assoc_hom_app m₁ m₂ m₃
      (m₁ + m₂) (m₂ + m₃) (m₁ + (m₂ + m₃)) rfl rfl (add_assoc _ _ _) X],
end

end add_comm_monoid

variables {C A} {D : Type*} [category D] [add_monoid A] [has_shift D A]
variables (F : C ⥤ D) [full F] [faithful F]

section

variables (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shift_functor D i)

include F s i

/-- auxiliary definition for `has_shift_of_fully_faithful` -/
def has_shift_of_fully_faithful_zero : s 0 ≅ 𝟭 C :=
nat_iso_of_comp_fully_faithful F ((i 0) ≪≫ iso_whisker_left F (shift_functor_zero D A) ≪≫
  functor.right_unitor _ ≪≫ (functor.left_unitor _).symm)

@[simp]
lemma map_has_shift_of_fully_faithful_zero_hom_app (X : C) :
  F.map ((has_shift_of_fully_faithful_zero F s i).hom.app X) =
    (i 0).hom.app X ≫ (shift_functor_zero D A).hom.app (F.obj X) :=
by { dsimp [has_shift_of_fully_faithful_zero], simp, }

@[simp]
lemma map_has_shift_of_fully_faithful_zero_inv_app (X : C) :
F.map ((has_shift_of_fully_faithful_zero F s i).inv.app X) =
  (shift_functor_zero D A).inv.app (F.obj X) ≫ (i 0).inv.app X :=
by { dsimp [has_shift_of_fully_faithful_zero], simp, }

/-- auxiliary definition for `has_shift_of_fully_faithful` -/
def has_shift_of_fully_faithful_add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
nat_iso_of_comp_fully_faithful F (i (a + b) ≪≫
  iso_whisker_left _ (shift_functor_add D a b) ≪≫
  (functor.associator _ _ _).symm ≪≫ (iso_whisker_right (i a).symm _) ≪≫
  functor.associator _ _ _ ≪≫ (iso_whisker_left _ (i b).symm) ≪≫
  (functor.associator _ _ _).symm)

@[simp]
lemma map_has_shift_of_fully_faithful_add_hom_app (a b : A) (X : C) :
  F.map ((has_shift_of_fully_faithful_add F s i a b).hom.app X) =
    (i (a + b)).hom.app X ≫ (shift_functor_add D a b).hom.app (F.obj X) ≫
      ((i a).inv.app X)⟦b⟧' ≫ (i b).inv.app ((s a).obj X) :=
by { dsimp [has_shift_of_fully_faithful_add], simp, }

@[simp]
lemma map_has_shift_of_fully_faithful_add_inv_app (a b : A) (X : C) :
  F.map ((has_shift_of_fully_faithful_add F s i a b).inv.app X) =
    (i b).hom.app ((s a).obj X) ≫ ((i a).hom.app X)⟦b⟧' ≫
      (shift_functor_add D a b).inv.app (F.obj X) ≫ (i (a + b)).inv.app X :=
by { dsimp [has_shift_of_fully_faithful_add], simp, }

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def has_shift_of_fully_faithful : has_shift C A := has_shift_mk C A
  { F := s,
    zero := has_shift_of_fully_faithful_zero F s i,
    add := has_shift_of_fully_faithful_add F s i,
    assoc_hom_app := λ m₁ m₂ m₃ X, F.map_injective begin
      rw [← cancel_mono ((i m₃).hom.app ((s m₂).obj ((s m₁).obj X)))],
      simp only [functor.map_comp, map_has_shift_of_fully_faithful_add_hom_app, category.assoc,
        iso.inv_hom_id_app_assoc, iso.inv_hom_id_app],
      erw [(i m₃).hom.naturality],
      have := dcongr_arg (λ a, (i a).hom.app X) (add_assoc m₁ m₂ m₃),
      dsimp at this,
      dsimp,
      rw [iso.inv_hom_id_app_assoc, map_has_shift_of_fully_faithful_add_hom_app, this,
        eq_to_hom_map, category.comp_id, ← functor.map_comp, category.assoc,
        iso.inv_hom_id_app_assoc, functor.map_comp, functor.map_comp,
        shift_functor_add_assoc_hom_app_assoc m₁ m₂ m₃ (F.obj X)],
      dsimp [shift_functor_add'],
      simp only [eq_to_hom_app, category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl,
        category.id_comp, nat_trans.naturality_assoc, functor.comp_map],
    end,
    zero_add_hom_app := λ n X, F.map_injective begin
      have this := dcongr_arg (λ a, (i a).hom.app X) (zero_add n),
      dsimp at this,
      rw [← cancel_mono ((i n).hom.app ((s 0).obj X))],
      simp only [this, map_has_shift_of_fully_faithful_add_hom_app,
        shift_functor_add_zero_add_hom_app, eq_to_hom_map, category.assoc,
        eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp, iso.inv_hom_id_app,
        functor.map_comp],
      erw [(i n).hom.naturality],
      dsimp,
      simp,
    end,
    add_zero_hom_app := λ n X, F.map_injective begin
      have := dcongr_arg (λ a, (i a).hom.app X) (add_zero n),
      dsimp at this,
      simpa [this, ← nat_trans.naturality_assoc, eq_to_hom_map,
        shift_functor_add_add_zero_hom_app],
    end, }

end

end category_theory
