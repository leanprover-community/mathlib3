/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Andrew Yang
-/
import category_theory.limits.preserves.shapes.zero
import category_theory.monoidal.End
import category_theory.monoidal.discrete

/-!
# Shift

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

Many of the definitions in this file are marked as an `abbreviation` so that the simp lemmas in
`category_theory/monoidal/End` can apply.

-/
namespace category_theory

noncomputable theory

universes v u

variables (C : Type u) (A : Type*) [category.{v} C]

local attribute [instance] endofunctor_monoidal_category

section eq_to_hom

variables {A C}

variables [add_monoid A] (F : monoidal_functor (discrete A) (C ⥤ C))

 @[simp, reassoc] lemma eq_to_hom_μ_app {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
   eq_to_hom (by rw [h₁, h₂] : (F.obj ⟨i⟩ ⊗ F.obj ⟨j⟩).obj X =
       (F.obj ⟨i'⟩ ⊗ F.obj ⟨j'⟩).obj X) ≫ (F.μ ⟨i'⟩ ⟨j'⟩).app X =
     (F.μ ⟨i⟩ ⟨j⟩).app X ≫ eq_to_hom (by rw [h₁, h₂]) :=
 by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

 @[simp, reassoc] lemma μ_inv_app_eq_to_hom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
   inv ((F.μ ⟨i⟩ ⟨j⟩).app X) ≫ eq_to_hom (by rw [h₁, h₂]) =
     eq_to_hom (by rw [h₁, h₂]) ≫ inv ((F.μ ⟨i'⟩ ⟨j'⟩).app X) :=
 by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

end eq_to_hom

variables {A C}

/-- A monoidal functor from a group `A` into `C ⥤ C` induces
a self-equivalence of `C` for each `n : A`. -/
@[simps functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def add_neg_equiv [add_group A] (F : monoidal_functor (discrete A) (C ⥤ C)) (n : A) : C ≌ C :=
equiv_of_tensor_iso_unit F ⟨n⟩ ⟨(-n : A)⟩
  (discrete.eq_to_iso (add_neg_self n)) (discrete.eq_to_iso (neg_add_self n))
  (subsingleton.elim _ _)

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

section
local attribute [simp] eq_to_hom_map
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

/-- Constructs a `has_shift C A` instance from `shift_mk_core`. -/
@[simps]
def has_shift_mk (h : shift_mk_core C A) : has_shift C A :=
⟨{ ε := h.ε.hom,
   μ := λ m n, (h.μ m.as n.as).hom,
   μ_natural' := by { rintros ⟨X⟩ ⟨Y⟩ ⟨X'⟩ ⟨Y'⟩ ⟨⟨⟨rfl⟩⟩⟩ ⟨⟨⟨rfl⟩⟩⟩, ext,
     dsimp, simp, dsimp, simp },
   associativity' := by { introv, ext, dsimp, simpa using h.associativity _ _ _ _, },
   left_unitality' :=
    by { rintro ⟨X⟩, ext, dsimp, rw [category.id_comp, ← category.assoc, h.left_unitality], simp },
   right_unitality' :=
    by { rintro ⟨X⟩, ext, dsimp, rw [functor.map_id, category.comp_id,
      ← category.assoc, h.right_unitality], simp },
 ..(discrete.functor h.F) }⟩

end

variables [has_shift C A]

/-- The monoidal functor from `A` to `C ⥤ C` given a `has_shift` instance. -/
def shift_monoidal_functor : monoidal_functor (discrete A) (C ⥤ C) := has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbreviation shift_functor (i : A) : C ⥤ C := (shift_monoidal_functor C A).obj ⟨i⟩

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_functor_add (i j : A) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
((shift_monoidal_functor C A).μ_iso ⟨i⟩ ⟨j⟩).symm

variables (A)

/-- Shifting by zero is the identity functor. -/
abbreviation shift_functor_zero : shift_functor C (0 : A) ≅ 𝟭 C :=
(shift_monoidal_functor C A).ε_iso.symm

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

end defs

section add_monoid

variables {C A} [add_monoid A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

@[simp] lemma has_shift.shift_obj_obj (n : A) (X : C) : (has_shift.shift.obj ⟨n⟩).obj X = X⟦n⟧ :=
rfl

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

section add_group

variables (C) {A} [add_group A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` is an equivalence. -/
instance (i : A) : is_equivalence (shift_functor C i) :=
begin
  change is_equivalence (add_neg_equiv (shift_monoidal_functor C A) i).functor,
  apply_instance,
end

@[simp] lemma shift_functor_inv (i : A) :
  (shift_functor C i).inv = shift_functor C (-i) :=
rfl

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_functor_comp_shift_functor_neg (i : A) :
  shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) ⟨i⟩ ⟨(-i : A)⟩
  (discrete.eq_to_iso (add_neg_self i))

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_functor_neg_comp_shift_functor (i : A) :
  shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) ⟨(-i : A)⟩ ⟨i⟩
  (discrete.eq_to_iso (neg_add_self i))

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

section
local attribute [reducible] discrete.add_monoidal

lemma shift_shift_neg_hom_shift (n : A) (X : C) :
  (shift_shift_neg X n).hom ⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).hom :=
begin
  -- This is just `simp, simp [eq_to_hom_map]`.
  simp only [iso.app_hom, unit_of_tensor_iso_unit_hom_app, eq_to_iso.hom, functor.map_comp,
    obj_μ_app, eq_to_iso.inv, obj_ε_inv_app, μ_naturalityₗ_assoc, category.assoc,
    μ_inv_hom_app_assoc, ε_inv_app_obj, μ_naturalityᵣ_assoc],
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_hom_trans],
end

end

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

lemma shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
category_theory.functor.map_zero _ _ _

end add_group

section add_comm_monoid

variables {C A} [add_comm_monoid A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shift_comm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
(shift_add X i j).symm ≪≫ ((shift_monoidal_functor C A).to_functor.map_iso
  (discrete.eq_to_iso $ add_comm i j : (⟨i+j⟩ : discrete A) ≅ ⟨j+i⟩)).app X ≪≫ shift_add X j i

@[simp] lemma shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i :=
begin
  ext, dsimp [shift_comm], simpa [eq_to_hom_map],
end

variables {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
lemma shift_comm' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).hom :=
begin
  -- This is just `simp, simp [eq_to_hom_map]`.
  simp only [shift_comm, iso.trans_hom, iso.symm_hom, iso.app_inv, iso.symm_inv,
    monoidal_functor.μ_iso_hom, iso.app_hom, functor.map_iso_hom, eq_to_iso.hom, μ_naturality_assoc,
    nat_trans.naturality_assoc, nat_trans.naturality, functor.comp_map, category.assoc,
    μ_inv_hom_app_assoc],
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
    μ_hom_inv_app_assoc],
end

@[reassoc] lemma shift_comm_hom_comp (i j : A) :
  (shift_comm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).hom :=
by rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end add_comm_monoid

variables {D : Type*} [category D] [add_monoid A] [has_shift D A]
variables (F : C ⥤ D) [full F] [faithful F]

section
local attribute [reducible] discrete.add_monoidal

/-- Given a family of endomorphisms of `C` which are interwined by a fully faithful `F : C ⥤ D`
with shift functors on `D`, we can promote that family to shift functors on `C`. -/
def has_shift_of_fully_faithful
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shift_functor D i) : has_shift C A :=
has_shift_mk C A
{ F := s,
  ε := nat_iso_of_comp_fully_faithful F
    (calc 𝟭 C ⋙ F ≅ F                                   : functor.left_unitor _
      ... ≅ F ⋙ 𝟭 D                                     : (functor.right_unitor _).symm
      ... ≅ F ⋙ shift_functor D (0 : A)                 :
              iso_whisker_left F (shift_functor_zero D A).symm
      ... ≅ s 0 ⋙ F                                     : (i 0).symm),
  μ := λ a b, nat_iso_of_comp_fully_faithful F
    (calc (s a ⋙ s b) ⋙ F ≅ s a ⋙ s b ⋙ F             : functor.associator _ _ _
     ... ≅ s a ⋙ F ⋙ shift_functor D b                 : iso_whisker_left _ (i b)
     ... ≅ (s a ⋙ F) ⋙ shift_functor D b               : (functor.associator _ _ _).symm
     ... ≅ (F ⋙ shift_functor D a) ⋙ shift_functor D b : iso_whisker_right (i a) _
     ... ≅ F ⋙ shift_functor D a ⋙ shift_functor D b   : functor.associator _ _ _
     ... ≅ F ⋙ shift_functor D (a + b)                  :
             iso_whisker_left _ (shift_functor_add D a b).symm
     ... ≅ s (a + b) ⋙ F                                : (i (a + b)).symm),
  associativity := begin
    intros, apply F.map_injective, dsimp,
    simp only [category.comp_id, category.id_comp, category.assoc,
      category_theory.functor.map_comp, functor.image_preimage,
       eq_to_hom_map, iso.inv_hom_id_app_assoc],
    erw (i m₃).hom.naturality_assoc,
    congr' 1,
    dsimp,
    simp only [eq_to_iso.inv, eq_to_hom_app, eq_to_hom_map, obj_μ_app, μ_naturality_assoc,
      category.assoc, category_theory.functor.map_comp, functor.image_preimage],
    congr' 3,
    dsimp,
    simp only [←(shift_functor D m₃).map_comp_assoc, iso.inv_hom_id_app],
    erw [(shift_functor D m₃).map_id, category.id_comp],
    erw [((shift_monoidal_functor D A).μ_iso ⟨m₁ + m₂⟩ ⟨m₃⟩).inv_hom_id_app_assoc],
    congr' 1,
    have := dcongr_arg (λ a, (i a).inv.app X) (add_assoc m₁ m₂ m₃),
    dsimp at this,
    simp [this],
  end,
  left_unitality := begin
    intros, apply F.map_injective, dsimp,
    simp only [category.comp_id, category.id_comp, category.assoc, category_theory.functor.map_comp,
      eq_to_hom_app, eq_to_hom_map, functor.image_preimage],
    erw (i n).hom.naturality_assoc,
    dsimp,
    simp only [eq_to_iso.inv, eq_to_hom_app, category.assoc, category_theory.functor.map_comp,
      eq_to_hom_map, obj_ε_app, functor.image_preimage],
    simp only [←(shift_functor D n).map_comp_assoc, iso.inv_hom_id_app],
    dsimp,
    simp only [category.id_comp, μ_inv_hom_app_assoc, category_theory.functor.map_id],
    have := dcongr_arg (λ a, (i a).inv.app X) (zero_add n),
    dsimp at this,
    simp [this],
  end,
  right_unitality := begin
    intros, apply F.map_injective, dsimp,
    simp only [category.comp_id, category.id_comp, category.assoc,
      iso.inv_hom_id_app_assoc, eq_to_iso.inv, eq_to_hom_app, eq_to_hom_map,
      category_theory.functor.map_comp, functor.image_preimage,
      obj_zero_map_μ_app, ε_hom_inv_app_assoc],
    have := dcongr_arg (λ a, (i a).inv.app X) (add_zero n),
    dsimp at this,
    simp [this],
  end, }

end

/-- When we construct shifts on a subcategory from shifts on the ambient category,
the inclusion functor intertwines the shifts. -/
@[nolint unused_arguments] -- incorrectly reports that `[full F]` and `[faithful F]` are unused.
def has_shift_of_fully_faithful_comm
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shift_functor D i) (m : A) :
  begin
    haveI := has_shift_of_fully_faithful F s i,
    exact (shift_functor C m) ⋙ F ≅ F ⋙ shift_functor D m
  end :=
i m

end category_theory
