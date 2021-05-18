/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import algebraic_topology.simplex_category
import category_theory.category.ulift
import category_theory.limits.functor_category
import category_theory.opposites
import category_theory.adjunction.limits
import category_theory.comma

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `simplex_category`.
(Similarly a cosimplicial object is functor `simplex_category ⥤ C`.)

Use the notation `X _[n]` in the `simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

-/

open opposite
open category_theory
open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[derive category, nolint has_inhabited_instance]
def simplicial_object := simplex_category.{v}ᵒᵖ ⥤ C

namespace simplicial_object

localized
  "notation X `_[`:1000 n `]` :=
    (X : category_theory.simplicial_object _).obj (opposite.op (simplex_category.mk n))"
  in simplicial

instance {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object C) := by {dsimp [simplicial_object], apply_instance}

instance [has_limits C] : has_limits (simplicial_object C) := ⟨infer_instance⟩

instance {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object C) := by {dsimp [simplicial_object], apply_instance}

instance [has_colimits C] : has_colimits (simplicial_object C) := ⟨infer_instance⟩

variables {C} (X : simplicial_object C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : fin (n+2)) : X _[n+1] ⟶ X _[n] :=
X.map (simplex_category.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : fin (n+1)) : X _[n] ⟶ X _[n+1] :=
X.map (simplex_category.σ i).op


/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
X.map_iso (eq_to_iso (by rw h))

@[simp] lemma eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
by { ext, simp [eq_to_iso], }


/-- The generic case of the first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ H] }

/-- The special case of the first simplicial identity -/
lemma δ_comp_δ_self {n} {i : fin (n+2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ_self] }

/-- The second simplicial identity -/
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_le H] }

/-- The first part of the third simplicial identity -/
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_self, op_id, X.map_id],
end

/-- The second part of the third simplicial identity -/
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_succ, op_id, X.map_id],
end

/-- The fourth simplicial identity -/
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_gt H] }

/-- The fifth simplicial identity -/
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.σ_comp_σ H] }

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ simplicial_object C ⥤ simplicial_object D :=
whiskering_right _ _ _

/-- Truncated simplicial objects. -/
@[derive category, nolint has_inhabited_instance]
def truncated (n : ℕ) := (simplex_category.truncated.{v} n)ᵒᵖ ⥤ C

variable {C}

namespace truncated

instance {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object.truncated C n) := by {dsimp [truncated], apply_instance}

instance {n} [has_limits C] : has_limits (simplicial_object.truncated C n) := ⟨infer_instance⟩

instance {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_colimits C] : has_colimits (simplicial_object.truncated C n) := ⟨infer_instance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
whiskering_right _ _ _

variable {C}

end truncated

section skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : simplicial_object C ⥤ simplicial_object.truncated C n :=
(whiskering_left _ _ _).obj simplex_category.truncated.inclusion.op

end skeleton

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbreviation const : C ⥤ simplicial_object C := category_theory.functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
@[derive category, nolint has_inhabited_instance]
def augmented := comma (𝟭 (simplicial_object C)) (const C)

variable {C}

namespace augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ simplicial_object C := comma.fst _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C := comma.snd _ _

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskering_obj (D : Type*) [category.{v} D] (F : C ⥤ D) :
  augmented C ⥤ augmented D :=
{ obj := λ X,
  { left := ((whiskering _ _).obj F).obj (drop.obj X),
    right := F.obj (point.obj X),
    hom := whisker_right X.hom F ≫ (functor.const_comp _ _ _).hom },
  map := λ X Y η,
  { left := whisker_right η.left _,
    right := F.map η.right,
    w' := begin
      ext,
      dsimp,
      erw [category.comp_id, category.comp_id, ← F.map_comp,
        ← F.map_comp, ← nat_trans.comp_app, η.w],
      refl,
    end } }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
{ obj := whiskering_obj _ _,
  map := λ X Y η,
  { app := λ A,
    { left := whisker_left _ η,
      right := η.app _ } } }

variable {C}

end augmented

end simplicial_object

/-- Cosimplicial objects. -/
@[derive category, nolint has_inhabited_instance]
def cosimplicial_object := simplex_category.{v} ⥤ C

namespace cosimplicial_object

localized
  "notation X `_[`:1000 n `]` :=
    (X : category_theory.cosimplicial_object _).obj (simplex_category.mk n)"
  in simplicial

instance {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (cosimplicial_object C) := by {dsimp [cosimplicial_object], apply_instance}

instance [has_limits C] : has_limits (cosimplicial_object C) := ⟨infer_instance⟩

instance {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object C) :=
by {dsimp [cosimplicial_object], apply_instance}

instance [has_colimits C] : has_colimits (cosimplicial_object C) := ⟨infer_instance⟩

variables {C} (X : cosimplicial_object C)

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : fin (n+2)) : X _[n] ⟶ X _[n+1] :=
X.map (simplex_category.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : fin (n+1)) : X _[n+1] ⟶ X _[n] :=
X.map (simplex_category.σ i)

/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
X.map_iso (eq_to_iso (by rw h))

@[simp] lemma eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
by { ext, simp [eq_to_iso], }


/-- The generic case of the first cosimplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ :=
by { dsimp [δ], simp only [←X.map_comp, simplex_category.δ_comp_δ H], }

/-- The special case of the first cosimplicial identity -/
lemma δ_comp_δ_self {n} {i : fin (n+2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ :=
by { dsimp [δ], simp only [←X.map_comp, simplex_category.δ_comp_δ_self] }

/-- The second cosimplicial identity -/
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.δ_comp_σ_of_le H] }

/-- The first part of the third cosimplicial identity -/
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  X.δ i.cast_succ ≫ X.σ i = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, simplex_category.δ_comp_σ_self, X.map_id],
end

/-- The second part of the third cosimplicial identity -/
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  X.δ i.succ ≫ X.σ i = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, simplex_category.δ_comp_σ_succ, X.map_id],
end

/-- The fourth cosimplicial identity -/
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.δ_comp_σ_of_gt H] }

/-- The fifth cosimplicial identity -/
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.σ_comp_σ H] }

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ cosimplicial_object C ⥤ cosimplicial_object D :=
whiskering_right _ _ _

/-- Truncated cosimplicial objects. -/
@[derive category, nolint has_inhabited_instance]
def truncated (n : ℕ) := simplex_category.truncated.{v} n ⥤ C

variable {C}

namespace truncated

instance {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (cosimplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_limits C] : has_limits (cosimplicial_object.truncated C n) := ⟨infer_instance⟩

instance {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_colimits C] : has_colimits (cosimplicial_object.truncated C n) := ⟨infer_instance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
whiskering_right _ _ _

variable {C}

end truncated

section skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : cosimplicial_object C ⥤ cosimplicial_object.truncated C n :=
(whiskering_left _ _ _).obj simplex_category.truncated.inclusion

end skeleton

variable (C)

/-- The constant cosimplicial object. -/
abbreviation const : C ⥤ cosimplicial_object C := category_theory.functor.const _

/-- Augmented cosimplicial objects. -/
@[derive category, nolint has_inhabited_instance]
def augmented := comma (const C) (𝟭 (cosimplicial_object C))

variable {C}

namespace augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ cosimplicial_object C := comma.snd _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C := comma.fst _ _

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskering_obj (D : Type*) [category.{v} D] (F : C ⥤ D) :
  augmented C ⥤ augmented D :=
{ obj := λ X,
  { left := F.obj (point.obj X),
    right := ((whiskering _ _).obj F).obj (drop.obj X),
    hom := (functor.const_comp _ _ _).inv ≫ whisker_right X.hom F },
  map := λ X Y η,
  { left := F.map η.left,
    right := whisker_right η.right _,
    w' := begin
      ext,
      dsimp,
      erw [category.id_comp, category.id_comp, ← F.map_comp,
        ← F.map_comp, ← nat_trans.comp_app, ← η.w],
      refl,
    end } }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type*) [category.{v} D] :
  (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
{ obj := whiskering_obj _ _,
  map := λ X Y η,
  { app := λ A,
    { left := η.app _,
      right := whisker_left _ η } } }

variable {C}

end augmented

end cosimplicial_object

end category_theory
