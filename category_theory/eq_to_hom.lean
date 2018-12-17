-- Copyright (c) 2018 Reid Barton. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Reid Barton, Scott Morrison

import category_theory.isomorphism

universes u v

namespace category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def eq_to_hom {X Y : C} (p : X = Y) : X ⟶ Y := by rw p; exact 𝟙 _

@[simp] lemma eq_to_hom_refl (X : C) (p : X = X) : eq_to_hom p = 𝟙 X := rfl
@[simp] lemma eq_to_hom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_hom p ≫ eq_to_hom q = eq_to_hom (p.trans q) :=
by cases p; cases q; simp

def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y :=
⟨eq_to_hom p, eq_to_hom p.symm, by simp, by simp⟩

@[simp] lemma eq_to_iso.hom {X Y : C} (p : X = Y) : (eq_to_iso p).hom = eq_to_hom p :=
rfl

@[simp] lemma eq_to_iso_refl (X : C) (p : X = X) : eq_to_iso p = iso.refl X := rfl
@[simp] lemma eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
  eq_to_iso p ≪≫ eq_to_iso q = eq_to_iso (p.trans q) :=
by ext; simp

namespace functor

universes u₁ v₁ u₂ v₂

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

@[simp] lemma eq_to_iso (F : C ⥤ D) {X Y : C} (p : X = Y) :
  F.on_iso (eq_to_iso p) = eq_to_iso (congr_arg F.obj p) :=
by ext; cases p; simp
end functor

end category_theory
