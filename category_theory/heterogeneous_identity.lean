-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.isomorphism

universes u v

namespace category_theory

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y := by rw p

@[simp,ematch] lemma eq_to_iso_refl (X : C) (p : X = X) : eq_to_iso p = (iso.refl X) := rfl

@[simp,ematch] lemma eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : (eq_to_iso p) ≪≫ (eq_to_iso q) = eq_to_iso (p.trans q) :=
begin /- obviously' says: -/ ext, induction q, induction p, dsimp at *, simp at * end
end

namespace functor

universes u₁ v₁ u₂ v₂

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma eq_to_iso (F : C ↝ D) {X Y : C} (p : X = Y) : F.on_isos (eq_to_iso p) = eq_to_iso (congr_arg F.obj p) :=
begin /- obviously says: -/ ext1, induction p, dsimp at *, simp at * end
end functor
end category_theory

