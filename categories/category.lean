-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

namespace categories

meta def obviously : tactic unit := `[all_goals { sorry }]  -- This is a placeholder for automation.

universes u

class category (Obj : Type u) :=
  (Hom : Obj → Obj → Type u)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f . obviously)
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f . obviously)
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) . obviously)

variable {C : Type u}
variables {W X Y Z : C}
variable [category C]

def Hom : C → C → Type u := category.Hom

notation `𝟙` := category.identity
infixr ` >> `:80 := category.compose

@[simp] def category.left_identity_lemma (f : Hom X Y) : 𝟙 X >> f = f := by rw category.left_identity
@[simp] def category.right_identity_lemma (f : Hom X Y) : f >> 𝟙 Y = f := by rw category.right_identity
@[simp,ematch] def category.associativity_lemma (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) : (f >> g) >> h = f >> (g >> h) := by rw category.associativity

@[ematch] lemma category.identity_idempotent (X : C) : 𝟙 X >> 𝟙 X = 𝟙 X := by simp

end categories
