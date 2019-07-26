/-
-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
-/
import category_theory.category

/-!
A sparse category is a category with at most one morphism between each pair of objects.

Examples include posets, but many indexing categories (diagrams) for special shapes
of (co)limits.

To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.
-/

universes u v

namespace category_theory

variables {C : Type u} [category_struct.{v} C]

/-- Construct a category instance from a category_struct, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
def sparse_category [∀ X Y : C, subsingleton (X ⟶ Y)] : category.{v} C := { }

end category_theory
