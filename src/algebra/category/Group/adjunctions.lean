/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.Group
import category_theory.adjunction.basic
import group_theory.free_abelian_group

/-!
The free abelian group on a type is the left adjoint of the
forgetful functor from abelian groups to types.
-/

noncomputable theory

universe u

open category_theory

namespace AddCommGroup

open_locale classical

/--
The free functor `Type u ⥤ AddCommGroup.{u}` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroup.{u} :=
{ obj := λ α, of (free_abelian_group α),
  map := λ X Y f, add_monoid_hom.of (λ x : free_abelian_group X, f <$> x),
  map_id' := λ X, add_monoid_hom.ext $ by simp,
  map_comp' := λ X Y Z f g, add_monoid_hom.ext $ by { intro x, simp [is_lawful_functor.comp_map], } }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = (free_abelian_group α) := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} (x : free_abelian_group α) :
  (free.map f) x = f <$> x := rfl

local attribute [ext] add_monoid_hom.ext -- TODO mark this globally?

/--
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroup :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_abelian_group.hom_equiv X G,
  hom_equiv_naturality_left_symm' := by {intros, ext, dsimp at *, simp,} }

end AddCommGroup
