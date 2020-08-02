/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.Group.basic
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
The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroup :=
{ obj := λ α, of (free_abelian_group α),
  map := λ X Y f, add_monoid_hom.of (λ x : free_abelian_group X, f <$> x),
  map_id' := λ X, add_monoid_hom.ext $ by simp [types_id],
  map_comp' := λ X Y Z f g, add_monoid_hom.ext $
    by { intro x, simp [is_lawful_functor.comp_map, types_comp], } }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = (free_abelian_group α) := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} (x : free_abelian_group α) :
  (free.map f) x = f <$> x := rfl

/--
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ forget AddCommGroup.{u} :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X G, free_abelian_group.hom_equiv X G,
  hom_equiv_naturality_left_symm' :=
  by { intros, ext, simp [types_comp, free_abelian_group.lift_comp], } }

/--
As an example, we now give a high-powered proof that
the monomorphisms in `AddCommGroup` are just the injective functions.

(This proof works in all universes.)
-/
example {G H : AddCommGroup.{u}} (f : G ⟶ H) [mono f] : function.injective f :=
(mono_iff_injective f).1 (right_adjoint_preserves_mono adj (by apply_instance : mono f))

end AddCommGroup
