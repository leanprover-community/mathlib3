/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.card
import category_theory.discrete_category
import category_theory.opposites
import category_theory.category.ulift

/-!
# Finite categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to #14046, `fin_category` required a `decidable_eq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/

universes w v u
open_locale classical
noncomputable theory

namespace category_theory

instance discrete_fintype {α : Type*} [fintype α] : fintype (discrete α) :=
fintype.of_equiv α (discrete_equiv.symm)

instance discrete_hom_fintype {α : Type*} (X Y : discrete α) : fintype (X ⟶ Y) :=
by { apply ulift.fintype }

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category (J : Type v) [small_category J] :=
(fintype_obj : fintype J . tactic.apply_instance)
(fintype_hom : Π (j j' : J), fintype (j ⟶ j') . tactic.apply_instance)

attribute [instance] fin_category.fintype_obj fin_category.fintype_hom

instance fin_category_discrete_of_fintype (J : Type v) [fintype J] :
  fin_category (discrete J) :=
{ }

namespace fin_category
variables (α : Type*) [fintype α] [small_category α] [fin_category α]

/-- A fin_category `α` is equivalent to a category with objects in `Type`. -/
@[nolint unused_arguments]
abbreviation obj_as_type : Type := induced_category α (fintype.equiv_fin α).symm

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def obj_as_type_equiv : obj_as_type α ≌ α :=
(induced_functor (fintype.equiv_fin α).symm).as_equivalence

/-- A fin_category `α` is equivalent to a fin_category with in `Type`. -/
@[nolint unused_arguments] abbreviation as_type : Type := fin (fintype.card α)

@[simps hom id comp (lemmas_only)] noncomputable
instance category_as_type : small_category (as_type α) :=
{ hom := λ i j, fin (fintype.card (@quiver.hom (obj_as_type α) _ i j)),
  id := λ i, fintype.equiv_fin _ (𝟙 i),
  comp := λ i j k f g, fintype.equiv_fin _
    ((fintype.equiv_fin _).symm f ≫ (fintype.equiv_fin _).symm g) }

local attribute [simp] category_as_type_hom category_as_type_id
  category_as_type_comp

/-- The "identity" functor from `as_type α` to `obj_as_type α`. -/
@[simps] noncomputable def as_type_to_obj_as_type : as_type α ⥤ obj_as_type α :=
{ obj := id, map := λ i j, (fintype.equiv_fin _).symm }

/-- The "identity" functor from `obj_as_type α` to `as_type α`. -/
@[simps] noncomputable def obj_as_type_to_as_type : obj_as_type α ⥤ as_type α :=
{ obj := id, map := λ i j, fintype.equiv_fin _ }

/-- The constructed category (`as_type α`) is equivalent to `obj_as_type α`. -/
noncomputable def as_type_equiv_obj_as_type : as_type α ≌ obj_as_type α :=
equivalence.mk (as_type_to_obj_as_type α) (obj_as_type_to_as_type α)
  (nat_iso.of_components iso.refl $ λ _ _ _, by { dsimp, simp })
  (nat_iso.of_components iso.refl $ λ _ _ _, by { dsimp, simp })

noncomputable
instance as_type_fin_category : fin_category (as_type α) := {}

/-- The constructed category (`as_type α`) is indeed equivalent to `α`. -/
noncomputable def equiv_as_type : as_type α ≌ α :=
(as_type_equiv_obj_as_type α).trans (obj_as_type_equiv α)

end fin_category

open opposite

/--
The opposite of a finite category is finite.
-/
instance fin_category_opposite {J : Type v} [small_category J] [fin_category J] :
  fin_category Jᵒᵖ :=
{ fintype_obj := fintype.of_equiv _ equiv_to_opposite,
  fintype_hom := λ j j', fintype.of_equiv _ (op_equiv j j').symm, }

/-- Applying `ulift` to morphisms and objects of a category preserves finiteness. -/
instance fin_category_ulift {J : Type v} [small_category J] [fin_category J] :
  fin_category.{(max w v)} (ulift_hom.{w (max w v)} (ulift.{w v} J)) :=
{ fintype_obj := ulift.fintype J }

end category_theory
