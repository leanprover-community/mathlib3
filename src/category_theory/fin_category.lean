/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import category_theory.discrete_category
import category_theory.opposites

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation

We also ask for decidable equality of objects and morphisms, but it may be reasonable to just
go classical in future.
-/

universes v u

namespace category_theory

instance discrete_fintype {α : Type*} [fintype α] : fintype (discrete α) :=
by { dsimp [discrete], apply_instance }

instance discrete_hom_fintype {α : Type*} [decidable_eq α] (X Y : discrete α) : fintype (X ⟶ Y) :=
by { apply ulift.fintype }

/-- A category with a `fintype` of objects, and a `fintype` for each morphism space. -/
class fin_category (J : Type v) [small_category J] :=
(decidable_eq_obj : decidable_eq J . tactic.apply_instance)
(fintype_obj : fintype J . tactic.apply_instance)
(decidable_eq_hom : Π (j j' : J), decidable_eq (j ⟶ j') . tactic.apply_instance)
(fintype_hom : Π (j j' : J), fintype (j ⟶ j') . tactic.apply_instance)

attribute [instance] fin_category.decidable_eq_obj fin_category.fintype_obj
                     fin_category.decidable_eq_hom fin_category.fintype_hom

-- We need a `decidable_eq` instance here to construct `fintype` on the morphism spaces.
instance fin_category_discrete_of_decidable_fintype (J : Type v) [decidable_eq J] [fintype J] :
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

/-- The constructed category (`as_type α`) is equivalent to `obj_as_type α`. -/
noncomputable
def obj_as_type_equiv_as_type : as_type α ≌ obj_as_type α :=
{ functor := { obj := id, map := λ i j f, (fintype.equiv_fin _).symm f,
    map_comp' := λ _ _ _ _ _, by { dsimp, simp } },
  inverse := { obj := id, map := λ i j f, fintype.equiv_fin _ f,
    map_comp' := λ _ _ _ _ _, by { dsimp, simp }  },
  unit_iso := nat_iso.of_components iso.refl (λ _ _ _, by { dsimp, simp }),
  counit_iso := nat_iso.of_components iso.refl (λ _ _ _, by { dsimp, simp }) }

noncomputable
instance as_type_fin_category : fin_category (as_type α) := {}

/-- The constructed category (`as_type α`) is indeed equivalent to `α`. -/
noncomputable def equiv_as_type : as_type α ≌ α :=
(obj_as_type_equiv_as_type α).trans (obj_as_type_equiv α)

end fin_category

open opposite

/--
The opposite of a finite category is finite.
-/
instance fin_category_opposite {J : Type v} [small_category J] [fin_category J] :
  fin_category Jᵒᵖ :=
{ decidable_eq_obj := equiv.decidable_eq equiv_to_opposite.symm,
  fintype_obj := fintype.of_equiv _ equiv_to_opposite,
  decidable_eq_hom := λ j j', equiv.decidable_eq (op_equiv j j'),
  fintype_hom := λ j j', fintype.of_equiv _ (op_equiv j j').symm, }

end category_theory
