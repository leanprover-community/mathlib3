/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import category_theory.opposites
import category_theory.discrete_category

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

section

-- TODO: move deccidable eq and fintype instances to opposite file
local attribute [semireducible] opposite -- cheating a bit.

noncomputable
instance fin_category_op (J : Type v) [small_category J] [fin_category J] : fin_category Jᵒᵖ :=
{ decidable_eq_obj := by {unfold opposite, apply_instance},
  fintype_obj := by {unfold opposite, apply_instance},
  fintype_hom := λ a b, let ff : (a ⟶ b) → (b.unop ⟶ a.unop) := λ f, f.unop in
    fintype.of_injective ff has_hom.hom.unop_inj }

end

end category_theory
