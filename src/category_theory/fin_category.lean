/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.fintype.basic
import category_theory.discrete_category
import category_theory.opposites
import category_theory.category.ulift

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

/--
If `K` is a finite category, and `F : J ⥤ K` is a faithful functor which is injective on objects,
then `J` is a finite category as well.
-/
noncomputable
def fin_category_of_injective_faithful {J K : Type v} [small_category J] [small_category K]
  (F : J ⥤ K) (inj : function.injective F.obj) [faithful F] [fin_category K] : fin_category J :=
{ decidable_eq_obj := by {classical, apply_instance},
  fintype_obj := fintype.of_injective _ inj,
  decidable_eq_hom := by {classical, apply_instance},
  fintype_hom := λ j j', fintype.of_injective (λ f : (j ⟶ j'), F.map f) F.map_injective }

noncomputable
instance {J : Type v} [small_category J] [fin_category J] : fin_category Jᵒᵖ :=
{ decidable_eq_obj := by {classical, apply_instance},
  fintype_obj := fintype.of_injective opposite.unop (by tidy),
  fintype_hom := λ j j', fintype.of_injective (λ f, f.unop) has_hom.hom.unop_inj }

instance {J : Type v} [small_category J] [fin_category J] : fin_category (ulift'.{u} J) :=
{ fintype_obj := by {unfold ulift', apply_instance} }

end category_theory
