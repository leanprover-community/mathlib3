/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.generator
import category_theory.limits.cone_category
import category_theory.limits.constructions.weakly_initial
import category_theory.limits.functor_category
import category_theory.subobject.comma

/-!
# Adjoint functor theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the (general) adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` has limits, and satisfies the solution set condition,
  then it has a left adjoint: `is_right_adjoint_of_preserves_limits_of_solution_set_condition`.

We show that the converse holds, i.e. that if `G` has a left adjoint then it satisfies the solution
set condition, see `solution_set_condition_of_is_right_adjoint`
(the file `category_theory/adjunction/limits` already shows it preserves limits).

We define the *solution set condition* for the functor `G : D ⥤ C` to mean, for every object
`A : C`, there is a set-indexed family ${f_i : A ⟶ G (B_i)}$ such that any morphism `A ⟶ G X`
factors through one of the `f_i`.

This file also proves the special adjoint functor theorem, in the form:
* If `G : D ⥤ C` preserves limits and `D` is complete, well-powered and has a small coseparating
  set, then `G` has a left adjoint: `is_right_adjoint_of_preserves_limits_of_is_coseparating`

Finally, we prove the following corollary of the special adjoint functor theorem:
* If `C` is complete, well-powered and has a small coseparating set, then it is cocomplete:
  `has_colimits_of_has_limits_of_is_coseparating`

-/
universes v u u'

namespace category_theory
open limits

variables {J : Type v}
variables {C : Type u} [category.{v} C]

/--
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def solution_set_condition {D : Type u} [category.{v} D] (G : D ⥤ C) : Prop :=
∀ (A : C), ∃ (ι : Type v) (B : ι → D) (f : Π (i : ι), A ⟶ G.obj (B i)),
  ∀ X (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

section general_adjoint_functor_theorem
variables {D : Type u} [category.{v} D]

variables (G : D ⥤ C)

/-- If `G : D ⥤ C` is a right adjoint it satisfies the solution set condition.  -/
lemma solution_set_condition_of_is_right_adjoint [is_right_adjoint G] :
  solution_set_condition G :=
begin
  intros A,
  refine ⟨punit, λ _, (left_adjoint G).obj A, λ _, (adjunction.of_right_adjoint G).unit.app A, _⟩,
  intros B h,
  refine ⟨punit.star, ((adjunction.of_right_adjoint G).hom_equiv _ _).symm h, _⟩,
  rw [←adjunction.hom_equiv_unit, equiv.apply_symm_apply],
end

/--
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
if `G` satisfies the solution set condition then `G` is a right adjoint.
-/
noncomputable def is_right_adjoint_of_preserves_limits_of_solution_set_condition
  [has_limits D] [preserves_limits G] (hG : solution_set_condition G) :
  is_right_adjoint G :=
begin
  apply is_right_adjoint_of_structured_arrow_initials _,
  intro A,
  specialize hG A,
  choose ι B f g using hG,
  let B' : ι → structured_arrow A G := λ i, structured_arrow.mk (f i),
  have hB' : ∀ (A' : structured_arrow A G), ∃ i, nonempty (B' i ⟶ A'),
  { intros A',
    obtain ⟨i, _, t⟩ := g _ A'.hom,
    exact ⟨i, ⟨structured_arrow.hom_mk _ t⟩⟩ },
  obtain ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_has_products hB',
  apply has_initial_of_weakly_initial_and_has_wide_equalizers hT,
end

end general_adjoint_functor_theorem

section special_adjoint_functor_theorem
variables {D : Type u'} [category.{v} D]

/--
The special adjoint functor theorem: if `G : D ⥤ C` preserves limits and `D` is complete,
well-powered and has a small coseparating set, then `G` has a left adjoint.
-/
noncomputable def is_right_adjoint_of_preserves_limits_of_is_coseparating [has_limits D]
  [well_powered D] {𝒢 : set D} [small.{v} 𝒢] (h𝒢 : is_coseparating 𝒢) (G : D ⥤ C)
  [preserves_limits G] : is_right_adjoint G :=
have ∀ A, has_initial (structured_arrow A G),
  from λ A, has_initial_of_is_coseparating (structured_arrow.is_coseparating_proj_preimage A G h𝒢),
by exactI is_right_adjoint_of_structured_arrow_initials _

/--
The special adjoint functor theorem: if `F : C ⥤ D` preserves colimits and `C` is cocomplete,
well-copowered and has a small separating set, then `F` has a right adjoint.
-/
noncomputable def is_left_adjoint_of_preserves_colimits_of_is_separatig [has_colimits C]
  [well_powered Cᵒᵖ] {𝒢 : set C} [small.{v} 𝒢] (h𝒢 : is_separating 𝒢) (F : C ⥤ D)
  [preserves_colimits F] : is_left_adjoint F :=
have ∀ A, has_terminal (costructured_arrow F A),
  from λ A, has_terminal_of_is_separating (costructured_arrow.is_separating_proj_preimage F A h𝒢),
by exactI is_left_adjoint_of_costructured_arrow_terminals _

end special_adjoint_functor_theorem

namespace limits

/-- A consequence of the special adjoint functor theorem: if `C` is complete, well-powered and
    has a small coseparating set, then it is cocomplete. -/
lemma has_colimits_of_has_limits_of_is_coseparating [has_limits C] [well_powered C]
  {𝒢 : set C} [small.{v} 𝒢] (h𝒢 : is_coseparating 𝒢) : has_colimits C :=
{ has_colimits_of_shape := λ J hJ, by exactI has_colimits_of_shape_iff_is_right_adjoint_const.2
    ⟨is_right_adjoint_of_preserves_limits_of_is_coseparating h𝒢 _⟩ }

/-- A consequence of the special adjoint functor theorem: if `C` is cocomplete, well-copowered and
    has a small separating set, then it is complete. -/
lemma has_limits_of_has_colimits_of_is_separating [has_colimits C] [well_powered Cᵒᵖ]
  {𝒢 : set C} [small.{v} 𝒢] (h𝒢 : is_separating 𝒢) : has_limits C :=
{ has_limits_of_shape := λ J hJ, by exactI has_limits_of_shape_iff_is_left_adjoint_const.2
    ⟨is_left_adjoint_of_preserves_colimits_of_is_separatig h𝒢 _⟩ }

end limits

end category_theory
