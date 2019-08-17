/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.pempty

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

abbreviation terminal [has_limit (functor.empty C)] : C := limit (functor.empty C)
abbreviation initial [has_colimit (functor.empty C)] : C := colimit (functor.empty C)

section
variables {C}

abbreviation terminal.from [has_limit (functor.empty C)] (P : C) : P ⟶ terminal C :=
limit.lift (functor.empty C) { X := P, π := by tidy }.
abbreviation initial.to [has_colimit (functor.empty C)] (P : C) : initial C ⟶ P :=
colimit.desc (functor.empty C) { X := P, ι := by tidy }.

instance unique_to_terminal [has_limit (functor.empty C)] (P : C) : unique (P ⟶ terminal C) :=
{ default := terminal.from P,
  uniq := λ m,
  begin
    rw [is_limit.hom_lift infer_instance m],
    congr, funext j, cases j,
  end }

instance unique_from_initial [has_colimit (functor.empty C)] (P : C) : unique (initial C ⟶ P) :=
{ default := initial.to P,
  uniq := λ m,
  begin
    rw [is_colimit.hom_desc infer_instance m],
    congr, funext j, cases j,
  end }
end

class has_terminal :=
(has_limits_of_shape : has_limits_of_shape.{v} pempty C)
class has_initial :=
(has_colimits_of_shape : has_colimits_of_shape.{v} pempty C)

attribute [instance] has_terminal.has_limits_of_shape has_initial.has_colimits_of_shape

instance [has_finite_products.{v} C] : has_terminal.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F, has_limit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }
instance [has_finite_coproducts.{v} C] : has_initial.{v} C :=
{ has_colimits_of_shape :=
  { has_colimit := λ F, has_colimit_of_equivalence_comp ((functor.empty (discrete pempty)).as_equivalence.symm) } }

end category_theory.limits
