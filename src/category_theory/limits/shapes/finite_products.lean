/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.products

/-!
# Categories with finite (co)products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Typeclasses representing categories with (co)products over finite indexing types.
-/

universes w v u

open category_theory
open_locale classical

namespace category_theory.limits

variables (C : Type u) [category.{v} C]

/--
A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[finite J]`.

We require this condition only for `J = fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class has_finite_products : Prop :=
(out [] (n : ℕ) : has_limits_of_shape (discrete (fin n)) C)

/-- If `C` has finite limits then it has finite products. -/
@[priority 10]
instance has_finite_products_of_has_finite_limits [has_finite_limits C] :
  has_finite_products C :=
⟨λ n, infer_instance⟩

instance has_limits_of_shape_discrete [has_finite_products C] (ι : Type w) [finite ι] :
  has_limits_of_shape (discrete ι) C :=
begin
  rcases finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩,
  haveI := has_finite_products.out C n,
  exact has_limits_of_shape_of_equivalence (discrete.equivalence e.symm)
end

/-- We can now write this for powers. -/
noncomputable example [has_finite_products C] (X : C) : C := ∏ (λ (i : fin 5), X)

/--
If a category has all products then in particular it has finite products.
-/
lemma has_finite_products_of_has_products [has_products.{w} C] : has_finite_products C :=
⟨λ n, has_limits_of_shape_of_equivalence (discrete.equivalence equiv.ulift.{w})⟩

/--
A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[fintype J]`.

We require this condition only for `J = fin n` in the definition, then deduce a version for any
`J : Type*` as a corollary of this definition.
-/
class has_finite_coproducts : Prop :=
(out [] (n : ℕ) : has_colimits_of_shape (discrete (fin n)) C)

attribute [class] has_finite_coproducts

instance has_colimits_of_shape_discrete [has_finite_coproducts C] (ι : Type w) [finite ι] :
  has_colimits_of_shape (discrete ι) C :=
begin
  rcases finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩,
  haveI := has_finite_coproducts.out C n,
  exact has_colimits_of_shape_of_equivalence (discrete.equivalence e.symm)
end

/-- If `C` has finite colimits then it has finite coproducts. -/
@[priority 10]
instance has_finite_coproducts_of_has_finite_colimits [has_finite_colimits C] :
  has_finite_coproducts C :=
⟨λ J, by apply_instance⟩

/--
If a category has all coproducts then in particular it has finite coproducts.
-/
lemma has_finite_coproducts_of_has_coproducts [has_coproducts.{w} C] : has_finite_coproducts C :=
⟨λ J, has_colimits_of_shape_of_equivalence (discrete.equivalence (equiv.ulift.{w}))⟩

end category_theory.limits
