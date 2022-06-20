/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.products
import category_theory.limits.shapes.terminal

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/

universes w v u

open category_theory
open_locale classical

namespace category_theory.limits

variables (C : Type u) [category.{v} C]

/--
A category has finite products if there is a chosen limit for every diagram
with shape `discrete J`, where we have `[fintype J]`.
-/
-- We can't simply make this an abbreviation, as we do with other `has_Xs` limits typeclasses,
-- because of https://github.com/leanprover-community/lean/issues/429
class has_finite_products : Prop :=
(out (J : Type) [fintype J] : has_limits_of_shape (discrete J) C)

instance has_limits_of_shape_discrete
  (J : Type) [fintype J] [has_finite_products C] :
  has_limits_of_shape (discrete J) C :=
by { haveI := @has_finite_products.out C _ _ J, apply_instance }

/-- If `C` has finite limits then it has finite products. -/
@[priority 10]
instance has_finite_products_of_has_finite_limits [has_finite_limits C] :
  has_finite_products C :=
⟨λ J 𝒥, by { resetI, apply_instance }⟩

instance has_fintype_products [has_finite_products C] (ι : Type w) [fintype ι] :
  has_limits_of_shape (discrete ι) C :=
has_limits_of_shape_of_equivalence
  (discrete.equivalence
    ((show ulift.{0} (fin (fintype.card ι)) ≃ fin (fintype.card ι), by tidy).trans
      (fintype.equiv_fin ι).symm))

/-- We can now write this for powers. -/
noncomputable example [has_finite_products C] (X : C) : C := ∏ (λ (i : fin 5), X)

/--
If a category has all products then in particular it has finite products.
-/
lemma has_finite_products_of_has_products [has_products.{w} C] : has_finite_products C :=
⟨λ J _, has_limits_of_shape_of_equivalence (discrete.equivalence (equiv.ulift.{w}))⟩

/--
A category has finite coproducts if there is a chosen colimit for every diagram
with shape `discrete J`, where we have `[fintype J]`.
-/
class has_finite_coproducts : Prop :=
(out (J : Type) [fintype J] : has_colimits_of_shape (discrete J) C)

attribute [class] has_finite_coproducts

instance has_colimits_of_shape_discrete
  (J : Type) [fintype J] [has_finite_coproducts C] :
  has_colimits_of_shape (discrete J) C :=
by { haveI := @has_finite_coproducts.out C _ _ J, apply_instance }

/-- If `C` has finite colimits then it has finite coproducts. -/
@[priority 10]
instance has_finite_coproducts_of_has_finite_colimits [has_finite_colimits C] :
  has_finite_coproducts C :=
⟨λ J 𝒥, by { resetI, apply_instance }⟩

instance has_fintype_coproducts [has_finite_coproducts C] (ι : Type w) [fintype ι] :
  has_colimits_of_shape (discrete ι) C :=
has_colimits_of_shape_of_equivalence
  (discrete.equivalence
    ((show ulift.{0} (fin (fintype.card ι)) ≃ fin (fintype.card ι), by tidy).trans
      (fintype.equiv_fin ι).symm))

/--
If a category has all coproducts then in particular it has finite coproducts.
-/
lemma has_finite_coproducts_of_has_coproducts [has_coproducts.{w} C] : has_finite_coproducts C :=
⟨λ J _, has_colimits_of_shape_of_equivalence (discrete.equivalence (equiv.ulift.{w}))⟩

end category_theory.limits
