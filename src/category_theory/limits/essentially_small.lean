/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.products
import category_theory.essentially_small

/-!
# Limits over essentially small indexing categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `C` has limits of size `w` and `J` is `w`-essentially small, then `C` has limits of shape `J`.

-/

universes w₁ w₂ v₁ v₂ u₁ u₂

noncomputable theory

open category_theory

namespace category_theory.limits
variables (J : Type u₂) [category.{v₂} J] (C : Type u₁) [category.{v₁} C]

lemma has_limits_of_shape_of_essentially_small [essentially_small.{w₁} J]
  [has_limits_of_size.{w₁ w₁} C] : has_limits_of_shape J C :=
has_limits_of_shape_of_equivalence $ equivalence.symm $ equiv_small_model.{w₁} J

lemma has_colimits_of_shape_of_essentially_small [essentially_small.{w₁} J]
  [has_colimits_of_size.{w₁ w₁} C] : has_colimits_of_shape J C :=
has_colimits_of_shape_of_equivalence $ equivalence.symm $ equiv_small_model.{w₁} J

lemma has_products_of_shape_of_small (β : Type w₂) [small.{w₁} β] [has_products.{w₁} C] :
  has_products_of_shape β C :=
has_limits_of_shape_of_equivalence $ discrete.equivalence $ equiv.symm $ equiv_shrink β

lemma has_coproducts_of_shape_of_small (β : Type w₂) [small.{w₁} β] [has_coproducts.{w₁} C] :
  has_coproducts_of_shape β C :=
has_colimits_of_shape_of_equivalence $ discrete.equivalence $ equiv.symm $ equiv_shrink β

end category_theory.limits
