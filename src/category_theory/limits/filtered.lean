/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.filtered
import category_theory.limits.has_limits

/-!
# Possession of filtered colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universes w' w v u

noncomputable theory

open category_theory

variables {C : Type u} [category.{v} C]

namespace category_theory.limits

section
variables (C)

/-- Class for having all cofiltered limits of a given size. -/
class has_cofiltered_limits_of_size : Prop :=
(has_limits_of_shape : Π (I : Type w) [category.{w'} I] [is_cofiltered I], has_limits_of_shape I C)

/-- Class for having all filtered colimits of a given size. -/
class has_filtered_colimits_of_size : Prop :=
(has_colimits_of_shape : Π (I : Type w) [category.{w'} I] [is_filtered I],
  has_colimits_of_shape I C)

end

@[priority 100]
instance has_limits_of_shape_of_has_cofiltered_limits [has_cofiltered_limits_of_size.{w' w} C]
  (I : Type w) [category.{w'} I] [is_cofiltered I] : has_limits_of_shape I C :=
has_cofiltered_limits_of_size.has_limits_of_shape _

@[priority 100]
instance has_colimits_of_shape_of_has_filtered_colimits [has_filtered_colimits_of_size.{w' w} C]
  (I : Type w) [category.{w'} I] [is_filtered I] : has_colimits_of_shape I C :=
has_filtered_colimits_of_size.has_colimits_of_shape _

end category_theory.limits
