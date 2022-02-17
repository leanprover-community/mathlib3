/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.basic

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

set_option old_structure_cmd true

open filter set
open_locale topological_space

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_group (α : Type*)
extends linear_ordered_add_comm_group α, has_norm α, metric_space α, normed_group α

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type*)
extends linear_ordered_field α, has_norm α, metric_space α, normed_field α,
  normed_linear_ordered_group α

noncomputable
instance : normed_linear_ordered_field ℚ :=
{ .. rat.linear_ordered_field, .. rat.normed_field }

noncomputable
instance : normed_linear_ordered_field ℝ :=
{ .. real.linear_ordered_field, .. real.normed_field }
