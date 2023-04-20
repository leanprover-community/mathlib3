/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yaël Dillies
-/
import algebra.order.group.type_tags
import analysis.normed_space.basic

/-!
# Ordered normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

open filter set
open_locale topology

variables {α : Type*}

/-- A `normed_ordered_add_group` is an additive group that is both a `normed_add_comm_group` and an
`ordered_add_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
class normed_ordered_add_group (α : Type*)
  extends ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = ‖x - y‖ . obviously)

/-- A `normed_ordered_group` is a group that is both a `normed_comm_group` and an
`ordered_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class normed_ordered_group (α : Type*) extends ordered_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = ‖x / y‖ . obviously)

/-- A `normed_linear_ordered_add_group` is an additive group that is both a `normed_add_comm_group`
and a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds caused by both
classes carrying their own group structure. -/
class normed_linear_ordered_add_group (α : Type*)
  extends linear_ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = ‖x - y‖ . obviously)

/-- A `normed_linear_ordered_group` is a group that is both a `normed_comm_group` and a
`linear_ordered_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class normed_linear_ordered_group (α : Type*)
  extends linear_ordered_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = ‖x / y‖ . obviously)

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type*)
extends linear_ordered_field α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = ‖x - y‖ . obviously)
(norm_mul' : ∀ x y : α, ‖x * y‖ = ‖x‖ * ‖y‖)

@[to_additive, priority 100]
instance normed_ordered_group.to_normed_comm_group [normed_ordered_group α] : normed_comm_group α :=
⟨normed_ordered_group.dist_eq⟩

@[to_additive, priority 100]
instance normed_linear_ordered_group.to_normed_ordered_group [normed_linear_ordered_group α] :
  normed_ordered_group α :=
⟨normed_linear_ordered_group.dist_eq⟩

@[priority 100] instance normed_linear_ordered_field.to_normed_field (α : Type*)
  [normed_linear_ordered_field α] : normed_field α :=
{ dist_eq := normed_linear_ordered_field.dist_eq,
  norm_mul' := normed_linear_ordered_field.norm_mul' }

instance : normed_linear_ordered_field ℚ :=
⟨dist_eq_norm, norm_mul⟩

noncomputable
instance : normed_linear_ordered_field ℝ :=
⟨dist_eq_norm, norm_mul⟩

@[to_additive] instance [normed_ordered_group α] : normed_ordered_group αᵒᵈ :=
{ ..normed_ordered_group.to_normed_comm_group, ..order_dual.ordered_comm_group }

@[to_additive] instance [normed_linear_ordered_group α] : normed_linear_ordered_group αᵒᵈ :=
{ ..order_dual.normed_ordered_group, ..order_dual.linear_order _ }

instance [normed_ordered_group α] : normed_ordered_add_group (additive α) :=
{ ..additive.normed_add_comm_group }

instance [normed_ordered_add_group α] : normed_ordered_group (multiplicative α) :=
{ ..multiplicative.normed_comm_group }

instance [normed_linear_ordered_group α] : normed_linear_ordered_add_group (additive α) :=
{ ..additive.normed_add_comm_group }

instance [normed_linear_ordered_add_group α] : normed_linear_ordered_group (multiplicative α) :=
{ ..multiplicative.normed_comm_group }
