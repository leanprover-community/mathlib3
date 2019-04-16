-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import topology.basic
import topology.algebra.ring
import ring_theory.subring

universes u v

local attribute [elab_simple] continuous.comp

@[to_additive continuous_add_submonoid]
instance continuous_submonoid (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem := @continuous_const _ _ _ _ 1,
  mul_mem :=
  λ f g fc gc, continuous.comp (continuous.prod_mk fc gc) (topological_monoid.continuous_mul β) }.

@[to_additive continuous_add_subgroup]
instance continuous_subgroup (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [group β] [topological_group β] : is_subgroup { f : α → β | continuous f } :=
{ inv_mem := λ f fc, continuous.comp fc (topological_group.continuous_inv β),
  ..continuous_submonoid α β, }.

@[to_additive continuous_add_monoid]
instance continuous_monoid {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : monoid { f : α → β | continuous f } :=
subtype.monoid

@[to_additive continuous_add_group]
instance continuous_group {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group { f : α → β | continuous f } :=
subtype.group

instance continuous_subring (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : is_subring { f : α → β | continuous f } :=
{ ..continuous_add_subgroup α β,
  ..continuous_submonoid α β }.

instance continuous_ring {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring { f : α → β | continuous f } :=
@subtype.ring _ _ _ (continuous_subring α β) -- infer_instance doesn't work?!

instance continuous_comm_ring {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [comm_ring β] [topological_ring β] : comm_ring { f : α → β | continuous f } :=
@subtype.comm_ring _ _ _ (continuous_subring α β) -- infer_instance doesn't work?!
