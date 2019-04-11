-- Copyright (c) 2019 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import topology.basic
import topology.algebra.ring
import ring_theory.subring

universes u v

instance continuous_submonoid (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem :=
  begin
    dsimp [has_one.one, monoid.one],
    exact continuous_const,
  end,
  mul_mem := λ f g fc gc,
  begin
    have q := continuous.comp (continuous.prod_mk fc gc) (topological_monoid.continuous_mul β),
    exact q,
  end }.

instance continuous_subring (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : is_subring { f : α → β | continuous f } :=
{ zero_mem :=
  begin
    dsimp [has_zero.zero, add_group.zero, add_monoid.zero, add_comm_group.zero, ring.zero],
    exact continuous_const,
  end,
  add_mem := λ f g fc gc,
  begin
    have q := continuous.comp (continuous.prod_mk fc gc) (topological_add_monoid.continuous_add β),
    exact q,
  end,
  neg_mem := λ f fc,
  begin
    have q := continuous.comp fc (topological_ring.continuous_neg β),
    exact q,
  end,
  ..continuous_submonoid α β }.

instance continuous_monoid {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : monoid { f : α → β | continuous f } :=
subtype.monoid

instance continuous_ring {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring { f : α → β | continuous f } :=
@subtype.ring _ _ _ (continuous_subring α β) -- infer_instance doesn't work?!

instance continuous_comm_ring {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [comm_ring β] [topological_ring β] : comm_ring { f : α → β | continuous f } :=
@subtype.comm_ring _ _ _ (continuous_subring α β) -- infer_instance doesn't work?!
