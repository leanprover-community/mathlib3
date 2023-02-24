/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import topology.order.basic
import topology.extend_from

/-!
# Lemmas about `extend_from` in an order topology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open filter set topological_space
open_locale topology classical

universes u v
variables {α : Type u} {β : Type v}

lemma continuous_on_Icc_extend_from_Ioo [topological_space α] [linear_order α] [densely_ordered α]
  [order_topology α] [topological_space β] [regular_space β] {f : α → β} {a b : α}
  {la lb : β} (hab : a ≠ b) (hf : continuous_on f (Ioo a b))
  (ha : tendsto f (𝓝[>] a) (𝓝 la)) (hb : tendsto f (𝓝[<] b) (𝓝 lb)) :
  continuous_on (extend_from (Ioo a b) f) (Icc a b) :=
begin
  apply continuous_on_extend_from,
  { rw closure_Ioo hab },
  { intros x x_in,
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with rfl | rfl | h,
    { exact ⟨la, ha.mono_left $ nhds_within_mono _ Ioo_subset_Ioi_self⟩ },
    { exact ⟨lb, hb.mono_left $ nhds_within_mono _ Ioo_subset_Iio_self⟩ },
    { use [f x, hf x h] } }
end

lemma eq_lim_at_left_extend_from_Ioo [topological_space α] [linear_order α] [densely_ordered α]
  [order_topology α] [topological_space β] [t2_space β] {f : α → β} {a b : α}
  {la : β} (hab : a < b) (ha : tendsto f (𝓝[>] a) (𝓝 la)) :
  extend_from (Ioo a b) f a = la :=
begin
  apply extend_from_eq,
  { rw closure_Ioo hab.ne,
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc] },
  { simpa [hab] }
end

lemma eq_lim_at_right_extend_from_Ioo [topological_space α] [linear_order α] [densely_ordered α]
  [order_topology α] [topological_space β] [t2_space β] {f : α → β} {a b : α}
  {lb : β} (hab : a < b) (hb : tendsto f (𝓝[<] b) (𝓝 lb)) :
  extend_from (Ioo a b) f b = lb :=
begin
  apply extend_from_eq,
  { rw closure_Ioo hab.ne,
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc] },
  { simpa [hab] }
end

lemma continuous_on_Ico_extend_from_Ioo [topological_space α]
  [linear_order α] [densely_ordered α] [order_topology α] [topological_space β]
  [regular_space β] {f : α → β} {a b : α} {la : β} (hab : a < b) (hf : continuous_on f (Ioo a b))
  (ha : tendsto f (𝓝[>] a) (𝓝 la)) :
  continuous_on (extend_from (Ioo a b) f) (Ico a b) :=
begin
  apply continuous_on_extend_from,
  { rw [closure_Ioo hab.ne], exact Ico_subset_Icc_self, },
  { intros x x_in,
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with rfl | h,
    { use la,
      simpa [hab] },
    { use [f x, hf x h] } }
end

lemma continuous_on_Ioc_extend_from_Ioo [topological_space α]
  [linear_order α] [densely_ordered α] [order_topology α] [topological_space β]
  [regular_space β] {f : α → β} {a b : α} {lb : β} (hab : a < b) (hf : continuous_on f (Ioo a b))
  (hb : tendsto f (𝓝[<] b) (𝓝 lb)) :
  continuous_on (extend_from (Ioo a b) f) (Ioc a b) :=
begin
  have := @continuous_on_Ico_extend_from_Ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ _ hab,
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this,
  exact this hf hb
end
