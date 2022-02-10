/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import order.succ_pred.basic
import topology.algebra.ordered.basic

/-!
# Instances related to the discrete topology

We prove that the discrete topology is a first-countable topology, and is second-countable for an
encodable type. Also, in linear orders which are also `pred_order` and `succ_order`, the discrete
topology is the order topology.

When importing this file and `data.nat.succ_pred`, the instances `second_countable_topology ℕ` and
`order_topology ℕ` become available.

-/

open topological_space

variables {α : Type*} [topological_space α]

@[priority 100]
instance discrete_topology.first_countable_topology [discrete_topology α] :
  first_countable_topology α :=
{ nhds_generated_countable :=
    by { rw nhds_discrete, exact λ a, filter.is_countably_generated_pure _, } }

@[priority 100]
instance discrete_topology.second_countable_topology_of_encodable
  [hd : discrete_topology α] [encodable α] :
  second_countable_topology α :=
begin
  haveI : ∀ (i : α), second_countable_topology ↥({i} : set α),
    from λ i, { is_open_generated_countable :=
      ⟨{set.univ}, set.countable_singleton _, by simp only [eq_iff_true_of_subsingleton]⟩, },
  have h_open : ∀ (i : α), is_open ({i} : set α), from λ i, is_open_discrete _,
  exact second_countable_topology_of_countable_cover h_open (set.Union_of_singleton α),
end

@[priority 100]
instance discrete_topology.order_topology_of_pred_succ' [h : discrete_topology α] [partial_order α]
  [succ_order α] [pred_order α] [no_max_order α] [no_min_order α] :
  order_topology α :=
begin
  constructor,
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = set.Iio (succ_order.succ a) ∩ set.Ioi (pred_order.pred a),
  { suffices h_singleton_eq_inter' : {a} = set.Iic a ∩ set.Ici a,
      by rw [h_singleton_eq_inter', pred_order.Ici_eq_Ioi_pred, succ_order.Iic_eq_Iio_succ],
    rw [set.inter_comm, set.Ici_inter_Iic, set.Icc_self a], },
  rw h_singleton_eq_inter,
  refine @is_open.inter _ _ _ (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}) _ _,
  { exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, },
  { exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, },
end

@[priority 100]
instance discrete_topology.order_topology_of_pred_succ [h : discrete_topology α] [linear_order α]
  [succ_order α] [pred_order α] :
  order_topology α :=
begin
  constructor,
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = set.Iic a ∩ set.Ici a,
    by rw [set.inter_comm, set.Ici_inter_Iic, set.Icc_self a],
  by_cases ha_top : is_top a,
  { rw [ha_top.Iic_eq, set.inter_comm, set.inter_univ] at h_singleton_eq_inter,
    by_cases ha_bot : is_bot a,
    { rw ha_bot.Ici_eq at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact @is_open_univ _ (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}), },
    { rw is_bot_iff_is_min at ha_bot,
      rw pred_order.Ici_eq_Ioi_pred' ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, }, },
  { rw is_top_iff_is_max at ha_top,
    rw succ_order.Iic_eq_Iio_succ' ha_top at h_singleton_eq_inter,
    by_cases ha_bot : is_bot a,
    { rw [ha_bot.Ici_eq, set.inter_univ] at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, },
    { rw is_bot_iff_is_min at ha_bot,
      rw pred_order.Ici_eq_Ioi_pred' ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      refine @is_open.inter _ _ _
        (generate_from {s : set α | ∃ a, s = set.Ioi a ∨ s = set.Iio a}) _ _,
      { exact is_open_generate_from_of_mem ⟨succ_order.succ a, or.inr rfl⟩, },
      { exact is_open_generate_from_of_mem ⟨pred_order.pred a, or.inl rfl⟩, }, }, },
end
