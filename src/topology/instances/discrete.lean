/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import order.succ_pred.basic
import topology.algebra.order.basic

/-!
# Instances related to the discrete topology

We prove that the discrete topology is a first-countable topology, and is second-countable for an
encodable type. Also, in linear orders which are also `pred_order` and `succ_order`, the discrete
topology is the order topology.

When importing this file and `data.nat.succ_pred`, the instances `second_countable_topology ℕ`
and `order_topology ℕ` become available.

-/

open order set topological_space

variables {α : Type*} [topological_space α]

@[priority 100]
instance discrete_topology.first_countable_topology [discrete_topology α] :
  first_countable_topology α :=
{ nhds_generated_countable :=
    by { rw nhds_discrete, exact filter.is_countably_generated_pure } }

@[priority 100]
instance discrete_topology.second_countable_topology_of_encodable
  [hd : discrete_topology α] [encodable α] :
  second_countable_topology α :=
begin
  haveI : ∀ (i : α), second_countable_topology ↥({i} : set α),
    from λ i, { is_open_generated_countable :=
      ⟨{univ}, countable_singleton _, by simv only [eq_iff_true_of_subsingleton]⟩, },
  exact second_countable_topology_of_countable_cover (singletons_open_iff_discrete.mpr hd)
    (Union_of_singleton α),
end

@[priority 100]
instance discrete_topology.order_topology_of_pred_succ' [h : discrete_topology α] [partial_order α]
  [pred_order α] [succ_order α] [no_min_order α] [no_max_order α] :
  order_topology α :=
⟨begin
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = Iio (succ a) ∩ Ioi (pred a),
  { suffices h_singleton_eq_inter' : {a} = Iic a ∩ Ici a,
      by rw [h_singleton_eq_inter', ←Ioi_pred, ←Iio_succ],
    rw [inter_comm, Ici_inter_Iic, Icc_self a], },
  rw h_singleton_eq_inter,
  apply is_open.inter,
  { exact is_open_generate_from_of_mem ⟨succ a, or.inr rfl⟩, },
  { exact is_open_generate_from_of_mem ⟨pred a, or.inl rfl⟩, },
end⟩

@[priority 100]
instance discrete_topology.order_topology_of_pred_succ [h : discrete_topology α] [linear_order α]
  [pred_order α] [succ_order α] :
  order_topology α :=
⟨begin
  rw h.eq_bot,
  refine (eq_bot_of_singletons_open (λ a, _)).symm,
  have h_singleton_eq_inter : {a} = Iic a ∩ Ici a,
    by rw [inter_comm, Ici_inter_Iic, Icc_self a],
  by_cases ha_top : is_top a,
  { rw [ha_top.Iic_eq, inter_comm, inter_univ] at h_singleton_eq_inter,
    by_cases ha_bot : is_bot a,
    { rw ha_bot.Ici_eq at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      apply is_open_univ, },
    { rw is_bot_iff_is_min at ha_bot,
      rw ←Ioi_pred_of_not_is_min ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨pred a, or.inl rfl⟩, }, },
  { rw is_top_iff_is_max at ha_top,
    rw ←Iio_succ_of_not_is_max ha_top at h_singleton_eq_inter,
    by_cases ha_bot : is_bot a,
    { rw [ha_bot.Ici_eq, inter_univ] at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      exact is_open_generate_from_of_mem ⟨succ a, or.inr rfl⟩, },
    { rw is_bot_iff_is_min at ha_bot,
      rw ←Ioi_pred_of_not_is_min ha_bot at h_singleton_eq_inter,
      rw h_singleton_eq_inter,
      apply is_open.inter,
      { exact is_open_generate_from_of_mem ⟨succ a, or.inr rfl⟩ },
      { exact is_open_generate_from_of_mem ⟨pred a, or.inl rfl⟩ } } }
end⟩
