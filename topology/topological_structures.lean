/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological monoids, groups and rings.
-/

import topology.topological_space topology.continuity
open filter topological_space
local attribute [instance] classical.decidable_inhabited classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

lemma dense_or_discrete [linear_order α] {a₁ a₂ : α} (h : a₁ < a₂) :
  (∃a, a₁ < a ∧ a < a₂) ∨ ((∀a>a₁, a ≥ a₂) ∧ (∀a<a₂, a ≤ a₁)) :=
or_of_not_implies $ assume h,
  ⟨assume a ha₁, le_of_not_gt $ assume ha₂, h ⟨a, ha₁, ha₂⟩,
    assume a ha₂, le_of_not_gt $ assume ha₁, h ⟨a, ha₁, ha₂⟩⟩

section topological_add_monoid

class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

variables [topological_space α] [add_monoid α]

lemma continuous_add' [topological_add_monoid α] : continuous (λp:α×α, p.1 + p.2) :=
topological_add_monoid.continuous_add α

lemma continuous_add [topological_add_monoid α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x + g x) :=
continuous_compose (continuous_prod_mk hf hg) continuous_add'

lemma tendsto_add [topological_add_monoid α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x + g x) x (nhds (a + b)) :=
have tendsto (λp:α×α, p.fst + p.snd) (nhds (a, b)) (nhds (a + b)),
  from continuous_iff_tendsto.mp (topological_add_monoid.continuous_add α) (a, b),
tendsto_compose (tendsto_prod_mk hf hg) (by rw [nhds_prod_eq] at this; exact this)

end topological_add_monoid

section topological_add_group
class topological_add_group (α : Type u) [topological_space α] [add_group α]
  extends topological_add_monoid α : Prop :=
(continuous_neg : continuous (λa:α, -a))

variables [topological_space α] [add_group α]

lemma continuous_neg' [topological_add_group α] : continuous (λx:α, - x) :=
topological_add_group.continuous_neg α

lemma continuous_neg [topological_add_group α] [topological_space β] {f : β → α}
  (hf : continuous f) : continuous (λx, - f x) :=
continuous_compose hf continuous_neg'

lemma tendsto_neg [topological_add_group α] {f : β → α} {x : filter β} {a : α}
  (hf : tendsto f x (nhds a)) : tendsto (λx, - f x) x (nhds (- a)) :=
tendsto_compose hf (continuous_iff_tendsto.mp (topological_add_group.continuous_neg α) a)

lemma continuous_sub [topological_add_group α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x - g x) :=
by simp; exact continuous_add hf (continuous_neg hg)

lemma tendsto_sub [topological_add_group α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x - g x) x (nhds (a - b)) :=
by simp; exact tendsto_add hf (tendsto_neg hg)

end topological_add_group

section topological_ring
class topological_ring (α : Type u) [topological_space α] [ring α]
  extends topological_add_group α : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

variables [topological_space α] [ring α]

lemma continuous_mul [topological_ring α] [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λx, f x * g x) :=
continuous_compose (continuous_prod_mk hf hg) (topological_ring.continuous_mul α)

lemma tendsto_mul [topological_ring α] {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) : tendsto (λx, f x * g x) x (nhds (a * b)) :=
have tendsto (λp:α×α, p.fst * p.snd) (nhds (a, b)) (nhds (a * b)),
  from continuous_iff_tendsto.mp (topological_ring.continuous_mul α) (a, b),
tendsto_compose (tendsto_prod_mk hf hg) (by rw [nhds_prod_eq] at this; exact this)

end topological_ring

section linear_ordered_topology
class linear_ordered_topology (α : Type u) [t : topological_space α] [linear_order α] : Prop :=
(is_open_lt : ∀a, is_open {b : α | a < b})
(is_open_gt : ∀a, is_open {b : α | a > b})

variables [topological_space α] [linear_order α] [t : linear_ordered_topology α]
include t

lemma order_separated {a₁ a₂ : α} (h : a₁ < a₂) :
  ∃u v : set α, is_open u ∧ is_open v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ (∀b₁∈u, ∀b₂∈v, b₁ < b₂) :=
match dense_or_discrete h with
| or.inl ⟨a, ha₁, ha₂⟩ := ⟨{a' | a' < a}, {a' | a < a'},
    linear_ordered_topology.is_open_gt a, linear_ordered_topology.is_open_lt a, ha₁, ha₂,
    assume b₁ h₁ b₂ h₂, lt_trans h₁ h₂⟩
| or.inr ⟨h₁, h₂⟩ := ⟨{a | a < a₂}, {a | a₁ < a},
    linear_ordered_topology.is_open_gt a₂, linear_ordered_topology.is_open_lt a₁, h, h,
    assume b₁ hb₁ b₂ hb₂,
    calc b₁ ≤ a₁ : h₂ _ hb₁
      ... < a₂ : h
      ... ≤ b₂ : h₁ _ hb₂⟩
end

lemma is_open_lt_fst_snd : is_open {p:α×α | p.1 < p.2} :=
is_open_prod_iff.mpr $ assume a₁ a₂ (h : a₁ < a₂),
  let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h in
  ⟨u, v, hu, hv, ha₁, ha₂, assume ⟨b₁, b₂⟩ ⟨h₁, h₂⟩, h b₁ h₁ b₂ h₂⟩

lemma is_open_lt [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_open {b | f b < g b} :=
continuous_prod_mk hf hg {p:α×α | p.1 < p.2} is_open_lt_fst_snd

lemma is_closed_le [topological_space β] {f g : β → α} (hf : continuous f) (hg : continuous g) :
  is_closed {b | f b ≤ g b} :=
is_open_compl_iff.mp $ show is_open {b : β | ¬ f b ≤ g b},
  by simp [not_le_iff]; exact is_open_lt hg hf

instance linear_ordered_topology.to_t2_space : t2_space α :=
have ∀{a₁ a₂ : α}, a₁ < a₂ → ∃u v : set α, is_open u ∧ is_open v ∧ a₁ ∈ u ∧ a₂ ∈ v ∧ u ∩ v = ∅,
  from assume a₁ a₂ h,
  let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := order_separated h in
  ⟨u, v, hu, hv, ha₁, ha₂,
    set.eq_empty_of_forall_not_mem $ assume a ⟨h₁, h₂⟩, lt_irrefl a $ h _ h₁ _ h₂⟩,
⟨assume a₁ a₂ h, match lt_or_gt_of_ne h with
  | or.inl h := this h
  | or.inr h := let ⟨u, v, hu, hv, ha₁, ha₂, h⟩ := this h in
    ⟨v, u, hv, hu, ha₂, ha₁, by rwa [set.inter_comm] at h⟩
  end⟩

end linear_ordered_topology