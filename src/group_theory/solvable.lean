/-
Copyright (c) 2021 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/

import group_theory.abelianization
import data.bracket

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
  `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

open subgroup

variables {G : Type*} [group G]

section general_commutator

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance general_commutator : has_bracket (subgroup G) (subgroup G) :=
⟨λ H₁ H₂, closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}⟩

lemma general_commutator_def (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆ = closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} := rfl

instance general_commutator_normal (H₁ H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal ⁅H₁, H₂⁆ :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator_def, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  rw group.mem_conjugates_of_set_iff at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma general_commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  ⁅H₁, H₂⁆ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [← normal_closure_eq_self ⁅H₁, H₂⁆, general_commutator_def,
  normal_closure_closure_eq_normal_closure]

lemma general_commutator_le (H₁ H₂ : subgroup G) (K : subgroup G) :
  ⁅H₁, H₂⁆ ≤ K ↔ ∀ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ ∈ K :=
begin
  rw [general_commutator, closure_le],
  split,
  { intros h p hp q hq,
    exact h ⟨p, hp, q, hq, rfl⟩, },
  { rintros h x ⟨p, hp, q, hq, rfl⟩,
    exact h p hp q hq, }
end

lemma general_commutator_comm (H₁ H₂ : subgroup G) : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
begin
  suffices : ∀ H₁ H₂ : subgroup G, ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆, { exact le_antisymm (this _ _) (this _ _) },
  intros H₁ H₂,
  rw general_commutator_le,
  intros p hp q hq,
  have h : (p * q * p⁻¹ * q⁻¹)⁻¹ ∈ ⁅H₂, H₁⁆ := subset_closure ⟨q, hq, p, hp, by group⟩,
  convert inv_mem ⁅H₂, H₁⁆ h,
  group,
end

lemma general_commutator_le_right (H₁ H₂ : subgroup G) [h : normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₂ :=
begin
  rw general_commutator_le,
  intros p hp q hq,
  exact mul_mem H₂ (h.conj_mem q hq p) (inv_mem H₂ hq),
end

lemma general_commutator_le_left (H₁ H₂ : subgroup G) [h : normal H₁] :
  ⁅H₁, H₂⁆ ≤ H₁ :=
begin
  rw general_commutator_comm,
  exact general_commutator_le_right H₂ H₁,
end

@[simp] lemma general_commutator_bot (H : subgroup G) : ⁅H, ⊥⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_right H ⊥ }

@[simp] lemma bot_general_commutator (H : subgroup G) : ⁅(⊥ : subgroup G), H⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_left ⊥ H }

lemma general_commutator_le_inf (H₁ H₂ : subgroup G) [normal H₁] [normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
by simp only [general_commutator_le_left, general_commutator_le_right, le_inf_iff, and_self]

end general_commutator

section derived_series

variables (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derived_series : ℕ → subgroup G
| 0       := ⊤
| (n + 1) := ⁅(derived_series n), (derived_series n)⁆

@[simp] lemma derived_series_zero : derived_series G 0 = ⊤ := rfl

@[simp] lemma derived_series_succ (n : ℕ) :
  derived_series G (n + 1) = ⁅(derived_series G n), (derived_series G n)⁆ := rfl

lemma derived_series_normal (n : ℕ) : (derived_series G n).normal :=
begin
  induction n with n ih,
  { exact subgroup.top_normal, },
  { rw derived_series_succ,
    exactI general_commutator_normal (derived_series G n) (derived_series G n), }
end

@[simp] lemma general_commutator_eq_commutator :
  ⁅(⊤ : subgroup G), (⊤ : subgroup G)⁆ = commutator G :=
begin
  rw [commutator, general_commutator_def'],
  apply le_antisymm; apply normal_closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩, },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩, }
end

lemma commutator_def' : commutator G = subgroup.closure {x : G | ∃ p q, p * q * p⁻¹ * q⁻¹ = x} :=
begin
  rw [← general_commutator_eq_commutator, general_commutator],
  apply le_antisymm; apply closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩ },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩ }
end

@[simp] lemma derived_series_one : derived_series G 1 = commutator G :=
general_commutator_eq_commutator G

end derived_series

section solvable

variables (G)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class is_solvable : Prop :=
(solvable : ∃ n : ℕ, derived_series G n = ⊥)

@[priority 100]
instance is_solvable_of_comm {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, derived_series_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (monoid_hom.id G)
  ... = ⊥ : rfl,
end

end solvable
