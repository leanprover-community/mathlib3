/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/

import topology.algebra.group
import logic.function.iterate

/-!
# Flows and invariant sets

This file defines a flow on a topological space `α` by a topological
monoid `τ` as a continuous monoid-act of `τ` on `α`. Anticipating the
cases where `τ` is one of `ℕ`, `ℤ`, `ℝ⁺`, or `ℝ`, we use additive
notation for the monoids, though the definition does not require
commutativity.

A subset `s` of `α` is invariant under a family of maps `ϕₜ : α → α`
if `ϕₜ s ⊆ s` for all `t`. In many cases `ϕ` will be a flow on
`α`. For the cases where `ϕ` is a flow by an ordered (additive,
commutative) monoid, we additionally define forward invariance, where
`t` ranges over those elements which are nonnegative.

Additionally, we define such constructions as the restriction of a
flow onto an invariant subset, and the time-reveral of a flow by a
group.
-/

open set function filter

/-!
### Invariant sets
-/

section invariant

variables {τ  : Type*} {α : Type*}

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def is_invariant (ϕ : τ → α → α) (s : set α): Prop := ∀ t (x ∈ s), ϕ t x ∈ s

variables (ϕ : τ → α → α) (s : set α)

lemma is_invariant_iff_image : is_invariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s :=
by { simp_rw image_subset_iff, exact iff.rfl }

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def is_fw_invariant [ordered_add_comm_monoid τ]
  (ϕ : τ → α → α) (s : set α): Prop := ∀ {t} (ht : 0 ≤ t) (x ∈ s), ϕ t x ∈ s

end invariant

/-!
### Flows
-/

/-- A flow on a topological space `α` by an a additive topological
    semigroup `τ` is a continuous semigroup-act of `τ` on `α`.-/
structure flow
  (τ : Type*) [topological_space τ] [add_monoid τ] [has_continuous_add τ]
  (α : Type*) [topological_space α] :=
(to_fun    : τ → α → α)
(cont'     : continuous (uncurry to_fun))
(map_add'  : ∀ t₁ t₂ x, to_fun t₂ (to_fun t₁ x) = to_fun (t₁ + t₂) x)
(map_zero' : ∀ x, to_fun 0 x = x)

namespace flow

variables
{τ : Type*} [add_monoid τ] [topological_space τ] [has_continuous_add τ]
{α : Type*} [topological_space α]
(ϕ : flow τ α)

instance : inhabited (flow τ α) :=
⟨{ to_fun    := λ _ x, x,
   cont'     := continuous_snd,
   map_add'  := λ _ _ _, rfl,
   map_zero' := λ _, rfl }⟩

instance : has_coe_to_fun (flow τ α) := ⟨_, flow.to_fun⟩

@[ext]
lemma ext : ∀ {ϕ₁ ϕ₂ : flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
| ⟨f₁, _, _, _⟩ ⟨f₂, _, _, _⟩ h := by { congr, funext, exact h _ _ }

@[continuity]
protected lemma continuous : continuous (uncurry ϕ) := ϕ.cont'

@[simp]
lemma map_add (t₁ t₂ : τ) (x : α) : ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x :=
ϕ.map_add' _ _ _

@[simp]
lemma map_zero (x : α) : ϕ 0 x = x := ϕ.map_zero' _

/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def from_iter {g : α → α} (h : continuous g) : flow ℕ α :=
{ to_fun    := λ n x, g^[n] x,
  cont'     := continuous_uncurry_of_discrete_topology_left (continuous.iterate h),
  map_add'  := λ _ _ _, by rw [add_comm, iterate_add_apply],
  map_zero' := λ x, by { rw iterate_zero, refl }}

/-- Restriction of a flow onto an invariant set. -/
def restrict {s : set α} (h : is_invariant ϕ s) : flow τ ↥s :=
{ to_fun    := λ t x, ⟨ϕ t x, h _ _ x.prop⟩,
  cont'     := continuous_subtype_mk _ (ϕ.continuous.comp
                 (continuous.prod_map continuous_id continuous_subtype_val)),
  map_add'  := λ _ _ _, subtype.ext (map_add _ _ _ _),
  map_zero' := λ _, subtype.ext (map_zero _ _)}

end flow

namespace flow

variables
{τ : Type*} [add_comm_group τ] [topological_space τ] [topological_add_group τ]
{α : Type*} [topological_space α]
(ϕ : flow τ α)

lemma is_invariant_iff_image_eq (s : set α) :
  is_invariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
(is_invariant_iff_image _ _).trans (iff.intro
  (λ h t, subset.antisymm (h t) (λ _ hx, ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp⟩))
  (λ h t, by rw h t))

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : flow τ α :=
{ to_fun    := λ t x, ϕ (-t) x,
  cont'     := ϕ.continuous.comp (continuous.prod_mk
                 (continuous_neg.comp continuous_fst) continuous_snd),
  map_add'  := λ _ _ _, by rw [map_add, neg_add],
  map_zero' := λ _, by simp_rw [neg_zero, map_zero] }

end flow
