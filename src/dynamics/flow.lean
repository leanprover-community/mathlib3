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

variables {τ : Type*} {α : Type*}

/-- A set `s ⊆ α` is invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t` in `τ`. -/
def is_invariant (ϕ : τ → α → α) (s : set α): Prop := ∀ t, maps_to (ϕ t) s s

variables (ϕ : τ → α → α) (s : set α)

lemma is_invariant_iff_image : is_invariant ϕ s ↔ ∀ t, ϕ t '' s ⊆ s :=
by simp_rw [is_invariant, maps_to']

/-- A set `s ⊆ α` is forward-invariant under `ϕ : τ → α → α` if
    `ϕ t s ⊆ s` for all `t ≥ 0`. -/
def is_fw_invariant [preorder τ] [has_zero τ] (ϕ : τ → α → α) (s : set α): Prop :=
∀ ⦃t⦄, 0 ≤ t → maps_to (ϕ t) s s

lemma is_invariant.is_fw_invariant [preorder τ] [has_zero τ] {ϕ : τ → α → α} {s : set α}
  (h : is_invariant ϕ s) : is_fw_invariant ϕ s :=
λ t ht, h t

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
lemma is_fw_invariant.is_invariant [canonically_ordered_add_monoid τ] {ϕ : τ → α → α} {s : set α}
  (h : is_fw_invariant ϕ s) : is_invariant ϕ s :=
λ t, h (zero_le t)

/-- If `τ` is a `canonically_ordered_add_monoid` (e.g., `ℕ` or `ℝ≥0`), then the notions
`is_fw_invariant` and `is_invariant` are equivalent. -/
lemma is_fw_invariant_iff_is_invariant [canonically_ordered_add_monoid τ]
  {ϕ : τ → α → α} {s : set α} :
  is_fw_invariant ϕ s ↔ is_invariant ϕ s :=
⟨is_fw_invariant.is_invariant, is_invariant.is_fw_invariant⟩

end invariant

/-!
### Flows
-/

/-- A flow on a topological space `α` by an a additive topological
    monoid `τ` is a continuous monoid action of `τ` on `α`.-/
structure flow
  (τ : Type*) [topological_space τ] [add_monoid τ] [has_continuous_add τ]
  (α : Type*) [topological_space α] :=
(to_fun    : τ → α → α)
(cont'     : continuous (uncurry to_fun))
(map_add'  : ∀ t₁ t₂ x, to_fun (t₁ + t₂) x = to_fun t₁ (to_fun t₂ x))
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
protected lemma continuous {β : Type*} [topological_space β]
  {t : β → τ} (ht : continuous t) {f : β → α} (hf : continuous f) :
  continuous (λ x, ϕ (t x) (f x)) :=
ϕ.cont'.comp (ht.prod_mk hf)

alias flow.continuous ← continuous.flow

lemma map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x) :=
ϕ.map_add' _ _ _

@[simp] lemma map_zero : ϕ 0 = id := funext ϕ.map_zero'

lemma map_zero_apply (x : α) : ϕ 0 x = x := ϕ.map_zero' x

/-- Iterations of a continuous function from a topological space `α`
    to itself defines a semiflow by `ℕ` on `α`. -/
def from_iter {g : α → α} (h : continuous g) : flow ℕ α :=
{ to_fun    := λ n x, g^[n] x,
  cont'     := continuous_uncurry_of_discrete_topology_left (continuous.iterate h),
  map_add'  := iterate_add_apply _,
  map_zero' := λ x, rfl }

/-- Restriction of a flow onto an invariant set. -/
def restrict {s : set α} (h : is_invariant ϕ s) : flow τ ↥s :=
{ to_fun    := λ t, (h t).restrict _ _ _,
  cont'     := continuous_subtype_mk _ (ϕ.continuous continuous_fst
    (continuous_subtype_coe.comp continuous_snd)),
  map_add'  := λ _ _ _, subtype.ext (map_add _ _ _ _),
  map_zero' := λ _, subtype.ext (map_zero_apply _ _)}

end flow

namespace flow

variables
{τ : Type*} [add_comm_group τ] [topological_space τ] [topological_add_group τ]
{α : Type*} [topological_space α]
(ϕ : flow τ α)

lemma is_invariant_iff_image_eq (s : set α) :
  is_invariant ϕ s ↔ ∀ t, ϕ t '' s = s :=
(is_invariant_iff_image _ _).trans (iff.intro
  (λ h t, subset.antisymm (h t) (λ _ hx, ⟨_, h (-t) ⟨_, hx, rfl⟩, by simp [← map_add]⟩))
  (λ h t, by rw h t))

/-- The time-reversal of a flow `ϕ` by a (commutative, additive) group
    is defined `ϕ.reverse t x = ϕ (-t) x`. -/
def reverse : flow τ α :=
{ to_fun    := λ t, ϕ (-t),
  cont'     := ϕ.continuous continuous_fst.neg continuous_snd,
  map_add'  := λ _ _ _, by rw [neg_add, map_add],
  map_zero' := λ _, by rw [neg_zero, map_zero_apply] }

/-- The map `ϕ t` as a homeomorphism. -/
def to_homeomorph (t : τ) : α ≃ₜ α :=
{ to_fun := ϕ t,
  inv_fun := ϕ (-t),
  left_inv := λ x, by rw [← map_add, neg_add_self, map_zero_apply],
  right_inv := λ x, by rw [← map_add, add_neg_self, map_zero_apply] }

lemma image_eq_preimage (t : τ) (s : set α) : ϕ t '' s = ϕ (-t) ⁻¹' s :=
(ϕ.to_homeomorph t).to_equiv.image_eq_preimage s

end flow
