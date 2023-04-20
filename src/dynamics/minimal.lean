/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import group_theory.group_action.basic
import topology.algebra.const_mul_action

/-!
# Minimal action of a group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/

open_locale pointwise

/-- An action of an additive monoid `M` on a topological space is called *minimal* if the `M`-orbit
of every point `x : α` is dense. -/
class add_action.is_minimal (M α : Type*) [add_monoid M] [topological_space α] [add_action M α] :
  Prop :=
(dense_orbit : ∀ x : α, dense (add_action.orbit M x))

/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[to_additive]
class mul_action.is_minimal (M α : Type*) [monoid M] [topological_space α] [mul_action M α] :
  Prop :=
(dense_orbit : ∀ x : α, dense (mul_action.orbit M x))

open mul_action set

variables (M G : Type*) {α : Type*} [monoid M] [group G] [topological_space α] [mul_action M α]
  [mul_action G α]

@[to_additive] lemma mul_action.dense_orbit [is_minimal M α] (x : α) : dense (orbit M x) :=
mul_action.is_minimal.dense_orbit x

@[to_additive] lemma dense_range_smul [is_minimal M α] (x : α) :
  dense_range (λ c : M, c • x) :=
mul_action.dense_orbit M x

@[priority 100, to_additive]
instance mul_action.is_minimal_of_pretransitive [is_pretransitive M α] : is_minimal M α :=
⟨λ x, (surjective_smul M x).dense_range⟩

@[to_additive] lemma is_open.exists_smul_mem [is_minimal M α] (x : α) {U : set α} (hUo : is_open U)
  (hne : U.nonempty) : ∃ c : M, c • x ∈ U :=
(dense_range_smul M x).exists_mem_open hUo hne

@[to_additive] lemma is_open.Union_preimage_smul [is_minimal M α] {U : set α} (hUo : is_open U)
  (hne : U.nonempty) : (⋃ c : M, (•) c ⁻¹' U) = univ :=
Union_eq_univ_iff.2 $ λ x, hUo.exists_smul_mem M x hne

@[to_additive] lemma is_open.Union_smul [is_minimal G α] {U : set α} (hUo : is_open U)
  (hne : U.nonempty) : (⋃ g : G, g • U) = univ :=
Union_eq_univ_iff.2 $ λ x, let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
in ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
lemma is_compact.exists_finite_cover_smul [is_minimal G α]
  [has_continuous_const_smul G α] {K U : set α} (hK : is_compact K) (hUo : is_open U)
  (hne : U.nonempty) :
  ∃ I : finset G, K ⊆ ⋃ g ∈ I, g • U :=
hK.elim_finite_subcover (λ g : G, g • U) (λ g, hUo.smul _) $
  calc K ⊆ univ : subset_univ K
  ... = ⋃ g : G, g • U : (hUo.Union_smul G hne).symm

@[to_additive]
lemma dense_of_nonempty_smul_invariant [is_minimal M α] {s : set α} (hne : s.nonempty)
  (hsmul : ∀ c : M, c • s ⊆ s) : dense s :=
let ⟨x, hx⟩ := hne in (mul_action.dense_orbit M x).mono
  (range_subset_iff.2 $ λ c, hsmul c $ ⟨x, hx, rfl⟩)

@[to_additive]
lemma eq_empty_or_univ_of_smul_invariant_closed [is_minimal M α] {s : set α} (hs : is_closed s)
  (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
s.eq_empty_or_nonempty.imp_right $ λ hne, hs.closure_eq ▸
  (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[to_additive] lemma is_minimal_iff_closed_smul_invariant [has_continuous_const_smul M α] :
  is_minimal M α ↔ ∀ s : set α, is_closed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ :=
begin
  split, { introsI h s, exact eq_empty_or_univ_of_smul_invariant_closed M },
  refine λ H, ⟨λ x, dense_iff_closure_eq.2 $ (H _ _ _).resolve_left _⟩,
  exacts [is_closed_closure, λ c, smul_closure_orbit_subset _ _,
    (orbit_nonempty _).closure.ne_empty]
end
