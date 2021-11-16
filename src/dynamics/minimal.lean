/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.algebra.mul_action
import group_theory.group_action.basic

/-!
# Minimal action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definiton and
prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/

open_locale pointwise
open set

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

namespace mul_action

variables (M G : Type*) {α : Type*} [monoid M] [group G] [topological_space α] [mul_action M α]
  [mul_action G α]

@[to_additive] lemma dense_orbit [is_minimal M α] (x : α) : dense (orbit M x) :=
mul_action.is_minimal.dense_orbit x

@[to_additive] lemma dense_range_smul [is_minimal M α] (x : α) :
  dense_range (λ c : M, c • x) :=
dense_orbit M x

@[priority 100, to_additive]
instance is_minimal_of_pretransitive [is_pretransitive M α] : is_minimal M α :=
⟨λ x, (surjective_smul M x).dense_range⟩

@[to_additive]
lemma exists_smul_mem_open [is_minimal M α] (x : α) {U : set α} (hUo : is_open U)
  (hne : U.nonempty) : ∃ c : M, c • x ∈ U :=
(dense_range_smul M x).exists_mem_open hUo hne

@[to_additive]
lemma exists_cover_smul [is_minimal G α] (s : set α) {U : set α} (hUo : is_open U)
  (hne : U.nonempty) :
  ∃ I : set G, s ⊆ ⋃ g ∈ I, g • U :=
begin
  choose g hgU using λ x, exists_smul_mem_open G x hUo hne,
  refine ⟨(λ x, (g x)⁻¹) '' s, λ x hx, mem_bUnion (mem_image_of_mem _ hx) _⟩,
  rw ← preimage_smul, exact hgU x
end

@[to_additive]
lemma exists_finite_cover_smul [topological_space G] [is_minimal G α] [has_continuous_smul G α]
  {K U : set α} (hK : is_compact K) (hUo : is_open U) (hne : U.nonempty) :
  ∃ I : finset G, K ⊆ ⋃ g ∈ I, g • U :=
begin
  classical,
  rcases exists_cover_smul G K hUo hne with ⟨I, hI⟩,
  rw bUnion_eq_Union at hI,
  rcases hK.elim_finite_subcover (λ c : I, (c : G) • U) (λ c, hUo.smul _) hI with ⟨t, ht⟩,
  refine ⟨t.image coe, _⟩, simpa [bUnion_eq_Union] using ht
end

@[to_additive]
lemma dense_of_nonempty_forward_invariant [is_minimal M α] {s : set α} (hne : s.nonempty)
  (hsmul : ∀ c : M, c • s ⊆ s) : dense s :=
let ⟨x, hx⟩ := hne in (dense_orbit M x).mono (range_subset_iff.2 $ λ c, hsmul c $ ⟨x, hx, rfl⟩)

@[to_additive]
lemma eq_empty_of_univ_of_forward_invariant_closed [is_minimal M α] {s : set α} (hs : is_closed s)
  (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
s.eq_empty_or_nonempty.imp_right $ λ hne, hs.closure_eq ▸
  (dense_of_nonempty_forward_invariant M hne hsmul).closure_eq

@[to_additive] lemma is_minimal_iff_closed_forward_invariant [topological_space M]
  [has_continuous_smul M α] :
  is_minimal M α ↔ ∀ s : set α, is_closed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ :=
begin
  split, { introsI h s, exact eq_empty_of_univ_of_forward_invariant_closed M },
  refine λ H, ⟨λ x, dense_iff_closure_eq.2 $ (H _ _ _).resolve_left _⟩,
  exacts [is_closed_closure, λ c, smul_closure_orbit_subset _ _,
    (orbit_nonempty _).closure.ne_empty]
end

end mul_action
