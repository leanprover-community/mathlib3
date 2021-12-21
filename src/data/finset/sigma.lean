/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.basic

/-!
# Finite sets in a sigma type

This file defines a `finset` construction on `Σ i, α i`.

## Main declarations

* `finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
-/

open function multiset

namespace finset
variables {ι : Type*} {α : ι → Type*} (s s₁ s₂ : finset ι) (t t₁ t₂ : Π i, finset (α i))

/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : finset (Σ i, α i) := ⟨_, nodup_sigma s.2 (λ i, (t i).2)⟩

variables {s s₁ s₂ t t₁ t₂}

@[simp] lemma mem_sigma {a : Σ i, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 := mem_sigma

@[simp] lemma sigma_nonempty : (s.sigma t).nonempty ↔ ∃ i ∈ s, (t i).nonempty :=
by simp [finset.nonempty]

@[simp] lemma sigma_eq_empty : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
by simp only [← not_nonempty_iff_eq_empty, sigma_nonempty, not_exists]

@[mono] lemma sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ ⟨i, a⟩ h, let ⟨hi, ha⟩ := mem_sigma.1 h in mem_sigma.2 ⟨hs hi, ht i ha⟩

lemma sigma_eq_bUnion [decidable_eq (Σ i, α i)] (s : finset ι) (t : Π i, finset (α i)) :
  s.sigma t = s.bUnion (λ i, (t i).map $ embedding.sigma_mk i) :=
by { ext ⟨x, y⟩, simp [and.left_comm] }

end finset
