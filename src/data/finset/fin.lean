/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison, Johan Commelin
-/
import data.finset.card

/-!
# Finsets in `fin n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A few constructions for finsets in `fin n`.

## Main declarations

* `finset.attach_fin`: Turns a finset of naturals strictly less than `n` into a `finset (fin n)`.
-/

variables {n : ℕ}

namespace finset

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : finset (fin n) :=
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, s.nodup.pmap $ λ _ _ _ _, fin.veq_of_eq⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ (a : ℕ) ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁,
λ h, multiset.mem_pmap.2 ⟨a, h, fin.eta _ _⟩⟩

@[simp] lemma card_attach_fin {n : ℕ} (s : finset ℕ) (h : ∀ m ∈ s, m < n) :
  (s.attach_fin h).card = s.card :=
multiset.card_pmap _ _ _

end finset
