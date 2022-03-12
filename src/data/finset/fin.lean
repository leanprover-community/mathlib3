/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison, Johan Commelin
-/
import data.finset.card

/-!
# Finsets in `fin n`

A few constructions for finsets in `fin n`.

## Main declarations

* `finset.fin_range`: `{0, 1, ..., n - 1}` as a `finset (fin n)`.
* `finset.attach_fin`: Turns a finset of naturals strictly less than `n` into a `finset (fin n)`.
-/

variables {n : ℕ}

namespace finset

/-- `finset.fin_range n` is the finset `{0, 1, ..., n - 1}`, as a `finset (fin n)`. -/
def fin_range (n : ℕ) : finset (fin n) := ⟨list.fin_range n, list.nodup_fin_range n⟩

@[simp]
lemma fin_range_card : (fin_range n).card = n := by simp [fin_range]

@[simp]
lemma mem_fin_range (m : fin n) : m ∈ fin_range n := list.mem_fin_range m

@[simp] lemma coe_fin_range (n : ℕ) : (fin_range n : set (fin n)) = set.univ :=
set.eq_univ_of_forall mem_fin_range

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : finset (fin n) :=
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, multiset.nodup_pmap (λ _ _ _ _, fin.veq_of_eq) s.2⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ (a : ℕ) ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁,
λ h, multiset.mem_pmap.2 ⟨a, h, fin.eta _ _⟩⟩

@[simp] lemma card_attach_fin {n : ℕ} (s : finset ℕ) (h : ∀ m ∈ s, m < n) :
  (s.attach_fin h).card = s.card :=
multiset.card_pmap _ _ _

end finset
