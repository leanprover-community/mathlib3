/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import data.fin.basic
import data.finset.sort
import order.lexicographic

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ tuple.sort f`.

## Main declarations

* `tuple.sort`: given `f : fin n → α`, produces a permutation on `fin n`
* `tuple.monotone_sort`: `f ∘ tuple.sort f` is `monotone`

-/

namespace tuple

variables {n : ℕ}
variables {α : Type*} [linear_order α]

/--
`graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : fin n → α) : finset (lex α (fin n)) :=
finset.univ.image (λ i, (f i, i))

/--
Given `p : lex α (fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : fin n → α} : graph f → α := λ p, p.1.1

@[simp] lemma graph.card (f : fin n → α) : (graph f).card = n :=
begin
  rw [graph, finset.card_image_of_injective],
  { exact finset.card_fin _ },
  { intros _ _,
    simp }
end

/--
`graph_equiv₁ f` is the natural equivalence between `fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graph_equiv₁ (f : fin n → α) : fin n ≃ graph f :=
{ to_fun := λ i, ⟨(f i, i), by simp [graph]⟩,
  inv_fun := λ p, p.1.2,
  left_inv := λ i, by simp,
  right_inv := λ ⟨⟨x, i⟩, h⟩, by simpa [graph] using h }

@[simp] lemma proj_equiv₁' (f : fin n → α) : graph.proj ∘ graph_equiv₁ f = f :=
rfl

/--
`graph_equiv₂ f` is an equivalence between `fin n` and `graph f` that respects the order.
-/
def graph_equiv₂ (f : fin n → α) : fin n ≃o graph f :=
finset.order_iso_of_fin _ (by simp)

/-- `sort f` is the permutation that orders `fin n` according to the order of the outputs of `f`. -/
def sort (f : fin n → α) : equiv.perm (fin n) :=
(graph_equiv₂ f).to_equiv.trans (graph_equiv₁ f).symm

lemma self_comp_sort (f : fin n → α) : f ∘ sort f = graph.proj ∘ graph_equiv₂ f :=
show graph.proj ∘ ((graph_equiv₁ f) ∘ (graph_equiv₁ f).symm) ∘ (graph_equiv₂ f).to_equiv = _,
  by simp


lemma monotone_proj (f : fin n → α) : monotone (graph.proj : graph f → α) :=
begin
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (h|h),
  { exact le_of_lt ‹_› },
  { simp [graph.proj] },
end

lemma monotone_sort (f : fin n → α) : monotone (f ∘ sort f) :=
begin
  rw [self_comp_sort],
  exact (monotone_proj f).comp (graph_equiv₂ f).monotone,
end

end tuple
