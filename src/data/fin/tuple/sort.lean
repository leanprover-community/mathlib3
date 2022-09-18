/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import data.fin.basic
import data.finset.sort
import data.prod.lex

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
def graph (f : fin n → α) : finset (α ×ₗ (fin n)) :=
finset.univ.image (λ i, (f i, i))

/--
Given `p : α ×ₗ (fin n) := (f i, i)` with `p ∈ graph f`,
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

namespace tuple

open list

variables {n : ℕ} {α : Type*}

/-- If we swap two strictly decreasing entries in a tuple, then the result is lexicographically
smaller than the original tuple. -/
lemma lex_desc [preorder α] {f : fin n → α} {i j : fin n} (h₁ : i < j) (h₂ : f j < f i) :
  to_lex (f ∘ equiv.swap i j) < to_lex f :=
begin
  simp only [has_lt.lt, pi.lex, pi.to_lex_apply, function.comp_app],
  refine ⟨i, λ k (hik : k < i), _, _⟩,
  { rw [equiv.swap_apply_of_ne_of_ne (ne_of_lt hik) (ne_of_lt $ hik.trans h₁)], },
  { simpa only [equiv.swap_apply_left], }
end

/-- If a tuple `f` and a permutation of `f` are both monotone, then they are equal. -/
lemma unique_monotone [partial_order α] {f : fin n → α} {σ : equiv.perm (fin n)} (hf : monotone f)
  (hfσ : monotone (f ∘ σ)) : f ∘ σ = f :=
of_fn_injective $ eq_of_perm_of_sorted (σ.of_fn_comp_perm f) hfσ.of_fn_sorted hf.of_fn_sorted

variables [linear_order α] {f : fin n → α}

/-- If a permutation of a tuple `f` is monotone, then it is equal to `f ∘ sort f`. -/
lemma unique_sort' {σ : equiv.perm (fin n)} (h : monotone (f ∘ σ)) : f ∘ σ = f ∘ sort f :=
begin
  let σ' := (sort f)⁻¹ * σ,
  have h' : f ∘ σ = (f ∘ sort f) ∘ σ',
  { ext, simp only [function.comp_app, equiv.perm.coe_mul, equiv.perm.apply_inv_self], },
  rw [h'],
  refine unique_monotone (monotone_sort f) _,
  rwa [← h'],
end

/-- If a tuple `f` is monotone, then it equals `f ∘ sort f`. -/
lemma unique_sort (h : monotone f) : f = f ∘ sort f :=
begin
  have hf : f = f ∘ (1 : equiv.perm (fin n)),
  { simp only [equiv.perm.coe_one, function.comp.right_id], },
  conv_lhs {rw hf},
  rw hf at h,
  exact unique_sort' h,
end

/-- The sorted versions of a tuple `f` and any permutation of it agree. -/
lemma sort_absorb {σ : equiv.perm (fin n)} : (f ∘ σ) ∘ (sort (f ∘ σ)) = f ∘ sort f :=
begin
  let τ := σ⁻¹ * (sort f),
  have h' : (f ∘ σ) ∘ τ = f ∘ sort f,
  { ext, simp only [equiv.perm.coe_mul, function.comp_app, equiv.perm.apply_inv_self] },
  have hm : monotone ((f ∘ σ) ∘ τ) := by { rw [h'], exact monotone_sort _, },
  exact (unique_sort' hm).symm.trans h',
end

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
lemma antitone_pair_of_not_sorted' {σ : equiv.perm (fin n)} (h : f ∘ σ ≠ f ∘ sort f) :
  ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i :=
begin
  by_contra' hf,
  have hm : monotone (f ∘ σ),
  { intros i j hij,
    cases eq_or_lt_of_le hij with heq hlt,
    { rw [heq], },
    { exact hf i j hlt, } },
  exact h (unique_sort' hm),
end

/-- If the tuple `f` is not the same as `f ∘ sort f`, then it has a pair of strictly decreasing
entries. -/
lemma antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
begin
  have hf : f = f ∘ (1 : equiv.perm (fin n)),
  { simp only [equiv.perm.coe_one, function.comp.right_id], },
  rw [hf], nth_rewrite 0 hf at h,
  exact antitone_pair_of_not_sorted' h,
end

end tuple
