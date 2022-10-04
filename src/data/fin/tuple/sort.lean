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
  simp only [(<), pi.lex, pi.to_lex_apply, function.comp_app],
  refine ⟨i, λ k (hik : k < i), _, _⟩,
  { rw [equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans h₁).ne], },
  { simpa only [equiv.swap_apply_left], }
end

/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
lemma unique_monotone [partial_order α] {f : fin n → α} {σ τ : equiv.perm (fin n)}
  (hfσ : monotone (f ∘ σ)) (hfτ : monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
of_fn_injective $ eq_of_perm_of_sorted
  ((σ.of_fn_comp_perm f).trans (τ.of_fn_comp_perm f).symm) hfσ.of_fn_sorted hfτ.of_fn_sorted

variables [linear_order α] {f : fin n → α} {σ : equiv.perm (fin n)}

lemma graph_equiv₁_apply (i : fin n) : (graph_equiv₁ f i).val = to_lex (f i, i) := rfl

/-- If `f` is monotone, then the map that sends `i` to `(f i, i)` is an order isomorphism. -/
def order_iso_of_monotone (hf : monotone f) : fin n ≃o graph f :=
{ to_equiv := graph_equiv₁ f,
  map_rel_iff' :=
  begin
    intros a b,
    simp_rw [←subtype.coe_le_coe, ←subtype.val_eq_coe, graph_equiv₁_apply, prod.lex.le_iff],
    refine ⟨λ h, h.elim (λ h', _) (λ h', h'.2),
            λ h, (hf h).lt_or_eq.elim or.inl (λ h', or.inr ⟨h', h⟩)⟩,
    by_contra' hh,
    exact not_le_of_lt h' (hf hh.le),
  end }

lemma order_iso_of_monotone_eq (hf : monotone f) : order_iso_of_monotone hf = graph_equiv₂ f :=
(eq_iff_true_of_subsingleton _ _).mpr trivial

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
lemma sort_eq_refl_iff_monotone : sort f = equiv.refl _ ↔ monotone f :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have := monotone_sort f,
    rwa [h, equiv.coe_refl, function.comp.right_id] at this, },
  { simp only [sort],
    change (graph_equiv₂ f).to_equiv.trans (order_iso_of_monotone h).to_equiv.symm = _,
    simp only [order_iso_of_monotone_eq h, equiv.self_trans_symm], }
end

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
lemma comp_sort_eq_comp_iff_monotone :
  f ∘ σ = f ∘ sort f ↔ monotone (f ∘ σ) :=
⟨λ h, h.symm ▸ monotone_sort f, λ h, unique_monotone h (monotone_sort f)⟩

/-- The sorted versions of a tuple `f` and of any permutation of `f` agree. -/
lemma comp_perm_comp_sort_eq_comp_sort : (f ∘ σ) ∘ (sort (f ∘ σ)) = f ∘ sort f :=
begin
  rw [function.comp.assoc, ← equiv.perm.coe_mul],
  exact unique_monotone (monotone_sort (f ∘ σ)) (monotone_sort f),
end

/-- If a permutation `f ∘ σ` of the tuple `f` is not the same as `f ∘ sort f`, then `f ∘ σ`
has a pair of strictly decreasing entries. -/
lemma antitone_pair_of_not_sorted' (h : f ∘ σ ≠ f ∘ sort f) :
  ∃ i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i :=
by { contrapose! h, exact comp_sort_eq_comp_iff_monotone.mpr (monotone_iff_forall_lt.mpr h) }

/-- If the tuple `f` is not the same as `f ∘ sort f`, then `f` has a pair of strictly decreasing
entries. -/
lemma antitone_pair_of_not_sorted (h : f ≠ f ∘ sort f) : ∃ i j, i < j ∧ f j < f i :=
antitone_pair_of_not_sorted' (id h : f ∘ equiv.refl _ ≠ _)

end tuple
