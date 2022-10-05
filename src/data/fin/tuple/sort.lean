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

lemma graph_equiv₂_apply (i : fin n) : (graph_equiv₂ f i).val = to_lex (f (sort f i), sort f i) :=
begin
  simp only [sort, graph_equiv₁, to_lex, prod.ext_iff, subtype.val_eq_coe, equiv.coe_trans,
             equiv.coe_fn_symm_mk, rel_iso.coe_fn_to_equiv, function.comp_app, equiv.coe_refl,
             id.def, eq_self_iff_true, and_true],
  have := (graph_equiv₂ f i).prop,
  simp only [graph, finset.mem_image, finset.mem_univ, exists_true_left] at this,
  obtain ⟨j, hj⟩ := this,
  rw ← hj,
end

lemma graph_equiv₂_apply' (i : fin n) :
  graph_equiv₂ f i = ⟨to_lex (f (sort f i), sort f i),
                      (@graph_equiv₂_apply _ _ _ f i) ▸ (graph_equiv₂ f i).prop⟩ :=
by simp [subtype.ext_iff, ← subtype.val_eq_coe, graph_equiv₂_apply]

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. -/
lemma eq_sort_iff : σ = sort f ↔ monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j :=
begin
  refine ⟨λ h, ⟨@eq.substr _ (λ (τ : equiv.perm (fin n)), monotone (f ∘ τ)) _ _ h (monotone_sort f),
                λ i j hij hfij, _⟩, λ h₁, _⟩,
  { have := (order_iso.lt_iff_lt (graph_equiv₂ f)).mpr hij,
    rw [graph_equiv₂_apply', graph_equiv₂_apply' j, subtype.mk_lt_mk, prod.lex.lt_iff] at this,
    simp only at this,
    rw [h] at hfij ⊢,
    exact this.elim (λ h₁, false.elim $ hfij.not_lt h₁) (λ h₁, h₁.2), },
  { obtain ⟨hf, h₂⟩ := h₁,
    let oi : fin n ≃o graph f :=
    { to_equiv := σ.trans (graph_equiv₁ f),
      map_rel_iff' :=
      begin
        intros a b,
        simp only [equiv.coe_trans, function.comp_app],
        simp_rw [←subtype.coe_le_coe, ←subtype.val_eq_coe, graph_equiv₁_apply, prod.lex.le_iff],
        refine ⟨λ h, _, λ h, _⟩,
        { by_contra' hh,
          have := hf hh.le, simp only [function.comp_app] at this,
          have H := h.resolve_left this.not_lt,
          exact H.2.not_lt (h₂ b a hh H.1.symm), },
        { have := hf h, simp only [function.comp_app] at this,
          exact this.lt_or_eq.elim or.inl (λ he, or.inr ⟨he, h.lt_or_eq.elim
             (λ hl, (h₂ a b hl he).le) (λ he', (congr_arg σ he').le)⟩), }
      end },
    ext,
    simp only [sort, subsingleton.elim (graph_equiv₂ f) oi, equiv.coe_trans, function.comp_app,
               equiv.symm_apply_apply], }
end

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
lemma sort_eq_refl_iff_monotone : sort f = equiv.refl _ ↔ monotone f :=
begin
  rw [eq_comm, eq_sort_iff, equiv.coe_refl, function.comp.right_id],
  simp only [id.def, and_iff_left_iff_imp],
  exact λ _ _ _ hij _, hij,
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
