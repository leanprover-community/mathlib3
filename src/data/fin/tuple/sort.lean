/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.finset.sort
import data.list.fin_range
import data.prod.lex
import group_theory.perm.basic

/-!

# Sorting tuples by their values

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

lemma graph_equiv₂_apply (f : fin n → α) (i : fin n) :
  graph_equiv₂ f i = graph_equiv₁ f (sort f i) :=
((graph_equiv₁ f).apply_symm_apply _).symm

lemma self_comp_sort (f : fin n → α) : f ∘ sort f = graph.proj ∘ graph_equiv₂ f :=
show graph.proj ∘ ((graph_equiv₁ f) ∘ (graph_equiv₁ f).symm) ∘ (graph_equiv₂ f).to_equiv = _,
  by simp

lemma monotone_proj (f : fin n → α) : monotone (graph.proj : graph f → α) :=
begin
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_|h),
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

/-- If two permutations of a tuple `f` are both monotone, then they are equal. -/
lemma unique_monotone [partial_order α] {f : fin n → α} {σ τ : equiv.perm (fin n)}
  (hfσ : monotone (f ∘ σ)) (hfτ : monotone (f ∘ τ)) : f ∘ σ = f ∘ τ :=
of_fn_injective $ eq_of_perm_of_sorted
  ((σ.of_fn_comp_perm f).trans (τ.of_fn_comp_perm f).symm) hfσ.of_fn_sorted hfτ.of_fn_sorted

variables [linear_order α] {f : fin n → α} {σ : equiv.perm (fin n)}

/-- A permutation `σ` equals `sort f` if and only if the map `i ↦ (f (σ i), σ i)` is
strictly monotone (w.r.t. the lexicographic ordering on the target). -/
lemma eq_sort_iff' : σ = sort f ↔ strict_mono (σ.trans $ graph_equiv₁ f) :=
begin
  split; intro h,
  { rw [h, sort, equiv.trans_assoc, equiv.symm_trans_self], exact (graph_equiv₂ f).strict_mono },
  { have := subsingleton.elim (graph_equiv₂ f) (h.order_iso_of_surjective _ $ equiv.surjective _),
    ext1, exact (graph_equiv₁ f).apply_eq_iff_eq_symm_apply.1 (fun_like.congr_fun this x).symm },
end

/-- A permutation `σ` equals `sort f` if and only if `f ∘ σ` is monotone and whenever `i < j`
and `f (σ i) = f (σ j)`, then `σ i < σ j`. This means that `sort f` is the lexicographically
smallest permutation `σ` such that `f ∘ σ` is monotone. -/
lemma eq_sort_iff : σ = sort f ↔ monotone (f ∘ σ) ∧ ∀ i j, i < j → f (σ i) = f (σ j) → σ i < σ j :=
begin
  rw eq_sort_iff',
  refine ⟨λ h, ⟨(monotone_proj f).comp h.monotone, λ i j hij hfij, _⟩, λ h i j hij, _⟩,
  { exact (((prod.lex.lt_iff _ _).1 $ h hij).resolve_left hfij.not_lt).2 },
  { obtain he|hl := (h.1 hij.le).eq_or_lt; apply (prod.lex.lt_iff _ _).2,
    exacts [or.inr ⟨he, h.2 i j hij he⟩, or.inl hl] },
end

/-- The permutation that sorts `f` is the identity if and only if `f` is monotone. -/
lemma sort_eq_refl_iff_monotone : sort f = equiv.refl _ ↔ monotone f :=
begin
  rw [eq_comm, eq_sort_iff, equiv.coe_refl, function.comp.right_id],
  simp only [id.def, and_iff_left_iff_imp],
  exact λ _ _ _ hij _, hij,
end

/-- A permutation of a tuple `f` is `f` sorted if and only if it is monotone. -/
lemma comp_sort_eq_comp_iff_monotone : f ∘ σ = f ∘ sort f ↔ monotone (f ∘ σ) :=
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
