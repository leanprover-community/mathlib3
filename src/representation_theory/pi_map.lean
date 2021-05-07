/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import ring_theory.simple_module
import linear_algebra.matrix
import linear_algebra.direct_sum_module

open_locale direct_sum classical big_operators
open classical linear_map
noncomputable theory
/-!
# Simple Modules



-/

def submodule.of {R : Type*} [ring R] {M : Type*} [add_comm_group M] [h : module R M]
  (N P : submodule R M) := N.comap P.subtype

def submodule.inclusion {R : Type*} [ring R] {M : Type*} [add_comm_group M] [h : module R M]
  (N P : submodule R M) (h : N ≤ P) : N →ₗ[R] P :=
{ to_fun := λ x, ⟨x.1, h x.2⟩, map_add' := λ ⟨x, hx⟩ ⟨y, hy⟩, rfl, map_smul' := λ r ⟨x, hx⟩, rfl }

def terrible_map {ι : Type*} [fintype ι]
  {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (p : ι → submodule R M) :=
(lsum R (λ i, p i) R (λ i, (p i).inclusion (supr p) (le_supr p i)))

def terrible_map_apply {ι : Type*} [fintype ι]
  {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (p : ι → submodule R M) (x : Π (i : ι), (p i)) (i : ι) :
  ((p i).inclusion (supr p) (le_supr p i)) (x i) = ⟨(x i).1, (le_supr p i : p i ≤ supr p) (x i).2⟩ :=
begin
  ext, simp only [submodule.inclusion, coe_mk],
end

lemma coe_sum {ι : Type*} [fintype ι]
  {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  {p : submodule R M} (x : ι → p) : (↑(∑ i, x i) : M) = ∑ i, ↑(x i) :=
begin
  rw ← submodule.subtype_apply,
  simp only [submodule.subtype_apply, eq_self_iff_true, map_sum],
end

lemma finset.sum_erase' {α : Type*} {β : Type*} [add_comm_group β] [decidable_eq α]
  (s : finset α) {f : α → β} {a : α} (h : a ∈ s) :
  ∑ (x : α) in s.erase a, f x + f a = ∑ (x : α) in s, f x :=
begin
  rw add_comm,
  rw ← finset.sum_insert,
  rw finset.insert_erase,
  exact h,
  exact finset.not_mem_erase a s,
end

lemma submodule.sum_erase_mem_bsupr {ι : Type*} [fintype ι]
  {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M] [module R M]
  (x : ι → M) {p : ι → submodule R M} (j : ι) (hx : ∀ i, x i ∈ p i) :
  ∑ (i : ι) in finset.univ.erase j, (x i) ∈ ⨆ (k : ι) (H : k ≠ j), p k :=
begin
  let p' := λ i (h : i ≠ j), p i,
  have : (⨆ (k : ι) (H : k ≠ j), p k) = ⨆ (k : ι) (H : k ≠ j), p' k H,
  { congr, },
  rw this,
  refine submodule.sum_mem _ (λ c hc, _),
  rw finset.mem_erase at hc,
  have almost : p' c hc.1 ≤ ⨆ i (H : i ≠ j), p' i H := le_bsupr _ _,
  exact almost (hx c),
end


lemma terrible_map_ker {ι : Type*} [fintype ι]
  {R : Type*} [nontrivial R] [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (p : ι → submodule R M) (h : complete_lattice.independent p) : (terrible_map p).ker = ⊥ :=
begin
  simp only [terrible_map, lsum_apply, ker_eq_bot', prod.forall, sum_apply, lsum_apply, coe_proj,
    function.comp_app, function.eval_apply, coe_comp],
  intros x hx,
  ext i,
  change Π (i : ι), (p i) at x,
  simp only [terrible_map_apply] at hx,
  rw ← set_like.coe_eq_coe at hx,
  rw coe_sum at hx,
  simp only [submodule.coe_mk] at hx,
  revert i,
  by_contra,
  push_neg at h,
  cases h with j hj,
  rw ← finset.sum_erase' finset.univ (finset.mem_univ j) at hx,
  simp only [submodule.coe_zero, subtype.val_eq_coe, ← neg_eq_iff_add_eq_zero] at hx,
  simp only [← hx, pi.zero_apply, submodule.coe_zero] at hj,
  have := submodule.disjoint_def.mp (complete_lattice.independent_def.mp h j) (x j) (x j).2,
  have almost : ∑ (i : ι) in finset.univ.erase j, ↑(x i) ∈ ⨆ (k : ι) (H : k ≠ j), p k,
  refine submodule.sum_erase_mem_bsupr _ _ (λ i, (x i).2),
  rw ← submodule.neg_mem_iff at almost,
  rw hx at almost,
  have hmm := this almost,
  rw hx at hj,
  contradiction,
end

lemma fintype.supr_eq_sup {α : Type*} [fintype α] {β : Type*} [complete_lattice β]  (f : α → β) :
 finset.univ.sup f = supr f :=
le_antisymm (finset.sup_le (λ a ha, le_supr f a))
  (supr_le (λ a, finset.le_sup (finset.mem_univ a)))

lemma submodule.mem_supr' {ι : Type*} [fintype ι]
  {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M]
  (p : ι → submodule R M) {x : M} :
  x ∈ supr p ↔ ∃ v : ι → M, (∀ i, v i ∈ p i) ∧ ∑ i, v i = x :=
begin
  rw submodule.supr_eq_span,
  refine ⟨λ h, _, λ h, _⟩,
  refine submodule.span_induction h _ _ _ _,
  { intros y hy,
    rw set.mem_Union at hy,
    cases hy with i hy,
    use λ j, if j = i then y else 0,
    simp only [and_true, finset.mem_univ, if_true, eq_self_iff_true, finset.sum_ite_eq'],
    intro j,
    split_ifs with hj,
    cases hj, exact hy,
    exact submodule.zero_mem (p j) },
  { use 0,
    simp only [pi.zero_apply, implies_true_iff, eq_self_iff_true, and_self,
      finset.sum_const_zero, submodule.zero_mem], },
  { intros x y hx hy,
    rcases hx with ⟨v, hv, hvs⟩,
    rcases hy with ⟨w, hw, hws⟩,
    use v + w,
    refine ⟨λ i, submodule.add_mem _ (hv i) (hw i), _⟩,
    rw ← hvs,
    rw ← hws,
    exact finset.sum_add_distrib },
  { intros r x hx,
    rcases hx with ⟨v, hv, hvs⟩,
    use r • v,
    refine ⟨λ i, submodule.smul_mem _ _ (hv i), _⟩,
    rw ← hvs,
    exact finset.smul_sum.symm, },
  rcases h with ⟨v, hv, hvs⟩,
  have := submodule.sum_mem (supr p) (λ i _, (le_supr p i : p i ≤ supr p) (hv i)),
  rw ← submodule.supr_eq_span,
  rwa hvs at this,
end


lemma terrible_map_range {ι : Type*} [fintype ι]
  {R : Type*} [nontrivial R] [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (p : ι → submodule R M) (h : complete_lattice.independent p) : (terrible_map p).range = ⊤ :=
begin
  ext,
  cases x with x hx,
  simp only [terrible_map, terrible_map_apply, coe_fn_sum, submodule.mem_top, mem_range,
    lsum_apply, coe_proj, fintype.sum_apply, function.comp_app, function.eval_apply,
    iff_true, coe_comp, subtype.val_eq_coe],
  rw submodule.mem_supr' at hx,
  rcases hx with ⟨v, hv, hvs⟩,
  use λ i, (⟨v i, hv i⟩ : (p i)),
  simp [← set_like.coe_eq_coe, coe_sum, hvs],
end

def submodule.prod_equiv_of_independent {ι : Type*} [fintype ι]
  {R : Type*} [comm_ring R] [nontrivial R] {M : Type*} [add_comm_group M] [module R M]
  (p : ι → submodule R M) (h : complete_lattice.independent p) :
  (Π i, p i) ≃ₗ[R] (supr p : submodule R M) :=
by { convert linear_equiv.of_bijective (terrible_map p : _ →ₗ[R] (supr p : submodule R M))
  (terrible_map_ker p h) (terrible_map_range p h) }
