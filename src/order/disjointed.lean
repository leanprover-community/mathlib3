/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import order.partial_sups

/-!
# Consecutive differences of sets

This file defines a way to make a sequence of sets into a sequence of disjoint sets.

## Main declarations

* `disjointed f`: Yields the sequence of sets `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ∪ f 1)`, ... This
  sequence has the same union as `f 0`, `f 1`, `f 2` but with disjoint sets.
-/

variables {α β : Type*}

namespace set

/-- If `f : ℕ → set α` is a sequence of sets, then `disjointed f` is
  the sequence formed with each set subtracted from the later ones
  in the sequence, to form a disjoint sequence. -/
def disjointed (f : ℕ → set α) (n : ℕ) : set α := f n ∩ (⋂ i < n, (f i)ᶜ)

variables {f : ℕ → set α} {n : ℕ}

lemma disjoint_disjointed : pairwise (disjoint on disjointed f) :=
λ i j h, begin
  wlog h' : i ≤ j; [skip, {revert a, exact (this h.symm).symm}],
  rintro a ⟨⟨h₁, _⟩, h₂, h₃⟩, simp at h₃,
  exact h₃ _ (lt_of_le_of_ne h' h) h₁
end

-- a more useful version might be `∀ i j x, x ∈ disjointed f i → x ∈ disjointed f j → i = j`
lemma disjoint_disjointed' :
  ∀ i j, i ≠ j → (disjointed f i) ∩ (disjointed f j) = ∅ :=
λ i j hij, disjoint_iff.1 $ disjoint_disjointed i j hij

lemma disjointed_subset : disjointed f n ⊆ f n := inter_subset_left _ _

lemma Union_lt_succ : (⋃ i < nat.succ n, f i) = f n ∪ (⋃ i < n, f i) :=
ext $ λ a, by simp [nat.lt_succ_iff_lt_or_eq, or_and_distrib_right, exists_or_distrib, or_comm]

lemma Inter_lt_succ : (⋂ i < nat.succ n, f i) = f n ∩ (⋂ i < n, f i) :=
ext $ λ a, by simp [nat.lt_succ_iff_lt_or_eq, or_imp_distrib, forall_and_distrib, and_comm]

lemma disjointed_induct {p : set α → Prop} (h₁ : p (f n)) (h₂ : ∀ t i, p t → p (t \ f i)) :
  p (disjointed f n) :=
begin
  rw disjointed,
  generalize_hyp : f n = t at h₁ ⊢,
  induction n,
  case nat.zero { simp [nat.not_lt_zero, h₁] },
  case nat.succ : n ih {
    rw [Inter_lt_succ, inter_comm ((f n)ᶜ), ← inter_assoc],
    exact h₂ _ n ih }
end

lemma disjointed_of_mono (hf : monotone f) :
  disjointed f (n + 1) = f (n + 1) \ f n :=
have (⋂ i (h : i < n + 1), (f i)ᶜ) = (f n)ᶜ,
  from le_antisymm
    (infi_le_of_le n $ infi_le_of_le (nat.lt_succ_self _) $ subset.refl _)
    (le_infi $ λ i, le_infi $ λ hi, compl_le_compl $ hf $ nat.le_of_succ_le_succ hi),
by simp [disjointed, this, diff_eq]

open_locale classical

lemma subset_Union_disjointed : f n ⊆ ⋃ i < n.succ, disjointed f i :=
λ x hx,
  have ∃ k, x ∈ f k, from ⟨n, hx⟩,
  have hn : ∀ (i : ℕ), i < nat.find this → x ∉ f i,
    from λ i, nat.find_min this,
  have hlt : nat.find this < n.succ,
    from (nat.find_min' this hx).trans_lt n.lt_succ_self,
  mem_bUnion hlt ⟨nat.find_spec this, mem_bInter hn⟩

lemma Union_disjointed : (⋃ n, disjointed f n) = (⋃ n, f n) :=
subset.antisymm (Union_subset_Union $ λ i, inter_subset_left _ _)
  (Union_subset $ λ n, subset.trans subset_Union_disjointed (bUnion_subset_Union _ _))

lemma Union_disjointed_of_mono (hf : monotone f) (n : ℕ) :
  (⋃ i < n.succ, disjointed f i) = f n :=
subset.antisymm (bUnion_subset $ λ k hk, subset.trans disjointed_subset $ hf $ nat.lt_succ_iff.1 hk)
  subset_Union_disjointed

lemma Union_inter_disjointed_eq {a : set α} (ha : a ⊆ ⋃ n, f n) :
  (⋃ n, a ∩ disjointed f n) = a :=
by rwa [← inter_Union, set.Union_disjointed, inter_eq_left_iff_subset]

lemma pairwise_disjoint_on_inter_disjointed {a : set α} :
  pairwise $ disjoint on (λ n, a ∩ disjointed f n) :=
pairwise_disjoint_on_inter disjoint_disjointed

end set
