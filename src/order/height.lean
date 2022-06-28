/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import data.list.chain
import data.nat.lattice
import algebra.order.monoid
import order.grade

/-!

# Maximal length of chains

This file contains lemmas to work with the maximal length of strictly descending finite
sequences (chains) in a partially ordered set.

## Main definition

- `sup_chain_length α`: The maximal length of chains in `α`.
- `chain_height a`: The maximal length of chains in `α` that start from `a : α`
  (not including `a` itself).

They are both valued in `enat`, and equal `⊤ : enat` when the lengths are unbounded.

## Main results

- `exists_chain_of_le_length`: For each `n : ℕ` such that `n ≤ chain_height a`, there exists a
  chain of length `n` starting from `a`.
- `chain_height_eq_one_iff`: An element has height zero iff it is minimal.
- `chain_height_le_of_lt`: If `a < b`, then `chain_height b + 1 ≤ chain_height a`. This implies that
  `chain_height` is decreasing (`chain_height_antitone`).
- `sup_chain_length_eq_sup_chain_height`: `sup_chain_length` is the supremum of all the heights.
- `sup_chain_length_dual`: The maximal length of a poset and is dual is the same.
- `chain_height_add_chain_height_dual_le`: The sum of the height of the same element in `α` and
  `αᵒᵈ` is bounded by `sup_chain_length`.

-/

universes u v

namespace list

variables (α : Type u) [preorder α]

/-- The maximal length of a strictly descending sequence in a poset. -/
noncomputable
def sup_chain_length : enat := supr $ λ l : { l : list α // list.chain' (>) l }, l.1.length

variable {α}

/-- The maximal length of a strictly descending sequence in a poset starting from `a`.
Note that `a` itself is not counted in the length. -/
noncomputable
def chain_height (a : α) : enat := supr $ λ l : { l // list.chain (>) a l }, l.1.length

instance (a : α) : nonempty {l // chain (>) a l} :=
⟨by exact ⟨[], list.chain.nil⟩⟩

lemma exists_chain_of_le_length {a : α} {l : list α} (hl : chain (>) a l) {n : ℕ}
  (hn : n ≤ l.length) : ∃ l, chain (>) a l ∧ l.length = n :=
begin
  cases n,
  { exact ⟨[], chain.nil, rfl⟩ },
  cases e : l.drop n,
  { exact (nat.lt_le_antisymm (nat.lt_iff_add_one_le.mpr hn) (drop_eq_nil_iff_le.mp e)).elim },
  rw [← l.take_append_drop n, e] at hl,
  refine ⟨_, (chain_split.mp hl).1, _⟩,
  simpa [nat.succ_eq_add_one] using n.le_succ.trans hn
end

lemma exists_chain_of_le_chain_height {a : α} {n : ℕ} (hn : ↑n ≤ chain_height a) :
  ∃ l, chain (>) a l ∧ l.length = n :=
begin
  by_cases ha : chain_height a = ⊤,
  { obtain ⟨⟨l, hl⟩, hl'⟩ := enat.exists_le_of_supr_eq_top _ ha n,
    apply exists_chain_of_le_length hl,
    simpa using hl' },
  { obtain ⟨⟨l, hl⟩, h : _ = chain_height a⟩ := enat.exists_eq_supr_of_ne_top _ ha,
    apply exists_chain_of_le_length hl,
    rw ← h at hn,
    simpa using hn }
end

lemma exists_chain_of_le_sup_chain_height {n : ℕ} (hn : ↑n ≤ sup_chain_length α) :
  ∃ l : list α, chain' (>) l ∧ l.length = n :=
begin
  cases n,
  { exact ⟨[], by simp⟩ },
  by_cases ha : sup_chain_length α = ⊤,
  { obtain ⟨⟨l, hl⟩, hl'⟩ := enat.exists_le_of_supr_eq_top _ ha (n+1),
    cases l,
    { simp only [list.length, enat.coe_le_coe, nat.succ_ne_zero, nonpos_iff_eq_zero] at hl',
      exact hl'.elim },
    dsimp at *,
    rw [enat.coe_le_coe, add_le_add_iff_right] at hl',
    obtain ⟨l', h, h'⟩ := exists_chain_of_le_length hl hl',
    rw ← h',
    refine ⟨l_hd :: l', h, rfl⟩ },
  casesI is_empty_or_nonempty {l : list α // chain' (>) l} with H H,
  { rw [sup_chain_length, supr, set.range_eq_empty, Sup_empty, le_bot_iff] at hn,
    exact (n.succ_ne_zero (enat.coe_inj.mp hn)).elim },
  { obtain ⟨⟨l, hl⟩, h : ↑l.length = sup_chain_length α⟩ := enat.exists_eq_supr_of_ne_top _ ha,
    cases l,
    { simp only [← h, list.length, enat.coe_le_coe, nat.succ_ne_zero, nonpos_iff_eq_zero] at hn,
      exact hn.elim },
    have : n ≤ l_tl.length,
    { rw [← h, enat.coe_le_coe] at hn, exact (add_le_add_iff_right 1).mp hn },
    obtain ⟨l', h, h'⟩ := exists_chain_of_le_length hl this,
    rw ← h',
    refine ⟨l_hd :: l', h, rfl⟩ }
end

@[simp]
lemma chain_height_eq_zero_iff (a : α) : chain_height a = 0 ↔ is_min a :=
begin
  rw ← not_iff_not,
  delta is_min,
  push_neg,
  simp_rw ← lt_iff_le_not_le,
  rw enat.ne_zero_iff_one_le,
  split,
  { intro h,
    obtain ⟨l, hl, hl'⟩ := exists_chain_of_le_chain_height h,
    obtain ⟨b, rfl⟩ := list.length_eq_one.mp hl',
    cases hl,
    exact ⟨b, by assumption⟩ },
  { rintro ⟨b, r⟩,
    refine le_trans _ (le_supr _ ⟨[b], by simpa⟩),
    simp }
end

@[simp]
lemma sup_chain_length_eq_zero_iff  : sup_chain_length α = 0 ↔ is_empty α :=
begin
  rw [← not_iff_not, ← ne.def, enat.ne_zero_iff_one_le],
  split,
  { rintros h₁ h₂,
    obtain ⟨⟨_|_, h⟩, h'⟩ := exists_chain_of_le_sup_chain_height h₁,
    { simpa using h'.2 },
    { exactI is_empty.false w_hd } },
  { rw not_is_empty_iff,
    rintro ⟨a⟩,
    refine le_trans _ (le_supr _ ⟨[a], _⟩); simp }
end

@[simp]
lemma sup_chain_length_eq_zero_of_empty [h : is_empty α] : sup_chain_length α = 0 :=
sup_chain_length_eq_zero_iff.mpr h

lemma chain_height_le_of_lt {a b : α} (r : b < a) : chain_height b + 1 ≤ chain_height a :=
begin
  erw ← enat.supr_add,
  apply supr_le,
  rintro ⟨l, hl⟩,
  refine le_trans _ (le_supr _ ⟨_, chain_cons.mpr ⟨r, hl⟩⟩),
  simp
end

lemma chain_height_monotone : monotone (chain_height : α → enat) :=
begin
  intros a b r,
  apply supr_le,
  rintro ⟨l, hl⟩,
  refine le_trans _ (le_supr _ ⟨l, _⟩),
  { cases l,
    { simp },
    { simp only [gt_iff_lt, list.chain_cons] at ⊢ hl, exact ⟨hl.1.trans_le r, hl.2⟩ } },
  { refl }
end

lemma chain_height_le_sup_chain_length (a : α) :
  chain_height a + 1 ≤ sup_chain_length α :=
begin
  erw ← enat.supr_add,
  apply supr_le,
  rintro ⟨l, hl⟩,
  refine le_trans (le_of_eq _) (le_supr _ ⟨list.cons a l, hl⟩),
  simp,
end

lemma sup_chain_length_eq_sup_chain_height :
  sup_chain_length α = ⨆ a : α, chain_height a + 1 :=
begin
  apply le_antisymm,
  { apply supr_le,
    rintro ⟨l, hl⟩,
    cases l with x xs,
    { simp },
    { refine le_trans _ (le_supr _ x),
      erw ← enat.supr_add,
      refine le_trans _ (le_supr _ ⟨xs, hl⟩),
      simp } },
  { exact supr_le chain_height_le_sup_chain_length }
end

lemma sup_chain_length_eq_chain_height_bot [order_top α] :
  sup_chain_length α = chain_height (⊤ : α) + 1 :=
begin
  rw [sup_chain_length_eq_sup_chain_height, enat.supr_add],
  congr' 1,
  exact le_antisymm (supr_le $ λ x, chain_height_monotone le_top) (le_supr chain_height ⊤)
end

lemma sup_chain_length_dual : sup_chain_length αᵒᵈ = sup_chain_length α :=
begin
  suffices : ∀ (α : Type u) [preorder α], by exactI sup_chain_length α ≤ sup_chain_length αᵒᵈ,
  { exact le_antisymm (this αᵒᵈ) (this α) },
  intros α hα,
  apply supr_le,
  rintro ⟨l, hl⟩,
  refine le_trans _ (le_supr _ _),
  { exact ⟨l.reverse, by simpa [chain'_iff_pairwise transitive_gt] using hl⟩ },
  { simp }
end

lemma chain_height_add_chain_height_dual_le (a : α) :
  chain_height a + @chain_height αᵒᵈ _ a + 1 ≤ sup_chain_length α :=
begin
  cases eq_or_ne (chain_height a) ⊤ with h₁ h₁,
  { have : sup_chain_length α = ⊤,
    { rw eq_top_iff, simpa [h₁] using chain_height_le_sup_chain_length a },
    simp [h₁, this] },
  cases eq_or_ne (@chain_height αᵒᵈ _ a) ⊤ with h₂ h₂,
  { have : sup_chain_length α = ⊤,
    { rw eq_top_iff, simpa [h₂, sup_chain_length_dual] using chain_height_le_sup_chain_length
        (show αᵒᵈ, from a) },
    simp [h₁, this] },
  obtain ⟨⟨l₁, hl₁⟩, hl'₁ : ↑(l₁.length) = chain_height a⟩ :=
    enat.exists_eq_supr_of_ne_top _ h₁,
  obtain ⟨⟨l₂, hl₂⟩, hl'₂ : ↑(l₂.length) = chain_height _⟩ :=
    enat.exists_eq_supr_of_ne_top _ h₂,

  refine le_trans _ (le_supr _ _),
  { refine ⟨l₂.reverse ++ a :: l₁, _⟩,
    rw chain'_split,
    refine ⟨_, hl₁⟩,
    rw [← (show (a :: l₂).reverse = l₂.reverse ++ [a], by simp),
        chain'_iff_pairwise transitive_gt, pairwise_reverse],
    exact (chain_iff_pairwise transitive_gt).mp hl₂ },
  { have : (↑l₁.length + ↑l₂.length + 1 : enat).dom := by refine ⟨⟨_, _⟩, _⟩; trivial,
    rw [← hl'₁, ← hl'₂, enat.le_coe_iff],
    simpa [add_comm l₁.length l₂.length, ← add_assoc] }
end

variables {β : Type v} [partial_order β] {f : α → β}

lemma chain_height_le_of_strict_mono (hf : strict_mono f) (a : α) :
  chain_height a ≤ chain_height (f a) :=
begin
  apply supr_le,
  rintro ⟨l, hl⟩,
  refine le_trans _ (le_supr _ ⟨l.map f, chain_map_of_chain f hf.dual hl⟩),
  simp
end

lemma sup_chain_length_le_of_strict_mono (hf : strict_mono f) :
  sup_chain_length α ≤ sup_chain_length β :=
begin
  rw [sup_chain_length_eq_sup_chain_height, sup_chain_length_eq_sup_chain_height],
  apply supr_le,
  intro x,
  refine le_trans _ (le_supr _ $ f x),
  exact add_le_add_right (chain_height_le_of_strict_mono hf x) 1
end

lemma chain_height_eq_of_order_iso (f : α ≃o β) (a : α) :
  chain_height a = chain_height (f a) :=
begin
  apply (chain_height_le_of_strict_mono f.strict_mono a).antisymm,
  conv_rhs { rw ← f.left_inv a },
  exact chain_height_le_of_strict_mono f.symm.strict_mono (f a)
end

lemma sup_chain_length_eq_of_order_iso (f : α ≃o β) :
  sup_chain_length α = sup_chain_length β :=
le_antisymm (sup_chain_length_le_of_strict_mono f.strict_mono)
  (sup_chain_length_le_of_strict_mono f.symm.strict_mono)

end list
