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

- `chain_height α`: The maximal length of chains in `α`.
- `chain_height a`: The maximal length of chains in `α` that start from `a : α`
  (not including `a` itself).

They are both valued in `with_top ℕ`, and equal to `⊤` when the lengths are unbounded.

## Main results

- `exists_chain_of_le_length`: For each `n : ℕ` such that `n ≤ chain_height a`, there exists a
  chain of length `n` starting from `a`.
- `chain_height_eq_one_iff`: An element has height zero iff it is minimal.
- `chain_height_le_of_lt`: If `a < b`, then `chain_height b + 1 ≤ chain_height a`. This implies that
  `chain_height` is decreasing (`chain_height_antitone`).
- `chain_height_eq_sup_chain_height`: `chain_height` is the supremum of all the heights.
- `chain_height_dual`: The maximal length of a poset and is dual is the same.
- `chain_height_add_chain_height_dual_le`: The sum of the height of the same element in `α` and
  `αᵒᵈ` is bounded by `chain_height`.

-/

universes u v

open list

namespace set

section

variables {α : Type u} (s : set α) [has_lt α]

/-- The maximal length of a strictly descending sequence in a poset. -/
noncomputable
def chain_height : with_top ℕ :=
⨆ l : { l : list α // list.chain' (<) l ∧ ∀ i ∈ l, i ∈ s }, l.1.length

-- variable {α}

-- /-- The maximal length of a strictly descending sequence in a poset starting from `a`.
-- Note that `a` itself is not counted in the length. -/
-- noncomputable
-- def chain_height (a : α) : (with_top ℕ) := supr $ λ l : { l // list.chain (>) a l }, l.1.length

instance : nonempty {l : list α // list.chain' (<) l ∧ ∀ i ∈ l, i ∈ s } :=
⟨⟨[], trivial, λ x hx, hx.elim⟩⟩

lemma exists_chain_of_le_length {l : list α} (hl : chain' (<) l) {n : ℕ}
  (hn : n ≤ l.length) : ∃ l' : list α, chain' (<) l' ∧ l' ⊆ l ∧ l'.length = n  :=
begin
  cases n,
  { exact ⟨[], trivial, λ _ h, h.elim, rfl⟩ },
  cases e : l.drop n,
  { exact (nat.lt_le_antisymm (nat.lt_iff_add_one_le.mpr hn) (drop_eq_nil_iff_le.mp e)).elim },
  rw [← l.take_append_drop n, e] at hl,
  refine ⟨_, (chain'_split.mp hl).1, _, _⟩,
  { simp only [list.nil_subset, and_true, list.append_subset_iff, list.cons_subset],
    exact ⟨list.take_subset _ _, list.drop_subset n _ $ by { rw e, exact or.inl rfl }⟩ },
  { simpa [nat.succ_eq_add_one] using n.le_succ.trans hn }
end

lemma exists_chain_of_le_chain_height {n : ℕ} (hn : ↑n ≤ s.chain_height) :
  ∃ l : list α, l.chain' (<) ∧ (∀ x ∈ l, x ∈ s) ∧ l.length = n :=
begin
  cases (le_top : s.chain_height ≤ ⊤).eq_or_lt with ha ha,
  { obtain ⟨_, ⟨⟨l, h₁, h₂⟩, rfl⟩, h₃⟩ :=
      not_bdd_above_iff'.mp ((with_top.supr_coe_eq_top _).mp ha) n,
    obtain ⟨l', h₁', h₂', h₃'⟩ := exists_chain_of_le_length h₁ (le_of_not_ge h₃),
    exact ⟨l', h₁', λ x h, h₂ _ (h₂' h), h₃'⟩ },
  { rw [chain_height, with_top.supr_coe_lt_top] at ha,
    obtain ⟨⟨l, h₁, h₂⟩, e : l.length = _⟩ := nat.Sup_mem (set.range_nonempty _) ha,
    obtain ⟨l', h₁', h₂', h₃'⟩ := exists_chain_of_le_length h₁ _,
    exact ⟨l', h₁', λ x h, h₂ _ (h₂' h), h₃'⟩,
    rwa [e, ← with_top.coe_le_coe, Sup_range, with_top.coe_supr],
    exact ha }
end

variables {s}

lemma le_chain_height_iff {n : ℕ} :
  ↑n ≤ s.chain_height ↔ ∃ l : list α, l.chain' (<) ∧ (∀ x ∈ l, x ∈ s) ∧ l.length = n :=
begin
  refine ⟨s.exists_chain_of_le_chain_height, _⟩,
  rintros ⟨l, h₁, h₂, rfl⟩,
  refine eq.trans_le _ (le_supr _ ⟨l, h₁, h₂⟩),
  refl
end

@[simp]
lemma chain_height_one_le_iff : 1 ≤ s.chain_height ↔ s.nonempty :=
begin
  change ((1 : ℕ) : with_top ℕ) ≤ _ ↔ _,
  rw set.le_chain_height_iff,
  split,
  { rintro ⟨_|⟨x, xs⟩, h₁, h₂, h₃⟩,
    { cases h₃ },
    { exact ⟨x, h₂ _ (or.inl rfl)⟩ } },
  { rintro ⟨x, hx⟩,
    exact ⟨[x], chain.nil, λ y h, (list.mem_singleton.mp h).symm ▸ hx, rfl⟩ }
end

@[simp]
lemma chain_height_eq_zero_iff : s.chain_height = 0 ↔ s = ∅ :=
begin
  rw [← not_iff_not, ← ne.def, ← bot_eq_zero, ← bot_lt_iff_ne_bot, bot_eq_zero,
    ← with_top.one_le_iff_pos, chain_height_one_le_iff, ← ne_empty_iff_nonempty],
end

@[simp]
lemma chain_length_empty : (∅ : set α).chain_height = 0 :=
chain_height_eq_zero_iff.mpr rfl

@[simp]
lemma chain_height_eq_zero_of_empty [is_empty α] : s.chain_height = 0 :=
chain_height_eq_zero_iff.mpr (subsingleton.elim _ _)

lemma with_top.le_iff_forall_coe_le {α : Type*} [preorder α] [no_max_order α] (x y : with_top α) :
  x ≤ y ↔ ∀ n : α, ↑n ≤ x → ↑n ≤ y :=
begin
  split,
  { exact λ e n h, h.trans e },
  { intros H,
    cases y,
    { exact le_top },
    cases x,
    { obtain ⟨y', hy'⟩ := exists_gt y,
      refine ((lt_iff_le_not_le.mp hy').2 _).elim,
      exact with_top.coe_le_coe.mp (H y' le_top) },
    { exact H _ rfl.le } }
end

lemma chain_height_le_of_subset {t : set α} (e : s ⊆ t) : s.chain_height ≤ t.chain_height :=
begin
  rw with_top.le_iff_forall_coe_le,
  simp_rw set.le_chain_height_iff,
  rintro n ⟨l, h₁, h₂, h₃⟩,
  exact ⟨l, h₁, λ _ h, e (h₂ _ h), h₃⟩
end

-- variables {β : Type*} (f : α → β)

-- lemma chain_height_image : (f '' s).chain_height = s.chain_height :=
-- begin

-- end

-- lemma chain_height_le_of_lt {a b : α} (r : b < a) : chain_height b + 1 ≤ chain_height a :=
-- begin
--   erw ← with_top.supr_add,
--   apply supr_le,
--   rintro ⟨l, hl⟩,
--   refine le_trans _ (le_supr _ ⟨_, chain_cons.mpr ⟨r, hl⟩⟩),
--   simp
-- end

-- lemma chain_height_monotone {α : Type u} [preorder α] : monotone (chain_height : α → (with_top ℕ)) :=
-- begin
--   intros a b r,
--   apply supr_le,
--   rintro ⟨l, hl⟩,
--   refine le_trans _ (le_supr _ ⟨l, _⟩),
--   { cases l,
--     { simp },
--     { simp only [gt_iff_lt, list.chain_cons] at ⊢ hl, exact ⟨hl.1.trans_le r, hl.2⟩ } },
--   { refl }
-- end

-- lemma chain_height_le_chain_height (a : α) :
--   chain_height a + 1 ≤ chain_height α :=
-- begin
--   erw ← (with_top ℕ).supr_add,
--   apply supr_le,
--   rintro ⟨l, hl⟩,
--   refine le_trans (le_of_eq _) (le_supr _ ⟨list.cons a l, hl⟩),
--   simp,
-- end

-- lemma chain_height_eq_sup_chain_height :
--   chain_height α = ⨆ a : α, chain_height a + 1 :=
-- begin
--   apply le_antisymm,
--   { apply supr_le,
--     rintro ⟨l, hl⟩,
--     cases l with x xs,
--     { simp },
--     { refine le_trans _ (le_supr _ x),
--       erw ← (with_top ℕ).supr_add,
--       refine le_trans _ (le_supr _ ⟨xs, hl⟩),
--       simp } },
--   { exact supr_le chain_height_le_chain_height }
-- end

-- lemma chain_height_eq_chain_height_bot {α : Type u} [preorder α] [order_top α] :
--   chain_height α = chain_height (⊤ : α) + 1 :=
-- begin
--   rw [chain_height_eq_sup_chain_height, (with_top ℕ).supr_add],
--   congr' 1,
--   exact le_antisymm (supr_le $ λ x, chain_height_monotone le_top) (le_supr chain_height ⊤)
-- end

-- lemma chain_height_dual {α : Type u} [preorder α] : chain_height αᵒᵈ = chain_height α :=
-- begin
--   suffices : ∀ (α : Type u) [preorder α], by exactI chain_height α ≤ chain_height αᵒᵈ,
--   { exact le_antisymm (this αᵒᵈ) (this α) },
--   intros α hα,
--   apply supr_le,
--   rintro ⟨l, hl⟩,
--   refine le_trans _ (le_supr _ _),
--   { exactI ⟨l.reverse, by simpa [chain'_iff_pairwise transitive_gt] using hl⟩ },
--   { simp }
-- end

-- lemma chain_height_add_chain_height_dual_le {α : Type u} [preorder α] (a : α) :
--   chain_height a + @chain_height αᵒᵈ _ a + 1 ≤ chain_height α :=
-- begin
--   cases eq_or_ne (chain_height a) ⊤ with h₁ h₁,
--   { have : chain_height α = ⊤,
--     { rw eq_top_iff, simpa [h₁] using chain_height_le_chain_height a },
--     simp [h₁, this] },
--   cases eq_or_ne (@chain_height αᵒᵈ _ a) ⊤ with h₂ h₂,
--   { have : chain_height α = ⊤,
--     { rw eq_top_iff, simpa [h₂, chain_height_dual] using chain_height_le_chain_height
--         (show αᵒᵈ, from a) },
--     simp [h₁, this] },
--   obtain ⟨⟨l₁, hl₁⟩, hl'₁ : ↑(l₁.length) = chain_height a⟩ :=
--     (with_top ℕ).exists_eq_supr_of_ne_top _ h₁,
--   obtain ⟨⟨l₂, hl₂⟩, hl'₂ : ↑(l₂.length) = chain_height _⟩ :=
--     (with_top ℕ).exists_eq_supr_of_ne_top _ h₂,

--   refine le_trans _ (le_supr _ _),
--   { refine ⟨l₂.reverse ++ a :: l₁, _⟩,
--     rw chain'_split,
--     refine ⟨_, hl₁⟩,
--     rw [← (show (a :: l₂).reverse = l₂.reverse ++ [a], by simp),
--         chain'_iff_pairwise transitive_gt, pairwise_reverse],
--     exact (chain_iff_pairwise transitive_gt).mp hl₂ },
--   { have : (↑l₁.length + ↑l₂.length + 1 : (with_top ℕ)).dom := by refine ⟨⟨_, _⟩, _⟩; trivial,
--     rw [← hl'₁, ← hl'₂, (with_top ℕ).le_coe_iff],
--     simpa [add_comm l₁.length l₂.length, ← add_assoc] }
-- end

-- end

-- variables {α : Type u} [preorder α] {β : Type v} [preorder β] {f : α → β}

-- lemma chain_height_le_of_strict_mono (hf : strict_mono f) (a : α) :
--   chain_height a ≤ chain_height (f a) :=
-- begin
--   apply supr_le,
--   rintro ⟨l, hl⟩,
--   refine le_trans _ (le_supr _ ⟨l.map f, chain_map_of_chain f hf.dual hl⟩),
--   simp
-- end

-- lemma chain_height_le_of_strict_mono (hf : strict_mono f) :
--   chain_height α ≤ chain_height β :=
-- begin
--   rw [chain_height_eq_sup_chain_height, chain_height_eq_sup_chain_height],
--   apply supr_le,
--   intro x,
--   refine le_trans _ (le_supr _ $ f x),
--   exact add_le_add_right (chain_height_le_of_strict_mono hf x) 1
-- end

-- lemma chain_height_eq_of_order_iso (f : α ≃o β) (a : α) :
--   chain_height a = chain_height (f a) :=
-- begin
--   apply (chain_height_le_of_strict_mono f.strict_mono a).antisymm,
--   conv_rhs { rw ← f.left_inv a },
--   exact chain_height_le_of_strict_mono f.symm.strict_mono (f a)
-- end

-- lemma chain_height_eq_of_order_iso (f : α ≃o β) :
--   chain_height α = chain_height β :=
-- le_antisymm (chain_height_le_of_strict_mono f.strict_mono)
--   (chain_height_le_of_strict_mono f.symm.strict_mono)

-- end list
end

end set
