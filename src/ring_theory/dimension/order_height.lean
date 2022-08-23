/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import data.list.chain
import data.nat.lattice
import algebra.order.monoid
import order.grade
import tactic.tfae

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

def subchain : set (list α) :=
{ l | list.chain' (<) l ∧ ∀ i ∈ l, i ∈ s }

/-- The maximal length of a strictly descending sequence in a poset. -/
noncomputable
def chain_height : with_top ℕ :=
⨆ l ∈ s.subchain, list.length l

lemma chain_height_eq_supr_subtype : s.chain_height = ⨆ l : s.subchain, l.1.length :=
begin
  rw supr_subtype,
  refl,
end

-- variable {α}

-- /-- The maximal length of a strictly descending sequence in a poset starting from `a`.
-- Note that `a` itself is not counted in the length. -/
-- noncomputable
-- def chain_height (a : α) : (with_top ℕ) := supr $ λ l : { l // list.chain (>) a l }, l.1.length

lemma nil_mem_subchain : [] ∈ s.subchain :=
⟨trivial, λ x hx, hx.elim⟩

instance : nonempty s.subchain :=
⟨⟨[], s.nil_mem_subchain⟩⟩

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
  ∃ l ∈ s.subchain, list.length l = n :=
begin
  cases (le_top : s.chain_height ≤ ⊤).eq_or_lt with ha ha; rw chain_height_eq_supr_subtype at ha,
  { obtain ⟨_, ⟨⟨l, h₁, h₂⟩, rfl⟩, h₃⟩ :=
      not_bdd_above_iff'.mp ((with_top.supr_coe_eq_top _).mp ha) n,
    obtain ⟨l', h₁', h₂', h₃'⟩ := exists_chain_of_le_length h₁ (le_of_not_ge h₃),
    exact ⟨l', ⟨h₁', λ x h, h₂ _ (h₂' h)⟩, h₃'⟩ },
  { rw with_top.supr_coe_lt_top at ha,
    obtain ⟨⟨l, h₁, h₂⟩, e : l.length = _⟩ := nat.Sup_mem (set.range_nonempty _) ha,
    obtain ⟨l', h₁', h₂', h₃'⟩ := exists_chain_of_le_length h₁ _,
    exact ⟨l', ⟨h₁', λ x h, h₂ _ (h₂' h)⟩, h₃'⟩,
    rwa [e, ← with_top.coe_le_coe, Sup_range, with_top.coe_supr, ← chain_height_eq_supr_subtype],
    exact ha }
end

variables {s}

lemma le_chain_height_iff {n : ℕ} :
  ↑n ≤ s.chain_height ↔ ∃ l ∈ s.subchain, list.length l = n :=
begin
  refine ⟨s.exists_chain_of_le_chain_height, _⟩,
  rintros ⟨l, h, rfl⟩,
  refine eq.trans_le _ (le_supr₂ l h),
  refl
end

lemma length_le_chain_height_of_mem_subchain (l ∈ s.subchain) :
  ↑l.length ≤ s.chain_height :=
le_chain_height_iff.mpr ⟨l, H, rfl⟩


@[simp]
lemma chain_height_one_le_iff : 1 ≤ s.chain_height ↔ s.nonempty :=
begin
  change ((1 : ℕ) : with_top ℕ) ≤ _ ↔ _,
  rw set.le_chain_height_iff,
  split,
  { rintro ⟨_|⟨x, xs⟩, ⟨h₁, h₂⟩, h₃⟩,
    { cases h₃ },
    { exact ⟨x, h₂ _ (or.inl rfl)⟩ } },
  { rintro ⟨x, hx⟩,
    exact ⟨[x], ⟨chain.nil, λ y h, (list.mem_singleton.mp h).symm ▸ hx⟩, rfl⟩ }
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

variables {β : Type*} [has_lt β]

lemma chain_height_le_chain_height_tfae (s : set α) (t : set β) :
  tfae [s.chain_height ≤ t.chain_height,
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, list.length l = list.length l',
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, list.length l ≤ list.length l'] :=
begin
  tfae_have : 1 → 2,
  { intros e l hl,
    simp_rw @eq_comm _ l.length,
    have := length_le_chain_height_of_mem_subchain l hl,
    exact le_chain_height_iff.mp (this.trans e) },
  tfae_have : 2 → 3,
  { exact forall₂_imp (λ l hl ⟨l', h₁, h₂⟩, ⟨l', h₁, h₂.le⟩) },
  tfae_have : 3 → 1,
  { intros H,
    refine supr₂_le _,
    intros l hl,
    obtain ⟨l', h₁, h₂⟩ := H l hl,
    exact (with_top.coe_le_coe.mpr h₂).trans (length_le_chain_height_of_mem_subchain l' h₁) },
  tfae_finish
end

lemma chain_height_le_chain_height_iff {t : set β} :
  s.chain_height ≤ t.chain_height ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, list.length l = list.length l' :=
(chain_height_le_chain_height_tfae s t).out 0 1

lemma chain_height_le_chain_height_iff_le {t : set β} :
  s.chain_height ≤ t.chain_height ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, list.length l ≤ list.length l' :=
(chain_height_le_chain_height_tfae s t).out 0 2


lemma chain_height_add_le_chain_height_add (s : set α) (t : set β) (n m : ℕ) :
  s.chain_height + n ≤ t.chain_height + m ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, list.length l + n ≤ list.length l' + m :=
begin
  split,
  { intros e l hl,
    cases le_or_gt m (l.length + n),
    swap, { refine ⟨[], set.nil_mem_subchain _, h.lt.le.trans_eq (zero_add _).symm⟩ },
    have : ↑(l.length + n - m) ≤ t.chain_height,
    { apply with_top.le_of_add_le_add_right (with_top.some_lt_none m).ne,
      rw [with_top.some_eq_coe, ← with_top.coe_add, tsub_add_cancel_of_le h, with_top.coe_add],
      exact (add_le_add (length_le_chain_height_of_mem_subchain l hl) rfl.le).trans e },
    obtain ⟨l', H, e⟩ := le_chain_height_iff.mp this,
    exact ⟨l', H, by rw [e, tsub_add_cancel_of_le h]⟩ },
  { intro H,
    have : ↑n ≤ t.chain_height + ↑m,
    { obtain ⟨l₀, H₀, e₀⟩ := H [] s.nil_mem_subchain,
      have := length_le_chain_height_of_mem_subchain l₀ H₀,
      calc (n : with_top ℕ) = nil.length + n      : (zero_add _).symm
                        ... ≤ l₀.length + m       : with_top.coe_le_coe.mpr e₀
                        ... ≤ t.chain_height + ↑m : add_le_add this rfl.le },
    rw ← tsub_add_cancel_of_le this,
    refine add_le_add _ rfl.le,
    apply supr₂_le _,
    intros l hl,
    obtain ⟨l', H', e⟩ := H l hl,
    apply with_top.le_of_add_le_add_right (with_top.some_lt_none n).ne,
    rw [with_top.some_eq_coe, tsub_add_cancel_of_le this],
    refine (with_top.coe_le_coe.mpr e).trans _,
    rw with_top.coe_add,
    exact add_le_add (length_le_chain_height_of_mem_subchain l' H') rfl.le },
end

lemma chain_height_le_of_subset {t : set α} (e : s ⊆ t) : s.chain_height ≤ t.chain_height :=
begin
  rw chain_height_le_chain_height_iff,
  intros l hl,
  exact ⟨l, ⟨hl.1, λ i hi, e (hl.2 i hi)⟩, rfl⟩
end

lemma cons_mem_subchain_iff {x : α} {xs : list α} :
  x :: xs ∈ s.subchain ↔ x ∈ s ∧ xs ∈ s.subchain ∧ (∀ y ∈ xs.head', x < y) :=
begin
  split,
  { intro h,
    exact ⟨h.2 _ (or.inl rfl), ⟨(chain'_cons'.mp h.1).2, λ i hi, h.2 _ (or.inr hi)⟩,
      (chain'_cons'.mp h.1).1⟩ },
  { rintro ⟨h₁, h₂, h₃⟩,
    split,
    { rw chain'_cons', exact ⟨h₃, h₂.1⟩ },
    { rintros i (rfl|hi), exacts [h₁, h₂.2 _ hi] } }
end

lemma chain_height_image {α β : Type*} [has_lt α] [has_lt β]
  (f : α → β) (hf : ∀ {x y}, x < y ↔ f x < f y) (s : set α) :
  (f '' s).chain_height = s.chain_height :=
begin
  apply le_antisymm; rw chain_height_le_chain_height_iff,
  { suffices : ∀ l ∈ (f '' s).subchain, ∃ l' ∈ s.subchain, list.map f l' = l,
    { intros l hl, obtain ⟨l', h₁, rfl⟩ := this l hl, exact ⟨l', h₁, list.length_map _ _⟩ },
    intro l,
    induction l with x xs hx,
    { exact λ _, ⟨nil, ⟨trivial, λ _ h, h.elim⟩, rfl⟩ },
    { intros h,
      rw cons_mem_subchain_iff at h,
      obtain ⟨⟨x, hx', rfl⟩, h₁, h₂⟩ := h,
      obtain ⟨l', h₃, rfl⟩ := hx h₁,
      refine ⟨x :: l', cons_mem_subchain_iff.mpr ⟨hx', h₃, _⟩, rfl⟩,
      cases l', { simp }, { simpa [← hf] using h₂ } } },
  { intros l hl,
    refine ⟨l.map f, ⟨_, _⟩, _⟩,
    { simp_rw [chain'_map, ← hf], exact hl.1 },
    { intros _ e, obtain ⟨a, ha, rfl⟩ := mem_map.mp e, exact set.mem_image_of_mem _ (hl.2 _ ha) },
    { rw length_map } },
end

end

section

variables {α : Type u} (s : set α) [preorder α]

lemma chain_height_order_dual (t : set αᵒᵈ) (e : s = t) : s.chain_height = t.chain_height :=
begin
  subst e,
  apply le_antisymm,
  all_goals
  { rw chain_height_le_chain_height_iff,
    rintros l ⟨h₁, h₂⟩,
    exact ⟨l.reverse, ⟨chain'_reverse.mpr h₁,
      λ i h, h₂ i (list.mem_reverse.mp h)⟩, (list.length_reverse _).symm⟩ },
end

lemma chain_height_eq_supr_Ici :
  s.chain_height = ⨆ i ∈ s, set.chain_height (s ∩ set.Ici i) :=
begin
  apply le_antisymm,
  { refine supr₂_le _,
    rintros (_|⟨x, xs⟩) h,
    { exact zero_le _ },
    { apply le_trans _ (le_supr₂ x (cons_mem_subchain_iff.mp h).1),
      apply length_le_chain_height_of_mem_subchain,
      refine ⟨h.1, λ i hi, ⟨h.2 i hi, _⟩⟩,
      cases hi, { exact hi.symm.le },
      cases chain'_iff_pairwise.mp h.1 with _ _ h',
      exact (h' _ hi).le } },
  { exact supr₂_le (λ i hi, chain_height_le_of_subset (set.inter_subset_left _ _)) }
end

lemma chain_height_eq_supr_Iic :
  s.chain_height = ⨆ i ∈ s, set.chain_height (s ∩ set.Iic i) :=
begin
  rw [chain_height_order_dual s s rfl, chain_height_eq_supr_Ici],
  congr, ext1, congr, ext1,
  apply chain_height_order_dual,
  refl,
end

lemma chain_height_insert_of_forall_le (x : α) (hx : ∀ a ∈ s, x < a) :
  (insert x s).chain_height = s.chain_height + 1 :=
begin
  rw ← add_zero (insert x s).chain_height,
  change (insert x s).chain_height + (0 : ℕ) = s.chain_height + (1 : ℕ),
  apply le_antisymm; rw chain_height_add_le_chain_height_add,
  { rintro (_|⟨y, ys⟩) h,
    { exact ⟨[], nil_mem_subchain _, zero_le _⟩ },
    { have h' := cons_mem_subchain_iff.mp h,
      refine ⟨ys, ⟨h'.2.1.1, λ i hi, _⟩, by simp⟩,
      apply (h'.2.1.2 i hi).resolve_left,
      rintro rfl,
      cases chain'_iff_pairwise.mp h.1 with _ _ hy,
      cases h'.1 with h' h',
      exacts [(hy _ hi).ne h', not_le_of_gt (hy _ hi) (hx _ h').le] } },
  { intros l hl,
    refine ⟨x :: l, ⟨_, _⟩, by simp⟩,
    { rw chain'_cons', exact ⟨λ y hy, hx _ (hl.2 _ (list.mem_of_mem_head' hy)), hl.1⟩ },
    { rintro x (rfl|hx), exacts [or.inl (set.mem_singleton x), or.inr (hl.2 x hx)] } }
end

lemma chain_height_insert_of_forall_ge (x : α) (hx : ∀ a ∈ s, x > a) :
  (insert x s).chain_height = s.chain_height + 1 :=
begin
  rw [chain_height_order_dual s s rfl, ← chain_height_insert_of_forall_le],
  { apply chain_height_order_dual, refl },
  { exact hx },
end

lemma chain_height_union_le (s t : set α) :
  (s ∪ t).chain_height ≤ s.chain_height + t.chain_height :=
begin
  classical,
  refine supr₂_le _,
  intros l hl,
  let l₁ := l.filter (∈ s), let l₂ := l.filter (∈ t),
  have hl₁ : ↑l₁.length ≤ s.chain_height,
  { apply set.length_le_chain_height_of_mem_subchain,
    exact ⟨hl.1.sublist (list.filter_sublist _), λ i h, (list.of_mem_filter h : _)⟩ },
  have hl₂ : ↑l₂.length ≤ t.chain_height,
  { apply set.length_le_chain_height_of_mem_subchain,
    exact ⟨hl.1.sublist (list.filter_sublist _), λ i h, (list.of_mem_filter h : _)⟩ },
  refine le_trans _ (add_le_add hl₁ hl₂),
  simp_rw [← with_top.coe_add, with_top.coe_le_coe, ← multiset.coe_card,
    ← multiset.card_add, ← multiset.coe_filter],
  rw [multiset.filter_add_filter, multiset.filter_eq_self.mpr, multiset.card_add],
  exacts [le_add_right rfl.le, hl.2]
end

lemma chain_height_union_eq (s t : set α) (H : ∀ (a ∈ s) (b ∈ t), a < b) :
  (s ∪ t).chain_height = s.chain_height + t.chain_height :=
begin
  cases h : t.chain_height,
  { rw [with_top.none_eq_top, add_top, eq_top_iff, ← with_top.none_eq_top, ← h],
    exact set.chain_height_le_of_subset (set.subset_union_right _ _) },
  apply le_antisymm,
  { rw ← h, exact chain_height_union_le s t },
  rw [with_top.some_eq_coe, ← add_zero (s ∪ t).chain_height, ← with_top.coe_zero,
    chain_height_add_le_chain_height_add],
  intros l hl,
  obtain ⟨l', hl', rfl⟩ := exists_chain_of_le_chain_height t h.symm.le,
  refine ⟨l ++ l', ⟨chain'.append hl.1 hl'.1 _, _⟩, by simp⟩,
  { intros x hx y hy, exact H x (hl.2 _ $ mem_of_mem_last' hx) y (hl'.2 _ $ mem_of_mem_head' hy) },
  { intros i hi, rw mem_append at hi, cases hi, exacts [or.inl (hl.2 _ hi), or.inr (hl'.2 _ hi)] }
end

end

end set
