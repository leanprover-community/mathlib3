/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import data.enat.lattice
import order.order_iso_nat
import tactic.tfae

/-!

# Maximal length of chains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas to work with the maximal length of strictly descending finite
sequences (chains) in a partial order.

## Main definition

- `set.subchain`: The set of strictly ascending lists of `α` contained in a `set α`.
- `set.chain_height`: The maximal length of a strictly ascending sequence in a partial order.
This is defined as the maximum of the lengths of `set.subchain`s, valued in `ℕ∞`.

## Main results

- `set.exists_chain_of_le_chain_height`: For each `n : ℕ` such that `n ≤ s.chain_height`, there
  exists `s.subchain` of length `n`.
- `set.chain_height_mono`: If `s ⊆ t` then `s.chain_height ≤ t.chain_height`.
- `set.chain_height_image`: If `f` is an order embedding, then
  `(f '' s).chain_height = s.chain_height`.
- `set.chain_height_insert_of_forall_lt`: If `∀ y ∈ s, y < x`, then
  `(insert x s).chain_height = s.chain_height + 1`.
- `set.chain_height_insert_of_lt_forall`: If `∀ y ∈ s, x < y`, then
  `(insert x s).chain_height = s.chain_height + 1`.
- `set.chain_height_union_eq`: If `∀ x ∈ s, ∀ y ∈ t, s ≤ t`, then
  `(s ∪ t).chain_height = s.chain_height + t.chain_height`.
- `set.well_founded_gt_of_chain_height_ne_top`:
  If `s` has finite height, then `>` is well-founded on `s`.
- `set.well_founded_lt_of_chain_height_ne_top`:
  If `s` has finite height, then `<` is well-founded on `s`.

-/

open list order_dual

universes u v
variables {α β : Type*}

namespace set
section has_lt
variables [has_lt α] [has_lt β] (s t : set α)

/-- The set of strictly ascending lists of `α` contained in a `set α`. -/
def subchain : set (list α) := {l | l.chain' (<) ∧ ∀ i ∈ l, i ∈ s}

lemma nil_mem_subchain : [] ∈ s.subchain := ⟨trivial, λ x hx, hx.elim⟩

variables {s} {l : list α} {a : α}

lemma cons_mem_subchain_iff :
  a :: l ∈ s.subchain ↔ a ∈ s ∧ l ∈ s.subchain ∧ ∀ b ∈ l.head', a < b :=
begin
  refine ⟨λ h, ⟨h.2 _ (or.inl rfl), ⟨(chain'_cons'.mp h.1).2, λ i hi, h.2 _ (or.inr hi)⟩,
      (chain'_cons'.mp h.1).1⟩, _⟩,
  rintro ⟨h₁, h₂, h₃⟩,
  split,
  { rw chain'_cons',
    exact ⟨h₃, h₂.1⟩ },
  { rintro i (rfl|hi),
    exacts [h₁, h₂.2 _ hi] }
end

instance : nonempty s.subchain := ⟨⟨[], s.nil_mem_subchain⟩⟩

variables (s)

/-- The maximal length of a strictly ascending sequence in a partial order. -/
noncomputable def chain_height : ℕ∞ := ⨆ l ∈ s.subchain, length l

lemma chain_height_eq_supr_subtype : s.chain_height = ⨆ l : s.subchain, l.1.length := supr_subtype'

lemma exists_chain_of_le_chain_height {n : ℕ} (hn : ↑n ≤ s.chain_height) :
  ∃ l ∈ s.subchain, length l = n :=
begin
  cases (le_top : s.chain_height ≤ ⊤).eq_or_lt with ha ha; rw chain_height_eq_supr_subtype at ha,
  { obtain ⟨_, ⟨⟨l, h₁, h₂⟩, rfl⟩, h₃⟩ :=
      not_bdd_above_iff'.mp ((with_top.supr_coe_eq_top _).mp ha) n,
    exact ⟨l.take n, ⟨h₁.take _, λ x h, h₂ _ $ take_subset _ _ h⟩,
      (l.length_take n).trans $ min_eq_left $ le_of_not_ge h₃⟩ },
  { rw with_top.supr_coe_lt_top at ha,
    obtain ⟨⟨l, h₁, h₂⟩, e : l.length = _⟩ := nat.Sup_mem (set.range_nonempty _) ha,
    refine ⟨l.take n, ⟨h₁.take _, λ x h, h₂ _ $ take_subset _ _ h⟩,
      (l.length_take n).trans $ min_eq_left $ _⟩,
    rwa [e, ←with_top.coe_le_coe, Sup_range, with_top.coe_supr _ ha,
      ←chain_height_eq_supr_subtype] }
end

lemma le_chain_height_tfae (n : ℕ) :
  tfae [↑n ≤ s.chain_height,
    ∃ l ∈ s.subchain, length l = n,
    ∃ l ∈ s.subchain, n ≤ length l] :=
begin
  tfae_have : 1 → 2, { exact s.exists_chain_of_le_chain_height },
  tfae_have : 2 → 3, { rintro ⟨l, hls, he⟩, exact ⟨l, hls, he.ge⟩ },
  tfae_have : 3 → 1, { rintro ⟨l, hs, hn⟩, exact le_supr₂_of_le l hs (with_top.coe_le_coe.2 hn) },
  tfae_finish,
end

variables {s t}

lemma le_chain_height_iff {n : ℕ} :
  ↑n ≤ s.chain_height ↔ ∃ l ∈ s.subchain, length l = n :=
(le_chain_height_tfae s n).out 0 1

lemma length_le_chain_height_of_mem_subchain (hl : l ∈ s.subchain) : ↑l.length ≤ s.chain_height :=
le_chain_height_iff.mpr ⟨l, hl, rfl⟩

lemma chain_height_eq_top_iff : s.chain_height = ⊤ ↔ ∀ n, ∃ l ∈ s.subchain, length l = n :=
begin
  refine ⟨λ h n, le_chain_height_iff.1 (le_top.trans_eq h.symm), λ h, _⟩,
  contrapose! h, obtain ⟨n, hn⟩ := with_top.ne_top_iff_exists.1 h,
  exact ⟨n + 1, λ l hs, (nat.lt_succ_iff.2 $ with_top.coe_le_coe.1 $
    (length_le_chain_height_of_mem_subchain hs).trans_eq hn.symm).ne⟩,
end

@[simp]
lemma one_le_chain_height_iff : 1 ≤ s.chain_height ↔ s.nonempty :=
begin
  change ((1 : ℕ) : enat) ≤ _ ↔ _,
  rw set.le_chain_height_iff,
  split,
  { rintro ⟨_|⟨x, xs⟩, ⟨h₁, h₂⟩, h₃⟩,
    { cases h₃ },
    { exact ⟨x, h₂ _ (or.inl rfl)⟩ } },
  { rintro ⟨x, hx⟩,
    exact ⟨[x], ⟨chain.nil, λ y h, (list.mem_singleton.mp h).symm ▸ hx⟩, rfl⟩ }
end

@[simp] lemma chain_height_eq_zero_iff : s.chain_height = 0 ↔ s = ∅ :=
by rw [←not_iff_not, ←ne.def, ←bot_eq_zero, ←bot_lt_iff_ne_bot, bot_eq_zero, ←enat.one_le_iff_pos,
  one_le_chain_height_iff, nonempty_iff_ne_empty]

@[simp] lemma chain_height_empty : (∅ : set α).chain_height = 0 := chain_height_eq_zero_iff.2 rfl

@[simp] lemma chain_height_of_is_empty [is_empty α] : s.chain_height = 0 :=
chain_height_eq_zero_iff.mpr (subsingleton.elim _ _)

lemma le_chain_height_add_nat_iff {n m : ℕ} :
  ↑n ≤ s.chain_height + m ↔ ∃ l ∈ s.subchain, n ≤ length l + m :=
by simp_rw [← tsub_le_iff_right, ← with_top.coe_sub, (le_chain_height_tfae s (n - m)).out 0 2]

lemma chain_height_add_le_chain_height_add (s : set α) (t : set β) (n m : ℕ) :
  s.chain_height + n ≤ t.chain_height + m ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l + n ≤ length l' + m :=
begin
  refine ⟨λ e l h, le_chain_height_add_nat_iff.1
    ((add_le_add_right (length_le_chain_height_of_mem_subchain h) _).trans e), λ H, _⟩,
  by_cases s.chain_height = ⊤,
  { suffices : t.chain_height = ⊤, { rw [this, top_add], exact le_top },
    rw chain_height_eq_top_iff at h ⊢,
    intro k, rw (le_chain_height_tfae t k).out 1 2,
    obtain ⟨l, hs, hl⟩ := h (k + m),
    obtain ⟨l', ht, hl'⟩ := H l hs,
    exact ⟨l', ht, (add_le_add_iff_right m).1 $ trans (hl.symm.trans_le le_self_add) hl'⟩ },
  { obtain ⟨k, hk⟩ := with_top.ne_top_iff_exists.1 h,
    obtain ⟨l, hs, hl⟩ := le_chain_height_iff.1 hk.le,
    rw [← hk, ← hl],
    exact le_chain_height_add_nat_iff.2 (H l hs) },
end

lemma chain_height_le_chain_height_tfae (s : set α) (t : set β) :
  tfae [s.chain_height ≤ t.chain_height,
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l',
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l'] :=
begin
  tfae_have : 1 ↔ 3, { convert ← chain_height_add_le_chain_height_add s t 0 0; apply add_zero },
  tfae_have : 2 ↔ 3, { refine forall₂_congr (λ l hl, _),
    simp_rw [← (le_chain_height_tfae t l.length).out 1 2, eq_comm] },
  tfae_finish
end

lemma chain_height_le_chain_height_iff {t : set β} :
  s.chain_height ≤ t.chain_height ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l = length l' :=
(chain_height_le_chain_height_tfae s t).out 0 1

lemma chain_height_le_chain_height_iff_le {t : set β} :
  s.chain_height ≤ t.chain_height ↔
    ∀ l ∈ s.subchain, ∃ l' ∈ t.subchain, length l ≤ length l' :=
(chain_height_le_chain_height_tfae s t).out 0 2

lemma chain_height_mono (h : s ⊆ t) : s.chain_height ≤ t.chain_height :=
chain_height_le_chain_height_iff.2 $ λ l hl, ⟨l, ⟨hl.1, λ i hi, h $ hl.2 i hi⟩, rfl⟩

lemma chain_height_image
  (f : α → β) (hf : ∀ {x y}, x < y ↔ f x < f y) (s : set α) :
  (f '' s).chain_height = s.chain_height :=
begin
  apply le_antisymm; rw chain_height_le_chain_height_iff,
  { suffices : ∀ l ∈ (f '' s).subchain, ∃ l' ∈ s.subchain, map f l' = l,
    { intros l hl, obtain ⟨l', h₁, rfl⟩ := this l hl, exact ⟨l', h₁, length_map _ _⟩ },
    intro l,
    induction l with x xs hx,
    { exact λ _, ⟨nil, ⟨trivial, λ _ h, h.elim⟩, rfl⟩ },
    { intros h,
      rw cons_mem_subchain_iff at h,
      obtain ⟨⟨x, hx', rfl⟩, h₁, h₂⟩ := h,
      obtain ⟨l', h₃, rfl⟩ := hx h₁,
      refine ⟨x :: l', set.cons_mem_subchain_iff.mpr ⟨hx', h₃, _⟩, rfl⟩,
      cases l', { simp }, { simpa [← hf] using h₂ } } },
  { intros l hl,
    refine ⟨l.map f, ⟨_, _⟩, _⟩,
    { simp_rw [chain'_map, ← hf], exact hl.1 },
    { intros _ e, obtain ⟨a, ha, rfl⟩ := mem_map.mp e, exact set.mem_image_of_mem _ (hl.2 _ ha) },
    { rw length_map } },
end

variables (s)

@[simp] lemma chain_height_dual : (of_dual ⁻¹' s).chain_height = s.chain_height :=
begin
  apply le_antisymm;
  { rw chain_height_le_chain_height_iff,
    rintro l ⟨h₁, h₂⟩,
    exact ⟨l.reverse, ⟨chain'_reverse.mpr h₁,
      λ i h, h₂ i (mem_reverse.mp h)⟩, (length_reverse _).symm⟩ }
end

end has_lt

section preorder
variables (s t : set α) [preorder α]

lemma chain_height_eq_supr_Ici : s.chain_height = ⨆ i ∈ s, (s ∩ set.Ici i).chain_height :=
begin
  apply le_antisymm,
  { refine supr₂_le _,
    rintro (_ | ⟨x, xs⟩) h,
    { exact zero_le _ },
    { apply le_trans _ (le_supr₂ x (cons_mem_subchain_iff.mp h).1),
      apply length_le_chain_height_of_mem_subchain,
      refine ⟨h.1, λ i hi, ⟨h.2 i hi, _⟩⟩,
      cases hi, { exact hi.symm.le },
      cases chain'_iff_pairwise.mp h.1 with _ _ h',
      exact (h' _ hi).le } },
  { exact supr₂_le (λ i hi, chain_height_mono $ set.inter_subset_left _ _) }
end

lemma chain_height_eq_supr_Iic : s.chain_height = ⨆ i ∈ s, (s ∩ set.Iic i).chain_height :=
by { simp_rw ←chain_height_dual (_ ∩ _), rw [←chain_height_dual, chain_height_eq_supr_Ici], refl }

variables {s t}

lemma chain_height_insert_of_forall_gt (a : α) (hx : ∀ b ∈ s, a < b) :
  (insert a s).chain_height = s.chain_height + 1 :=
begin
  rw ← add_zero (insert a s).chain_height,
  change (insert a s).chain_height + (0 : ℕ) = s.chain_height + (1 : ℕ),
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
    refine ⟨a :: l, ⟨_, _⟩, by simp⟩,
    { rw chain'_cons', exact ⟨λ y hy, hx _ (hl.2 _ (mem_of_mem_head' hy)), hl.1⟩ },
    { rintro x (rfl|hx), exacts [or.inl (set.mem_singleton x), or.inr (hl.2 x hx)] } }
end

lemma chain_height_insert_of_forall_lt (a : α) (ha : ∀ b ∈ s, b < a) :
  (insert a s).chain_height = s.chain_height + 1 :=
by { rw [←chain_height_dual, ←chain_height_dual s], exact chain_height_insert_of_forall_gt _ ha }

lemma chain_height_union_le : (s ∪ t).chain_height ≤ s.chain_height + t.chain_height :=
begin
  classical,
  refine supr₂_le (λ l hl, _),
  let l₁ := l.filter (∈ s), let l₂ := l.filter (∈ t),
  have hl₁ : ↑l₁.length ≤ s.chain_height,
  { apply set.length_le_chain_height_of_mem_subchain,
    exact ⟨hl.1.sublist (filter_sublist _), λ i h, (of_mem_filter h : _)⟩ },
  have hl₂ : ↑l₂.length ≤ t.chain_height,
  { apply set.length_le_chain_height_of_mem_subchain,
    exact ⟨hl.1.sublist (filter_sublist _), λ i h, (of_mem_filter h : _)⟩ },
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
    exact set.chain_height_mono (set.subset_union_right _ _) },
  apply le_antisymm,
  { rw ← h,
    exact chain_height_union_le },
  rw [with_top.some_eq_coe, ← add_zero (s ∪ t).chain_height, ← with_top.coe_zero,
    chain_height_add_le_chain_height_add],
  intros l hl,
  obtain ⟨l', hl', rfl⟩ := exists_chain_of_le_chain_height t h.symm.le,
  refine ⟨l ++ l', ⟨chain'.append hl.1 hl'.1 $ λ x hx y hy, _, λ i hi, _⟩, by simp⟩,
  { exact H x (hl.2 _ $ mem_of_mem_last' hx) y (hl'.2 _ $ mem_of_mem_head' hy) },
  { rw mem_append at hi, cases hi, exacts [or.inl (hl.2 _ hi), or.inr (hl'.2 _ hi)] }
end

lemma well_founded_gt_of_chain_height_ne_top (s : set α) (hs : s.chain_height ≠ ⊤) :
  well_founded_gt s :=
begin
  obtain ⟨n, hn⟩ := with_top.ne_top_iff_exists.1 hs,
  refine ⟨rel_embedding.well_founded_iff_no_descending_seq.2 ⟨λ f, _⟩⟩,
  refine n.lt_succ_self.not_le (with_top.coe_le_coe.1 $ hn.symm ▸ _),
  refine le_supr₂_of_le _ ⟨chain'_map_of_chain' coe (λ _ _, id)
    (chain'_iff_pairwise.2 $ pairwise_of_fn.2 $ λ i j, f.map_rel_iff.2), λ i h, _⟩ _,
  { exact n.succ },
  { obtain ⟨a, ha, rfl⟩ := mem_map.1 h, exact a.prop },
  { rw [length_map, length_of_fn], exact le_rfl },
end

lemma well_founded_lt_of_chain_height_ne_top (s : set α) (hs : s.chain_height ≠ ⊤) :
  well_founded_lt s :=
well_founded_gt_of_chain_height_ne_top (of_dual ⁻¹' s) $ by rwa chain_height_dual

end preorder

end set
