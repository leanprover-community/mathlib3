/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash
-/
import data.finset.card

/-!
# Finsets in product types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`finset.prod` operation which computes the multiplicative product.

## Main declarations

* `finset.product`: Turns `s : finset α`, `t : finset β` into their product in `finset (α × β)`.
* `finset.diag`: For `s : finset α`, `s.diag` is the `finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `finset.off_diag`: For `s : finset α`, `s.off_diag` is the `finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/

open multiset

variables {α β γ : Type*}

namespace finset

/-! ### prod -/
section prod
variables {s s' : finset α} {t t' : finset β} {a : α} {b : β}

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : finset α) (t : finset β) : finset (α × β) := ⟨_, s.nodup.product t.nodup⟩

/- This notation binds more strongly than (pre)images, unions and intersections. -/
infixr (name := finset.product) ` ×ˢ `:82 := finset.product

@[simp] lemma product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 := rfl

@[simp] lemma mem_product {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := mem_product

lemma mk_mem_product (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := mem_product.2 ⟨ha, hb⟩

@[simp, norm_cast] lemma coe_product (s : finset α) (t : finset β) :
  (↑(s ×ˢ t) : set (α × β)) = s ×ˢ t :=
set.ext $ λ x, finset.mem_product

lemma subset_product_image_fst [decidable_eq α] : (s ×ˢ t).image prod.fst ⊆ s :=
λ i, by simp [mem_image] {contextual := tt}

lemma subset_product_image_snd [decidable_eq β] : (s ×ˢ t).image prod.snd ⊆ t :=
λ i, by simp [mem_image] {contextual := tt}

lemma product_image_fst [decidable_eq α] (ht : t.nonempty) : (s ×ˢ t).image prod.fst = s :=
by { ext i, simp [mem_image, ht.bex] }

lemma product_image_snd [decidable_eq β] (ht : s.nonempty) : (s ×ˢ t).image prod.snd = t :=
by { ext i, simp [mem_image, ht.bex] }

lemma subset_product [decidable_eq α] [decidable_eq β] {s : finset (α × β)} :
  s ⊆ s.image prod.fst ×ˢ s.image prod.snd :=
λ p hp, mem_product.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

lemma product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s ×ˢ t ⊆ s' ×ˢ t' :=
λ ⟨x,y⟩ h, mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩

lemma product_subset_product_left (hs : s ⊆ s') : s ×ˢ t ⊆ s' ×ˢ t :=
product_subset_product hs (subset.refl _)

lemma product_subset_product_right (ht : t ⊆ t') : s ×ˢ t ⊆ s ×ˢ t' :=
product_subset_product (subset.refl _) ht

lemma map_swap_product (s : finset α) (t : finset β) :
  (t ×ˢ s).map ⟨prod.swap, prod.swap_injective⟩ = s ×ˢ t :=
coe_injective $ by { push_cast, exact set.image_swap_prod _ _ }

@[simp] lemma image_swap_product [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
  (t ×ˢ s).image prod.swap = s ×ˢ t :=
coe_injective $ by { push_cast, exact set.image_swap_prod _ _ }

lemma product_eq_bUnion [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
  s ×ˢ t = s.bUnion (λa, t.image $ λb, (a, b)) :=
ext $ λ ⟨x, y⟩, by simp only [mem_product, mem_bUnion, mem_image, exists_prop, prod.mk.inj_iff,
  and.left_comm, exists_and_distrib_left, exists_eq_right, exists_eq_left]

lemma product_eq_bUnion_right [decidable_eq α] [decidable_eq β] (s : finset α) (t : finset β) :
  s ×ˢ t = t.bUnion (λ b, s.image $ λ a, (a, b)) :=
ext $ λ ⟨x, y⟩, by simp only [mem_product, mem_bUnion, mem_image, exists_prop, prod.mk.inj_iff,
  and.left_comm, exists_and_distrib_left, exists_eq_right, exists_eq_left]

/-- See also `finset.sup_product_left`. -/
@[simp] lemma product_bUnion [decidable_eq γ] (s : finset α) (t : finset β) (f : α × β → finset γ) :
  (s ×ˢ t).bUnion f = s.bUnion (λ a, t.bUnion (λ b, f (a, b))) :=
by { classical, simp_rw [product_eq_bUnion, bUnion_bUnion, image_bUnion] }

@[simp] lemma card_product (s : finset α) (t : finset β) : card (s ×ˢ t) = card s * card t :=
multiset.card_product _ _

lemma filter_product (p : α → Prop) (q : β → Prop) [decidable_pred p] [decidable_pred q] :
  (s ×ˢ t).filter (λ (x : α × β), p x.1 ∧ q x.2) = s.filter p ×ˢ t.filter q :=
by { ext ⟨a, b⟩, simp only [mem_filter, mem_product],
     exact and_and_and_comm (a ∈ s) (b ∈ t) (p a) (q b) }

lemma filter_product_left (p : α → Prop) [decidable_pred p] :
  (s ×ˢ t).filter (λ (x : α × β), p x.1) = s.filter p ×ˢ t :=
by simpa using filter_product p (λ _, true)

lemma filter_product_right (q : β → Prop) [decidable_pred q] :
  (s ×ˢ t).filter (λ (x : α × β), q x.2) = s ×ˢ t.filter q :=
by simpa using filter_product (λ _ : α, true) q

lemma filter_product_card (s : finset α) (t : finset β)
  (p : α → Prop) (q : β → Prop) [decidable_pred p] [decidable_pred q] :
  ((s ×ˢ t).filter (λ (x : α × β), p x.1 ↔ q x.2)).card =
  (s.filter p).card * (t.filter q).card + (s.filter (not ∘ p)).card * (t.filter (not ∘ q)).card :=
begin
  classical,
  rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_eq],
  { apply congr_arg, ext ⟨a, b⟩, simp only [filter_union_right, mem_filter, mem_product],
    split; intros h; use h.1,
    simp only [function.comp_app, and_self, h.2, em (q b)],
    cases h.2; { try { simp at h_1 }, simp [h_1] } },
  { apply finset.disjoint_filter_filter',
    exact (disjoint_compl_right.inf_left _).inf_right _ }
end

lemma empty_product (t : finset β) : (∅ : finset α) ×ˢ t = ∅ := rfl

lemma product_empty (s : finset α) : s ×ˢ (∅ : finset β) = ∅ :=
eq_empty_of_forall_not_mem (λ x h, (finset.mem_product.1 h).2)

lemma nonempty.product (hs : s.nonempty) (ht : t.nonempty) : (s ×ˢ t).nonempty :=
let ⟨x, hx⟩ := hs, ⟨y, hy⟩ := ht in ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩

lemma nonempty.fst (h : (s ×ˢ t).nonempty) : s.nonempty :=
let ⟨xy, hxy⟩ := h in ⟨xy.1, (mem_product.1 hxy).1⟩

lemma nonempty.snd (h : (s ×ˢ t).nonempty) : t.nonempty :=
let ⟨xy, hxy⟩ := h in ⟨xy.2, (mem_product.1 hxy).2⟩

@[simp] lemma nonempty_product : (s ×ˢ t).nonempty ↔ s.nonempty ∧ t.nonempty :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, h.1.product h.2⟩

@[simp] lemma product_eq_empty {s : finset α} {t : finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
by rw [←not_nonempty_iff_eq_empty, nonempty_product, not_and_distrib, not_nonempty_iff_eq_empty,
  not_nonempty_iff_eq_empty]

@[simp] lemma singleton_product {a : α} :
  ({a} : finset α) ×ˢ t = t.map ⟨prod.mk a, prod.mk.inj_left _⟩ :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

@[simp] lemma product_singleton {b : β} :
  s ×ˢ {b} = s.map ⟨λ i, (i, b), prod.mk.inj_right _⟩ :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

lemma singleton_product_singleton {a : α} {b : β} :
  ({a} : finset α) ×ˢ ({b} : finset β) = {(a, b)} :=
by simp only [product_singleton, function.embedding.coe_fn_mk, map_singleton]

@[simp] lemma union_product [decidable_eq α] [decidable_eq β] :
  (s ∪ s') ×ˢ t = s ×ˢ t ∪ s' ×ˢ t :=
by { ext ⟨x, y⟩, simp only [or_and_distrib_right, mem_union, mem_product] }

@[simp] lemma product_union [decidable_eq α] [decidable_eq β] :
  s ×ˢ (t ∪ t') = s ×ˢ t ∪ s ×ˢ t' :=
by { ext ⟨x, y⟩, simp only [and_or_distrib_left, mem_union, mem_product] }

lemma inter_product [decidable_eq α] [decidable_eq β] :
  (s ∩ s') ×ˢ t = s ×ˢ t ∩ s' ×ˢ t :=
by { ext ⟨x, y⟩, simp only [←and_and_distrib_right, mem_inter, mem_product] }

lemma product_inter [decidable_eq α] [decidable_eq β] :
  s ×ˢ (t ∩ t') = s ×ˢ t ∩ s ×ˢ t' :=
by { ext ⟨x, y⟩, simp only [←and_and_distrib_left, mem_inter, mem_product] }

lemma product_inter_product [decidable_eq α] [decidable_eq β] :
  s ×ˢ t ∩ s' ×ˢ t' = (s ∩ s') ×ˢ (t ∩ t') :=
by { ext ⟨x, y⟩, simp only [and_assoc, and.left_comm, mem_inter, mem_product] }

lemma disjoint_product : disjoint (s ×ˢ t) (s' ×ˢ t') ↔ disjoint s s' ∨ disjoint t t' :=
by simp_rw [←disjoint_coe, coe_product, set.disjoint_prod]

@[simp] lemma disj_union_product (hs : disjoint s s') :
  s.disj_union s' hs ×ˢ t = (s ×ˢ t).disj_union (s' ×ˢ t)
    (disjoint_product.mpr $ or.inl hs) :=
eq_of_veq $ multiset.add_product _ _ _

@[simp] lemma product_disj_union (ht : disjoint t t') :
  s ×ˢ t.disj_union t' ht = (s ×ˢ t).disj_union (s ×ˢ t')
    (disjoint_product.mpr $ or.inr ht) :=
eq_of_veq $ multiset.product_add _ _ _

end prod

section diag
variables [decidable_eq α] (s t : finset α)

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag := (s ×ˢ s).filter (λ a : α × α, a.fst = a.snd)

/-- Given a finite set `s`, the off-diagonal, `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def off_diag := (s ×ˢ s).filter (λ (a : α × α), a.fst ≠ a.snd)

variables {s} {x : α × α}

@[simp] lemma mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 :=
by { simp only [diag, mem_filter, mem_product], split; intros h;
     simp only [h, and_true, eq_self_iff_true, and_self], rw ←h.2, exact h.1 }

@[simp] lemma mem_off_diag : x ∈ s.off_diag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
by { simp only [off_diag, mem_filter, mem_product], split; intros h;
     simp only [h, ne.def, not_false_iff, and_self] }

variables (s)

@[simp, norm_cast] lemma coe_off_diag : (s.off_diag : set (α × α)) = (s : set α).off_diag :=
set.ext $ λ _, mem_off_diag

@[simp] lemma diag_card : (diag s).card = s.card :=
begin
  suffices : diag s = s.image (λ a, (a, a)),
  { rw this, apply card_image_of_inj_on, exact λ x1 h1 x2 h2 h3, (prod.mk.inj h3).1 },
  ext ⟨a₁, a₂⟩, rw mem_diag, split; intros h; rw finset.mem_image at *,
  { use [a₁, h.1, prod.mk.inj_iff.mpr ⟨rfl, h.2⟩] },
  { rcases h with ⟨a, h1, h2⟩, have h := prod.mk.inj h2, rw [←h.1, ←h.2], use h1 },
end

@[simp] lemma off_diag_card : (off_diag s).card = s.card * s.card - s.card :=
begin
  suffices : (diag s).card + (off_diag s).card = s.card * s.card,
  { nth_rewrite 2 ← s.diag_card, simp only [diag_card] at *, rw tsub_eq_of_eq_add_rev, rw this },
  rw ← card_product,
  apply filter_card_add_filter_neg_card_eq_card,
end

@[mono] lemma diag_mono : monotone (diag : finset α → finset (α × α)) :=
λ s t h x hx, mem_diag.2 $ and.imp_left (@h _) $ mem_diag.1 hx

@[mono] lemma off_diag_mono : monotone (off_diag : finset α → finset (α × α)) :=
λ s t h x hx, mem_off_diag.2 $ and.imp (@h _) (and.imp_left $ @h _) $ mem_off_diag.1 hx

@[simp] lemma diag_empty : (∅ : finset α).diag = ∅ := rfl

@[simp] lemma off_diag_empty : (∅ : finset α).off_diag = ∅ := rfl

@[simp] lemma diag_union_off_diag : s.diag ∪ s.off_diag = s ×ˢ s :=
filter_union_filter_neg_eq _ _

@[simp] lemma disjoint_diag_off_diag : disjoint s.diag s.off_diag :=
disjoint_filter_filter_neg _ _ _

lemma product_sdiff_diag : s ×ˢ s \ s.diag = s.off_diag :=
by rw [←diag_union_off_diag, union_comm, union_sdiff_self,
    sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _).symm]

lemma product_sdiff_off_diag : s ×ˢ s \ s.off_diag = s.diag :=
by rw [←diag_union_off_diag, union_sdiff_self, sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _)]

lemma diag_inter : (s ∩ t).diag = s.diag ∩ t.diag :=
ext $ λ x, by simpa only [mem_diag, mem_inter] using and_and_distrib_right _ _ _

lemma off_diag_inter : (s ∩ t).off_diag = s.off_diag ∩ t.off_diag :=
coe_injective $ by { push_cast, exact set.off_diag_inter _ _ }

lemma diag_union : (s ∪ t).diag = s.diag ∪ t.diag :=
by { ext ⟨i, j⟩, simp only [mem_diag, mem_union, or_and_distrib_right] }

variables {s t}

lemma off_diag_union (h : disjoint s t) :
  (s ∪ t).off_diag = s.off_diag ∪ t.off_diag ∪ s ×ˢ t ∪ t ×ˢ s :=
coe_injective $ by { push_cast, exact set.off_diag_union (disjoint_coe.2 h) }

variables (a : α)

@[simp] lemma off_diag_singleton : ({a} : finset α).off_diag = ∅ :=
by simp [←finset.card_eq_zero]

lemma diag_singleton : ({a} : finset α).diag = {(a, a)} :=
by rw [←product_sdiff_off_diag, off_diag_singleton, sdiff_empty, singleton_product_singleton]

lemma diag_insert : (insert a s).diag = insert (a, a) s.diag :=
by rw [insert_eq, insert_eq, diag_union, diag_singleton]

lemma off_diag_insert (has : a ∉ s) :
  (insert a s).off_diag = s.off_diag ∪ {a} ×ˢ s ∪ s ×ˢ {a} :=
by rw [insert_eq, union_comm, off_diag_union (disjoint_singleton_right.2 has), off_diag_singleton,
  union_empty, union_right_comm]

end diag
end finset
