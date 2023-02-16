/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.fintype.prod
import data.fintype.vector
import data.sym.sym2

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `finset (sym α n)` and `finset (sym2 α)`.

## Main declarations

* `finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.

## TODO

`finset.sym` forms a Galois connection between `finset α` and `finset (sym α n)`. Similar for
`finset.sym2`.
-/

namespace finset
variables {α : Type*} [decidable_eq α] {s t : finset α} {a b : α}

lemma is_diag_mk_of_mem_diag {a : α × α} (h : a ∈ s.diag) : sym2.is_diag ⟦a⟧ :=
(sym2.is_diag_iff_proj_eq _).2 (mem_diag.1 h).2

lemma not_is_diag_mk_of_mem_off_diag {a : α × α} (h : a ∈ s.off_diag) : ¬ sym2.is_diag ⟦a⟧ :=
by { rw sym2.is_diag_iff_proj_eq, exact (mem_off_diag.1 h).2.2 }

section sym2
variables {m : sym2 α}

/-- Lifts a finset to `sym2 α`. `s.sym2` is the finset of all pairs with elements in `s`. -/
protected def sym2 (s : finset α) : finset (sym2 α) := (s ×ˢ s).image quotient.mk

@[simp] lemma mem_sym2_iff : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s :=
begin
  refine mem_image.trans
    ⟨_, λ h, ⟨m.out, mem_product.2 ⟨h _ m.out_fst_mem, h _ m.out_snd_mem⟩, m.out_eq⟩⟩,
  rintro ⟨⟨a, b⟩, h, rfl⟩,
  rw sym2.ball,
  rwa mem_product at h,
end

lemma mk_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by rw [mem_sym2_iff, sym2.ball]

@[simp] lemma sym2_empty : (∅ : finset α).sym2 = ∅ := rfl

@[simp] lemma sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ :=
by rw [finset.sym2, image_eq_empty, product_eq_empty, or_self]

@[simp] lemma sym2_nonempty : s.sym2.nonempty ↔ s.nonempty :=
by rw [finset.sym2, nonempty.image_iff, nonempty_product, and_self]

alias sym2_nonempty ↔ _ nonempty.sym2

attribute [protected] nonempty.sym2

@[simp] lemma sym2_univ [fintype α] : (univ : finset α).sym2 = univ := rfl

@[simp] lemma sym2_singleton (a : α) : ({a} : finset α).sym2 = {sym2.diag a} :=
by rw [finset.sym2, singleton_product_singleton, image_singleton, sym2.diag]

@[simp] lemma diag_mem_sym2_iff : sym2.diag a ∈ s.sym2 ↔ a ∈ s := mk_mem_sym2_iff.trans $ and_self _

@[simp] lemma sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 :=
λ m he, mem_sym2_iff.2 $ λ a ha, h $ mem_sym2_iff.1 he _ ha

lemma image_diag_union_image_off_diag :
  s.diag.image quotient.mk ∪ s.off_diag.image quotient.mk = s.sym2 :=
by { rw [←image_union, diag_union_off_diag], refl }

end sym2

section sym
variables {n : ℕ} {m : sym α n}

/-- Lifts a finset to `sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : finset α) : Π n, finset (sym α n)
| 0       := {∅}
| (n + 1) := s.sup $ λ a, (sym n).image $ _root_.sym.cons a

@[simp] lemma sym_zero : s.sym 0 = {∅} := rfl
@[simp] lemma sym_succ : s.sym (n + 1) = s.sup (λ a, (s.sym n).image $ sym.cons a) := rfl

@[simp] lemma mem_sym_iff : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s :=
begin
  induction n with n ih,
  { refine mem_singleton.trans ⟨_, λ _, sym.eq_nil_of_card_zero _⟩,
    rintro rfl,
    exact λ a ha, ha.elim },
  refine mem_sup.trans ⟨_, λ h, _⟩,
  { rintro ⟨a, ha, he⟩ b hb,
    rw mem_image at he,
    obtain ⟨m, he, rfl⟩ := he,
    rw sym.mem_cons at hb,
    obtain rfl | hb := hb,
    { exact ha },
    { exact ih.1 he _ hb } },
  { obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ,
    exact ⟨a, h _ $ sym.mem_cons_self _ _,
      mem_image_of_mem _ $ ih.2 $ λ b hb, h _ $ sym.mem_cons_of_mem hb⟩ }
end

@[simp] lemma sym_empty (n : ℕ) : (∅ : finset α).sym (n + 1) = ∅ := rfl

lemma replicate_mem_sym (ha : a ∈ s) (n : ℕ) : sym.replicate n a ∈ s.sym n :=
mem_sym_iff.2 $ λ b hb, by rwa (sym.mem_replicate.1 hb).2

protected lemma nonempty.sym (h : s.nonempty) (n : ℕ) : (s.sym n).nonempty :=
let ⟨a, ha⟩ := h in ⟨_, replicate_mem_sym ha n⟩

@[simp] lemma sym_singleton (a : α) (n : ℕ) : ({a} : finset α).sym n = {sym.replicate n a} :=
eq_singleton_iff_unique_mem.2 ⟨replicate_mem_sym (mem_singleton.2 rfl) _,
  λ s hs, sym.eq_replicate_iff.2 $ λ b hb, eq_of_mem_singleton $ mem_sym_iff.1 hs _ hb⟩

lemma eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ :=
begin
  rw ←not_nonempty_iff_eq_empty at ⊢ h,
  exact λ hs, h (hs.sym _),
end

@[simp] lemma sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ :=
begin
  cases n,
  { exact iff_of_false (singleton_ne_empty _) (λ h, (h.1 rfl).elim) },
  { refine ⟨λ h, ⟨n.succ_ne_zero, eq_empty_of_sym_eq_empty h⟩, _⟩,
    rintro ⟨_, rfl⟩,
    exact sym_empty _ }
end

@[simp] lemma sym_nonempty : (s.sym n).nonempty ↔ n = 0 ∨ s.nonempty :=
by simp_rw [nonempty_iff_ne_empty, ne.def, sym_eq_empty, not_and_distrib, not_ne_iff]

alias sym_nonempty ↔ _ nonempty.sym

attribute [protected] nonempty.sym

@[simp] lemma sym_univ [fintype α] (n : ℕ) : (univ : finset α).sym n = univ :=
eq_univ_iff_forall.2 $ λ s, mem_sym_iff.2 $ λ a _, mem_univ _

@[simp] lemma sym_mono (h : s ⊆ t) (n : ℕ): s.sym n ⊆ t.sym n :=
λ m hm, mem_sym_iff.2 $ λ a ha, h $ mem_sym_iff.1 hm _ ha

@[simp] lemma sym_inter (s t : finset α) (n : ℕ) : (s ∩ t).sym n = s.sym n ∩ t.sym n :=
by { ext m, simp only [mem_inter, mem_sym_iff, imp_and_distrib, forall_and_distrib] }

@[simp] lemma sym_union (s t : finset α) (n : ℕ) : s.sym n ∪ t.sym n ⊆ (s ∪ t).sym n :=
union_subset (sym_mono (subset_union_left s t) n) (sym_mono (subset_union_right s t) n)

lemma sym_fill_mem (a : α) {i : fin (n + 1)} {m : sym α (n - i)} (h : m ∈ s.sym (n - i)) :
  m.fill a i ∈ (insert a s).sym n :=
mem_sym_iff.2 $ λ b hb, mem_insert.2 $ (sym.mem_fill_iff.1 hb).imp and.right $ mem_sym_iff.1 h b

lemma sym_filter_ne_mem (a : α) (h : m ∈ s.sym n) :
  (m.filter_ne a).2 ∈ (s.erase a).sym (n - (m.filter_ne a).1) :=
mem_sym_iff.2 $ λ b H, mem_erase.2 $ (multiset.mem_filter.1 H).symm.imp ne.symm $ mem_sym_iff.1 h b

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps] def sym_insert_equiv (h : a ∉ s) : (insert a s).sym n ≃ Σ i : fin (n + 1), s.sym (n - i) :=
{ to_fun := λ m, ⟨_, (m.1.filter_ne a).2, by convert sym_filter_ne_mem a m.2; rw erase_insert h⟩,
  inv_fun := λ m, ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩,
  left_inv := λ m, subtype.ext $ m.1.fill_filter_ne a,
  right_inv := λ ⟨i, m, hm⟩, begin
    refine (_ : id.injective).sigma_map (λ i, _) _,
    { exact λ i, sym α (n - i) },
    swap, { exact λ _ _, id },
    swap, { exact subtype.coe_injective },
    refine eq.trans _ (sym.filter_ne_fill a _ _),
    exacts [rfl, h ∘ mem_sym_iff.1 hm a],
  end }

end sym
end finset
