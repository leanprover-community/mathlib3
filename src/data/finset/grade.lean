/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.card
import data.set.finite
import order.atoms
import order.grade

/-!
# Finsets and multisets form a graded order

This file characterises atoms, coatoms and the covering relation in finsets and multisets. It also
proves that they form a `ℕ`-graded order.
-/

open order

variables {α : Type*}

namespace multiset
variables {s t : multiset α} {a : α}

@[simp] lemma covby_cons (s : multiset α) (a : α) : s ⋖ a ::ₘ s :=
⟨lt_cons_self _ _, λ t hst hts, (covby_succ _).2 (card_lt_of_lt hst) $
  by simpa using card_lt_of_lt hts⟩

lemma _root_.covby.exists_multiset_cons (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma covby_iff : s ⋖ t ↔ ∃ a, t = a ::ₘ s :=
⟨covby.exists_multiset_cons, by { rintro ⟨a, rfl⟩, exact covby_cons _ _ }⟩

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
by { obtain ⟨a, rfl⟩ := h.exists_multiset_cons, rw card_cons, exact covby_succ _ }

lemma is_atom_iff : is_atom s ↔ ∃ a, s = {a} := bot_covby_iff.symm.trans covby_iff

@[simp] lemma is_atom_singleton (a : α) : is_atom ({a} : multiset α) := is_atom_iff.2 ⟨_, rfl⟩

instance : grade_min_order ℕ (multiset α) :=
{ grade := card,
  grade_strict_mono := card_strict_mono,
  covby_grade := λ s t, covby.card_multiset,
  is_min_grade := λ s hs, by { rw is_min_iff_eq_bot.1 hs, exact is_min_bot } }

@[simp] protected lemma grade (m : multiset α) : grade ℕ m = m.card := rfl

end multiset

namespace finset
variables {s t : finset α} {a : α}

/-- Finsets form an order-connected suborder of multisets. -/
lemma ord_connected_range_val : set.ord_connected (set.range val : set $ multiset α) :=
⟨by { rintro _ _ _ ⟨s, rfl⟩ t ht, exact ⟨⟨t, multiset.nodup_of_le ht.2 s.2⟩, rfl⟩ }⟩

/-- Finsets form an order-connected suborder of sets. -/
lemma ord_connected_range_coe : set.ord_connected (set.range (coe : finset α → set α)) :=
⟨by { rintro _ _ _ ⟨s, rfl⟩ t ht, exact ⟨_, (s.finite_to_set.subset ht.2).coe_to_finset⟩ }⟩

@[simp] lemma val_wcovby_val : s.1 ⩿ t.1 ↔ s ⩿ t :=
ord_connected_range_val.apply_wcovby_apply_iff ⟨⟨val, val_injective⟩, λ _ _ : finset α, val_le_iff⟩

@[simp] lemma val_covby_val : s.1 ⋖ t.1 ↔ s ⋖ t :=
ord_connected_range_val.apply_covby_apply_iff ⟨⟨val, val_injective⟩, λ _ _ : finset α, val_le_iff⟩

@[simp] lemma coe_wcovby_coe : (s : set α) ⩿ t ↔ s ⩿ t :=
ord_connected_range_coe.apply_wcovby_apply_iff ⟨⟨coe, coe_injective⟩, λ _ _ : finset α, coe_subset⟩

@[simp] lemma coe_covby_coe : (s : set α) ⋖ t ↔ s ⋖ t :=
ord_connected_range_coe.apply_covby_apply_iff ⟨⟨coe, coe_injective⟩, λ _ _ : finset α, coe_subset⟩

alias val_wcovby_val ↔ _ _root_.wcovby.finset_val
alias val_covby_val ↔ _ _root_.covby.finset_val
alias coe_wcovby_coe ↔ _ _root_.wcovby.finset_coe
alias coe_covby_coe ↔ _ _root_.covby.finset_coe

@[simp] lemma covby_cons (ha : a ∉ s) : s ⋖ s.cons a ha := by simp [←val_covby_val]

lemma _root_.covby.exists_finset_cons (h : s ⋖ t) : ∃ a ∉ s, t = s.cons a ‹_› :=
(ssubset_iff_exists_cons_subset.1 h.lt).imp₂ $ λ a ha (hst : cons a s ha ⊆ t),
  hst.eq_of_not_ssuperset $ h.2 $ ssubset_cons _

lemma covby_iff_cons : s ⋖ t ↔ ∃ a ∉ s, t = s.cons a ‹_› :=
⟨covby.exists_finset_cons, by { rintro ⟨a, ha, rfl⟩, exact covby_cons _ }⟩

lemma _root_.covby.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covby_val.2 h).card_multiset

section decidable_eq
variables [decidable_eq α]

@[simp] lemma wcovby_insert (s : finset α) (a : α) : s ⩿ insert a s := by simp [←coe_wcovby_coe]
@[simp] lemma erase_wcovby (s : finset α) (a : α) : s.erase a ⩿ s := by simp [←coe_wcovby_coe]

lemma covby_insert (ha : a ∉ s) : s ⋖ insert a s :=
(wcovby_insert _ _).covby_of_lt $ ssubset_insert ha

@[simp] lemma erase_covby (ha : a ∈ s) : s.erase a ⋖ s := ⟨erase_ssubset ha, (erase_wcovby _ _).2⟩

lemma _root_.covby.exists_finset_insert (h : s ⋖ t) : ∃ a ∉ s, t = insert a s :=
by simpa using h.exists_finset_cons

lemma _root_.covby.exists_finset_erase (h : s ⋖ t) : ∃ a ∈ t, s = t.erase a :=
by simpa only [←coe_inj, coe_erase] using h.finset_coe.exists_set_sdiff_singleton

lemma covby_iff_insert : s ⋖ t ↔ ∃ a ∉ s, t = insert a s :=
by simp only [←coe_covby_coe, set.covby_iff_insert, ←coe_inj, coe_insert, mem_coe]

lemma covby_iff_erase : s ⋖ t ↔ ∃ a ∈ t, s = t.erase a :=
by simp only [←coe_covby_coe, set.covby_iff_sdiff_singleton, ←coe_inj, coe_erase, mem_coe]

end decidable_eq

@[simp] lemma is_atom_singleton (a : α) : is_atom ({a} : finset α) :=
⟨singleton_ne_empty a, λ s, eq_empty_of_ssubset_singleton⟩

protected lemma is_atom_iff : is_atom s ↔ ∃ a, s = {a} :=
bot_covby_iff.symm.trans $ covby_iff_cons.trans $ by simp

section fintype
variables [fintype α] [decidable_eq α]

@[simp] lemma is_coatom_compl_singleton (a : α) : is_coatom ({a}ᶜ : finset α) :=
(is_atom_singleton a).compl

protected lemma is_coatom_iff : is_coatom s ↔ ∃ a, s = {a}ᶜ :=
by simp_rw [←is_atom_compl, finset.is_atom_iff, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

end fintype

instance grade_min_order_multiset : grade_min_order (multiset α) (finset α) :=
{ grade := val,
  grade_strict_mono := val_strict_mono,
  covby_grade := λ _ _, covby.finset_val,
  is_min_grade := λ s hs, by { rw is_min_iff_eq_bot.1 hs, exact is_min_bot } }

@[simp] lemma grade_multiset (s : finset α) : grade (multiset α) s = s.1 := rfl

instance grade_min_order_nat : grade_min_order ℕ (finset α) :=
{ grade := card,
  grade_strict_mono := card_strict_mono,
  covby_grade := λ _ _, covby.card_finset,
  is_min_grade := λ s hs, by { rw is_min_iff_eq_bot.1 hs, exact is_min_bot } }

@[simp] protected lemma grade (s : finset α) : grade ℕ s = s.card := rfl

end finset
