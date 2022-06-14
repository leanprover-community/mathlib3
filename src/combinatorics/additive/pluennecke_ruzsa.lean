/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import combinatorics.double_counting
import data.finset.pointwise

/-!
# The Plünnecke-Ruzsa inequality
-/

namespace finset
variables {ι α β γ : Type*}

section
variables [preorder α] {s : finset ι}

lemma exists_minimal_image (hs : s.nonempty) (f : ι → α) : ∃ i ∈ s, ∀ ⦃j⦄, j ∈ s → ¬ f j < f i :=
by { classical, simpa using exists_minimal _ (hs.image f) }

lemma exists_maximal_image (hs : s.nonempty) (f : ι → α) : ∃ i ∈ s, ∀ ⦃j⦄, j ∈ s → ¬ f i < f j :=
by { classical, simpa using exists_maximal _ (hs.image f) }

end

lemma powerset_nonempty (s : finset α) : s.powerset.nonempty := ⟨∅, empty_mem_powerset _⟩

open function
open_locale pointwise

section
variables [decidable_eq γ] {f : α → β → γ} (s s₁ s₂ : finset α) (t t₁ t₂ : finset β) (a : α) (b : β)

lemma card_image₂_singleton_left (hf : injective (f a)) : (image₂ f {a} t).card = t.card :=
by rw [image₂_singleton_left, card_image_of_injective _ hf]

lemma card_image₂_singleton_right (hf : injective (λ a, f a b)) : (image₂ f s {b}).card = s.card :=
by rw [image₂_singleton_right, card_image_of_injective _ hf]

lemma image₂_singleton_inter [decidable_eq β] (hf : injective (f a)) :
  image₂ f {a} (t₁ ∩ t₂) = image₂ f {a} t₁ ∩ image₂ f {a} t₂ :=
by simp_rw [image₂_singleton_left, image_inter _ _ hf]

lemma image₂_inter_singleton [decidable_eq α] (hf : injective (λ a, f a b)) :
  image₂ f (s₁ ∩ s₂) {b} = image₂ f s₁ {b} ∩ image₂ f s₂ {b} :=
by simp_rw [image₂_singleton_right, image_inter _ _ hf]

lemma card_le_card_image₂_left {s : finset α} (hs : s.nonempty) (hf : ∀ a, injective (f a)) :
  t.card ≤ (image₂ f s t).card :=
begin
  obtain ⟨a, ha⟩ := hs,
  rw ←card_image₂_singleton_left _ _ (hf a),
  exact card_le_of_subset (image₂_subset_right $ singleton_subset_iff.2 ha),
end

lemma card_le_card_image₂_right {t : finset β} (ht : t.nonempty)
  (hf : ∀ b, injective (λ a, f a b)) :
  s.card ≤ (image₂ f s t).card :=
begin
  obtain ⟨b, hb⟩ := ht,
  rw ←card_image₂_singleton_right _ _ (hf b),
  exact card_le_of_subset (image₂_subset_left $ singleton_subset_iff.2 hb),
end

end

section
variables [left_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[to_additive] lemma card_singleton_mul : ({a} * t).card = t.card :=
card_image₂_singleton_left _ _ $ mul_right_injective _

@[to_additive] lemma singleton_mul_inter : {a} * (s ∩ t) = ({a} * s) ∩ ({a} * t) :=
image₂_singleton_inter _ _ _ $ mul_right_injective _

@[to_additive] lemma card_le_card_mul_left {s : finset α} (hs : s.nonempty) :
  t.card ≤ (s * t).card :=
card_le_card_image₂_left _ hs mul_right_injective

end

section
variables [right_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[to_additive] lemma card_mul_singleton : (s * {a}).card = s.card :=
card_image₂_singleton_right _ _ $ mul_left_injective _

@[to_additive] lemma inter_mul_singleton : (s ∩ t) * {a} = (s * {a}) ∩ (t * {a}) :=
image₂_inter_singleton _ _ _ $ mul_left_injective _

@[to_additive] lemma card_le_card_mul_right {t : finset α} (ht : t.nonempty) :
  s.card ≤ (s * t).card :=
card_le_card_image₂_right _ ht mul_left_injective

end
end finset

section
variables {α : Type*} [semilattice_sup α] {a b c : α}

lemma sup_congr_left (hb : b ≤ a ⊔ c) (hc : c ≤ a ⊔ b) : a ⊔ b = a ⊔ c :=
(sup_le le_sup_left hb).antisymm $ sup_le le_sup_left hc

end

section
variables {α : Type*} [generalized_boolean_algebra α] {x y z : α}

lemma sup_sdiff_eq_sup (h : z ≤ x) : x ⊔ y \ z = x ⊔ y :=
sup_congr_left (sdiff_le.trans le_sup_right) $ le_sup_sdiff.trans $ sup_le_sup_right h _

end

open finset nat
open_locale pointwise

variables {α : Type*} [add_comm_group α] [decidable_eq α] {A B C X : finset α}

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_sub_mul_card_sub (A B C : finset α) :
  (A - C).card * B.card ≤ (A - B).card * (B - C).card :=
begin
  rw [←card_product (A - B), ←mul_one ((finset.product _ _).card)],
  refine card_mul_le_card_mul (λ b ac, ac.1 + ac.2 = b) (λ x hx, _)
    (λ x hx, card_le_one_iff.2 $ λ u v hu hv,
      ((mem_bipartite_below _).1 hu).2.symm.trans ((mem_bipartite_below _).1 hv).2),
  obtain ⟨a, c, ha, hc, rfl⟩ := mem_sub.1 hx,
  refine card_le_card_of_inj_on (λ b, (a - b, b - c)) (λ b hb, _) (λ b₁ _ b₂ _ h, _),
  { rw mem_bipartite_above,
    exact ⟨mk_mem_product (sub_mem_sub ha hb) (sub_mem_sub hb hc), sub_add_sub_cancel _ _ _⟩ },
  { have := congr_arg prod.fst h,
    exact sub_right_injective this }
end

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_add_mul_card_add (A B C : finset α) :
  (A - C).card * B.card ≤ (A + B).card * (B + C).card :=
begin
  rw [←sub_neg_eq_add, ←card_neg B, ←card_neg (B + C), neg_add, ←sub_eq_add_neg],
  exact card_sub_mul_le_card_sub_mul_card_sub _ _ _,
end

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_sub_mul_card_add (A B C : finset α) :
  (A + C).card * B.card ≤ (A - B).card * (B + C).card :=
by { rw [←sub_neg_eq_add, ←sub_neg_eq_add B], exact card_sub_mul_le_card_sub_mul_card_sub _ _ _ }

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_add_mul_card_sub (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B - C).card :=
by { rw [←sub_neg_eq_add, sub_eq_add_neg B], exact card_sub_mul_le_card_add_mul_card_add _ _ _ }

lemma pluennecke_petridis (C : finset α)
  (hA : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card) :
  (A + B + C).card * A.card ≤ (A + B).card * (A + C).card :=
begin
  induction C using finset.induction_on with x C hc ih,
  { simp },
  set A' := A ∩ (A + C - {x}) with hA',
  set C' := insert x C with hC',
  have h₀ : A' + {x} = (A + {x}) ∩ (A + C),
  { rw [hA', inter_add_singleton, (is_add_unit_singleton x).sub_add_cancel] },
  have h₁ : A + B + C' = (A + B + C) ∪ (A + B + {x}) \ (A' + B + {x}),
  { rw [hC', insert_eq, union_comm, add_union],
    refine (sup_sdiff_eq_sup _).symm,
    rw [add_right_comm, add_right_comm A, h₀],
    exact add_subset_add_right (inter_subset_right _ _) },
  have h₂ : A' + B + {x} ⊆ A + B + {x} :=
    add_subset_add_right (add_subset_add_right $ inter_subset_left _ _),
  have h₃ : (A + B + C').card ≤ (A + B + C).card + (A + B).card - (A' + B).card,
  { rw h₁,
    refine (card_union_le _ _).trans_eq _,
    rw [card_sdiff h₂, ←add_tsub_assoc_of_le (card_le_of_subset h₂), card_add_singleton,
      card_add_singleton] },
  refine (mul_le_mul_right' h₃ _).trans _,
  rw [tsub_mul, add_mul],
  refine (tsub_le_tsub (add_le_add_right ih _) $ hA _ $ inter_subset_left _ _).trans_eq _,
  rw [←mul_add, ←mul_tsub, ←hA', insert_eq, add_union, ←card_add_singleton A x,
    ←card_add_singleton A' x, add_comm (card _), h₀,
    eq_tsub_of_add_eq (card_union_add_card_inter _ _)],
end

/-! ### Sum triangle inequality -/

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_add_mul_card_add (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B + C).card :=
begin
  obtain rfl | hB := B.eq_empty_or_nonempty,
  { simp },
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _),
  obtain ⟨U, hU, hUA⟩ := exists_min_image (B.powerset.erase ∅) (λ U, (U + A).card/U.card : _ → ℚ)
    ⟨B, hB'⟩,
  rw [mem_erase, mem_powerset, ←nonempty_iff_ne_empty] at hU,
  refine cast_le.1 (_ : (_ : ℚ) ≤ _),
  push_cast,
  refine (le_div_iff $ by exact cast_pos.2 hB.card_pos).1 _,
  rw [mul_div_right_comm, add_comm _ B],
  refine (cast_le.2 $ card_le_card_add_left _ hU.1).trans _,
  refine le_trans _ (mul_le_mul (hUA _ hB') (cast_le.2 $ card_le_of_subset $
    add_subset_add_right hU.2) (cast_nonneg _) $ div_nonneg (cast_nonneg _) $
    cast_nonneg _),
  dsimp,
  rw [←mul_div_right_comm, ←add_assoc],
  refine (le_div_iff $ by exact cast_pos.2 hU.1.card_pos).2 _,
  norm_cast,
  refine pluennecke_petridis C (λ U' hUU', _),
  obtain rfl | hU' := U'.eq_empty_or_nonempty,
  { simp },
  have hU₀ : (0 : ℚ) < U.card := cast_pos.2 hU.1.card_pos,
  have hU₀' : (0 : ℚ) < U'.card := cast_pos.2 hU'.card_pos,
  exact_mod_cast (div_le_div_iff hU₀ hU₀').1
    (hUA _ $ mem_erase_of_ne_of_mem hU'.ne_empty $ mem_powerset.2 $ hUU'.trans hU.2),
end

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_sub_mul_card_sub (A B C : finset α) :
  (A + C).card * B.card ≤ (A - B).card * (B - C).card :=
begin
  rw [sub_eq_add_neg, ←card_neg B, ←card_neg (B - C), neg_sub', sub_neg_eq_add],
  exact card_add_mul_le_card_add_mul_card_add _ _ _,
end

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_add_mul_card_sub (A B C : finset α) :
  (A - C).card * B.card ≤ (A + B).card * (B - C).card :=
by { rw [sub_eq_add_neg, sub_eq_add_neg], exact card_add_mul_le_card_add_mul_card_add _ _ _ }

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_sub_mul_card_add (A B C : finset α) :
  (A - C).card * B.card ≤ (A - B).card * (B + C).card :=
by { rw [←sub_neg_eq_add, sub_eq_add_neg], exact card_add_mul_le_card_sub_mul_card_sub _ _ _ }
