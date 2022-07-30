/-
Copyright (c) 2022 Yaël Dillies, George Shakan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, George Shakan
-/
import combinatorics.double_counting
import data.finset.pointwise

/-!
# The Plünnecke-Ruzsa inequality

This file proves Ruzsa's triangle inequality, the Plünnecke-Petridis lemma, and the Plünnecke-Ruzsa
inequality.

## Main declarations

* `finset.card_sub_mul_le_card_sub_mul_card_sub`: Ruzsa's triangle inequality, difference version.
* `finset.card_add_mul_le_card_add_mul_card_add`: Ruzsa's triangle inequality, sum version.
* `finset.pluennecke_petridis`: The Plünnecke-Petridis lemma.
* `finset.card_smul_sub_smul_le`: The Plünnecke-Ruzsa inequality.
-/

open nat
open_locale pointwise

namespace finset
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

private lemma aux (hA : A.nonempty) (hAB : A ⊆ B)
  (h : ∀ A' ∈ B.powerset.erase ∅, ((A + C).card : ℚ) / ↑(A.card) ≤ ((A' + C).card) / ↑(A'.card)) :
  ∀ A' ⊆ A, (A + C).card * A'.card ≤ (A' + C).card * A.card :=
begin
  rintro A' hAA',
  obtain rfl | hA' := A'.eq_empty_or_nonempty,
  { simp },
  have hA₀ : (0 : ℚ) < A.card := cast_pos.2 hA.card_pos,
  have hA₀' : (0 : ℚ) < A'.card := cast_pos.2 hA'.card_pos,
  exact_mod_cast (div_le_div_iff (hA₀) hA₀').1 (h _ $ mem_erase_of_ne_of_mem hA'.ne_empty $
    mem_powerset.2 $ hAA'.trans hAB),
end

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
  rw [←mul_div_right_comm, ←add_assoc],
  refine (le_div_iff $ by exact cast_pos.2 hU.1.card_pos).2 _,
  exact_mod_cast pluennecke_petridis C (aux hU.1 hU.2 hUA),
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

lemma card_add_nsmul_le (hAB : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card) (n : ℕ) :
  ((A + n • B).card : ℚ) ≤ ((A + B).card / A.card) ^ n * A.card :=
begin
  obtain rfl | hA := A.eq_empty_or_nonempty,
  { simp },
  induction n with n ih,
  { simp },
  rw [succ_nsmul, ←add_assoc, pow_succ, mul_assoc, ←mul_div_right_comm, le_div_iff, ←cast_mul],
  swap, exact (cast_pos.2 hA.card_pos),
  refine (cast_le.2 $ pluennecke_petridis _ hAB).trans _,
  rw cast_mul,
  exact mul_le_mul_of_nonneg_left ih (cast_nonneg _),
end

/-- The **Plünnecke-Ruzsa inequality**. -/
lemma card_smul_sub_smul_le (hB : B.nonempty) (m n : ℕ) :
  ((m • B - n • B).card : ℚ) ≤ ((B + B).card / B.card) ^ (m + n) * B.card :=
begin
  have hB' : B ∈ B.powerset.erase ∅ := mem_erase_of_ne_of_mem hB.ne_empty (mem_powerset_self _),
  obtain ⟨A, hA, hAB⟩ := exists_min_image (B.powerset.erase ∅) (λ A, (A + B).card/A.card : _ → ℚ)
    ⟨B, hB'⟩,
  rw [mem_erase, mem_powerset, ←nonempty_iff_ne_empty] at hA,
  refine (mul_le_mul_right $ cast_pos.2 hA.1.card_pos).1 _,
  norm_cast,
  refine (cast_le.2 $ card_sub_mul_le_card_add_mul_card_add _ _ _).trans _,
  push_cast,
  rw [add_comm],
  refine (mul_le_mul (card_add_nsmul_le (aux hA.1 hA.2 hAB) _)
    (card_add_nsmul_le (aux hA.1 hA.2 hAB) _) (cast_nonneg _) $
    mul_nonneg (pow_nonneg (div_nonneg (cast_nonneg _) $ cast_nonneg _) _) $ cast_nonneg _).trans _,
  rw [mul_mul_mul_comm, ←pow_add, ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (cast_nonneg _),
  refine mul_le_mul _ _ _ _,
  refine pow_le_pow_of_le_left (div_nonneg (cast_nonneg _) $ cast_nonneg _) _ _,
  refine hAB _ hB',
  refine cast_le.2 (card_le_of_subset hA.2),
  refine cast_nonneg _,
  refine pow_nonneg _ _,
  refine div_nonneg (cast_nonneg _) (cast_nonneg _),
end

end finset
