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
variables {α : Type*}
open_locale pointwise

section
variables [add_left_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[simp] lemma card_singleton_add : ({a} + s).card = s.card :=
by { simp_rw singleton_add, exact card_image_of_injective _ (add_right_injective _) }

lemma singleton_add_inter : {a} + (s ∩ t) = ({a} + s) ∩ ({a} + t) :=
by { simp_rw singleton_add, exact image_inter _ _ (add_right_injective _) }

end

section
variables [add_right_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

lemma inter_add_singleton : (s ∩ t) + {a} = (s + {a}) ∩ (t + {a}) :=
by { simp_rw add_singleton, exact image_inter _ _ (add_left_injective a) }

@[simp] lemma card_add_singleton : (s + {a}).card = s.card :=
by { simp_rw add_singleton, exact card_image_of_injective _ (add_left_injective _) }

end
end finset

open finset
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

lemma pluennecke_petridis (hXA : ∀ A' ⊆ A, (A + B).card * A'.card ≤ (A' + B).card * A.card)
  (C : finset α) :
  (A + B + C).card * A.card ≤ (A + B).card * (B + C).card :=
begin
  induction C using finset.induction_on with x C hc ih,
  { simp },
  set A' := A ∩ (A + C - {x}) with hA',
  set C' := insert x C with hC',
  rw [insert_eq, add_union],
  have : A' + {x} = (A + {x}) ∩ (A + C),
  { rw [hA', inter_add_singleton, (is_add_unit_singleton x).sub_add_cancel] },
  have : (A + C').card = (A + C).card + A.card - A'.card,
  { rw [hC', insert_eq, add_union, ←card_add_singleton A x, ←card_add_singleton A' x,
      add_comm (card _), this],
    exact eq_tsub_of_add_eq (card_union_add_card_inter _ _) },
  sorry
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

/-! ### Sum triangle inequality -/

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_add_mul_card_add (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B + C).card :=
sorry

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
