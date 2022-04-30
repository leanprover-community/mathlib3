import combinatorics.additive.mathlib
import combinatorics.double_counting
import data.finset.pointwise

/-!
# The Plünnecke-Ruzsa inequality
-/

open finset
open_locale pointwise

variables {α : Type*} [add_group α] [decidable_eq α] {A B C X : finset α}

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
  {
    rw [hA'],
  },
  have : (A + C').card = (A + C).card + A.card - A'.card,
  {
    rw [hC', insert_eq, add_union, hA'],
  }
end

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_add_mul_card_add (A B C : finset α) :
  (A - C).card * B.card ≤ (A + B).card * (B + C).card :=
begin
  -- rw [←sub_neg_eq_add A, ←card_neg B, ←card_neg (B + C)],
  sorry
end

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_sub_mul_card_add (A B C : finset α) :
  (A + C).card * B.card ≤ (A - B).card * (B + C).card :=
begin
  sorry
end

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_add_mul_card_sub (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B - C).card :=
begin
  sorry
end

/-! ### Sum triangle inequality -/

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_add_mul_card_add (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B + C).card :=
sorry

/-- **Ruzsa's triangle inequality** -/
lemma card_add_mul_le_card_sub_mul_card_sub (A B C : finset α) :
  (A + C).card * B.card ≤ (A - B).card * (B - C).card :=
sorry

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_add_mul_card_sub (A B C : finset α) :
  (A - C).card * B.card ≤ (A + B).card * (B - C).card :=
sorry

/-- **Ruzsa's triangle inequality** -/
lemma card_sub_mul_le_card_sub_mul_card_add (A B C : finset α) :
  (A - C).card * B.card ≤ (A - B).card * (B + C).card :=
sorry
