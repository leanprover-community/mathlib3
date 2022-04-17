import combinatorics.double_counting
import data.finset.pointwise

/-!
# The Plünnecke-Ruzsa inequality-/

open finset
open_locale pointwise

variables {α : Type*} [add_group α] [decidable_eq α]

lemma ruzsa_triangle_inequality (A B C : finset α) :
  (A - C).card * B.card ≤ (A - B).card * (B - C).card :=
begin
  rw [←card_product (A - B), ←mul_one ((finset.product _ _).card)],
  refine card_mul_le_card_mul (λ b ac, ac.1 + ac.2 = b) (λ x hx, _) _,
  { obtain ⟨a, c, ha, hc, rfl⟩ := mem_sub.1 hx,
    refine card_le_card_of_inj_on (λ b, (a - b, b - c)) (λ b hb, _) (λ b₁ _ b₂ _ h, _),
    { rw mem_bipartite_above,
      exact ⟨mk_mem_product (sub_mem_sub ha hb) (sub_mem_sub hb hc), sub_add_sub_cancel _ _ _⟩ },
    { have := congr_arg prod.fst h,
      exact sub_right_injective this } },
  {
    sorry
  }
end

lemma ruzsa_sum_triangle_inequality (A B C : finset α) :
  (A + C).card * B.card ≤ (A + B).card * (B + C).card :=
sorry
