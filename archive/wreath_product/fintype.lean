import .defs

import data.fintype.basic
import data.fintype.big_operators
import data.fintype.prod
import data.fintype.pi


section fintype
variables (A B L : Type*) [group A] [group B] [mul_action A L] [fintype A] [fintype B] [fintype L] [decidable_eq L]

protected def bij : (L → B) × A ≃ B ≀[L] A  :=
{
  to_fun := λ x, ⟨x.1, x.2⟩,
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := begin
    unfold function.left_inverse,
    simp,
  end,
  right_inv := begin
    unfold function.right_inverse,
    unfold function.left_inverse,
    simp,
    intro,
    ext, simp,
  end,
}

instance : fintype (B ≀[L] A) := fintype.of_equiv ((L → B) × A) (bij A B L)

lemma wreath_product_card : fintype.card (B ≀[L] A) = (fintype.card B) ^ (fintype.card L) * (fintype.card A) :=
begin
  rw fintype.of_equiv_card (bij A B L),
  simp,
end

end fintype
