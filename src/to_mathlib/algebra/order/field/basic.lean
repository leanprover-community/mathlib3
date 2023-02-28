import algebra.order.field.basic
import tactic.ring

lemma one_add_le_inv_one_sub_of_lt_one {K : Type*} [linear_ordered_field K] {x : K} (hx : x < 1) :
  1 + x ≤ (1 - x)⁻¹ :=
begin
  have : 0 < 1 - x,
  { rwa [lt_sub_iff_add_lt, zero_add] },
  refine le_of_mul_le_mul_left _ this,
  rw mul_inv_cancel this.ne',
  simp [sub_mul, mul_add, ←pow_two, sq_nonneg]
end

lemma inv_one_add_two_mul_le_one_sub_of_nonneg_of_le_half {K : Type*} [linear_ordered_field K]
  {x : K} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : (1 + 2 * x)⁻¹ ≤ 1 - x :=
begin
  have : 0 < 1 + 2 * x,
  { refine add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg two_pos.le hx) },
  refine le_of_mul_le_mul_left _ this,
  rw mul_inv_cancel this.ne',
  ring_nf,
  simp only [add_mul, neg_mul, one_mul, le_add_iff_nonneg_left, le_neg_add_iff_add_le, add_zero],
  refine mul_le_of_le_one_left hx _,
  refine (mul_le_mul_of_nonneg_left hx' zero_le_two).trans _,
  rw [one_div, mul_inv_cancel],
  exact zero_lt_two.ne'
end
