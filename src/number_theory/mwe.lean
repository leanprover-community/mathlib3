import data.fintype.basic
import group_theory.order_of_element
import tactic.zify
import data.nat.totient
import data.zmod.basic
import number_theory.padics.padic_norm
import field_theory.finite.basic
import data.fintype.basic

example (a b c x y : ℕ) (a_le_x : a ≤ x) (x_le_b : x ≤ b) (b_le_y : b ≤ y) (y_le_c : y ≤ c) : (c - a) = (c - b) + (b - a) :=
begin
  zify,
  rw int.coe_nat_sub (le_trans a_le_x x_le_b),
  rw int.coe_nat_sub (le_trans b_le_y y_le_c),
  rw int.coe_nat_sub (le_trans (le_trans a_le_x x_le_b) (le_trans b_le_y y_le_c)),
  abel,
end

lemma sub_one_dvd_pow_sub_one (p α : ℕ) (one_le_p : 1 ≤ p) : (p - 1) ∣ (p^α - 1) :=
begin
  induction α with a ih,
  { simp, },
  { rw dvd_iff_exists_eq_mul_left at *,
    rcases ih with ⟨c, hc⟩,
    use p^a + c,
    rw add_mul,
    rw ← hc,
    rw mul_tsub,
    rw mul_one,
    zify,
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p a),
    rw int.coe_nat_sub (le_mul_of_one_le_right' one_le_p),
    rw int.coe_nat_sub (one_le_pow_of_one_le one_le_p (nat.succ a)),
    rw pow_succ',
    abel,
    exact one_le_pow_of_one_le one_le_p a,
    exact le_mul_of_one_le_right' one_le_p,
    exact one_le_pow_of_one_le one_le_p (nat.succ α),
    },
end
